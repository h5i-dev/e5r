//! Jump table recovery.
//!
//! A `switch` compiles to an indirect branch through a table, and a
//! disassembler that cannot read the table stops at the branch. That is most of
//! the difference between a function that analyzes completely and one that does
//! not.
//!
//! Recovery simulates the instructions leading to the branch with a small value
//! model, then reads the table. The hard part is knowing where the table ends.
//! Compilers emit compact tables of byte or halfword offsets scaled by the
//! instruction size, and *every* byte value in such a table yields a plausible
//! target, so scanning until an entry looks wrong never stops. The bound has to
//! come from the compare that guards the switch, and the compare has to be
//! matched to the register the table is indexed by. Without that match a stray
//! comparison elsewhere in the function would size the table.

use std::collections::BTreeMap;

use r12e_arch::{Flow, Insn, Operand, Reg, RegClass, Mem};
use r12e_core::{Addr, AddrRange, Caps, MemoryMap};
use serde::Serialize;

/// How a table entry becomes a target address.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TableKind {
    /// The entry is the target.
    Absolute,
    /// The entry is an offset from a single fixed address.
    RelativeToBase,
    /// The entry is an offset from its own address in the table, which is what
    /// a compiler emits when it folds the index into the pointer first.
    RelativeToEntry,
}

/// A recovered table.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct JumpTable {
    /// The indirect branch it resolves.
    pub at: Addr,
    /// Where the entries live.
    pub table: Addr,
    /// Bytes per entry.
    pub entry_size: u64,
    /// What the entries mean.
    pub kind: TableKind,
    /// Where offsets are measured from, for [`TableKind::RelativeToBase`].
    pub base: Addr,
    /// How far each entry is shifted before it is added.
    pub shift: u8,
    /// The targets, in table order.
    pub targets: Vec<Addr>,
    /// True when the size came from scanning rather than from a compare.
    pub bounded_by_scan: bool,
}

/// A register, identified across the simulation.
type RegKey = (u8, u8);

fn key(r: Reg) -> Option<RegKey> {
    match r.class {
        RegClass::Gpr => Some((0, r.num)),
        RegClass::Sp => Some((1, 31)),
        _ => None,
    }
}

/// What a register holds, as far as recovery needs to know.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Val {
    /// Anything.
    Unknown,
    /// A known address the code formed.
    Const(u64),
    /// `base + index * scale`: a pointer to one element of a table.
    Elem {
        table: u64,
        scale: u64,
        index: RegKey,
    },
    /// A value loaded from a table.
    Entry {
        table: u64,
        size: u64,
        signed: bool,
        /// The register the table was indexed by, which is what the guarding
        /// compare has to name for its bound to apply.
        index: Option<RegKey>,
        /// Stride between entries.
        scale: u64,
        /// True when the load went through an element pointer, so each entry's
        /// offset is measured from its own address rather than from one base.
        from_elem: bool,
    },
    /// An entry added to a base, which is the branch target.
    Target {
        table: u64,
        size: u64,
        signed: bool,
        index: Option<RegKey>,
        scale: u64,
        from_elem: bool,
        base: u64,
        shift: u8,
    },
}

#[derive(Default)]
struct Regs {
    registers: BTreeMap<RegKey, Val>,
    /// Stack slots, keyed by the register the address was formed from and the
    /// displacement. An unoptimized compiler spills the switch index and
    /// reloads it, so without this the index is unknown by the time the branch
    /// reads it and the table cannot be bounded.
    slots: BTreeMap<(RegKey, i64), Val>,
}

impl Regs {
    fn get(&self, r: Reg) -> Val {
        key(r)
            .and_then(|k| self.registers.get(&k).copied())
            .unwrap_or(Val::Unknown)
    }

    fn set(&mut self, r: Reg, v: Val) {
        if let Some(k) = key(r) {
            self.registers.insert(k, v);
            // Anything spilled from this register is now stale: the slot holds
            // what was written, not what the register holds next.
            self.slots.retain(|(base, _), _| *base != k);
        }
    }

    /// The slot a memory operand names, when it is a simple base and
    /// displacement.
    fn slot(&self, m: &Mem) -> Option<(RegKey, i64)> {
        if m.index.is_some() || m.mode != r12e_arch::AddrMode::Offset {
            return None;
        }
        Some((key(m.base?)?, m.disp))
    }

    fn load_slot(&self, m: &Mem) -> Option<Val> {
        self.slots.get(&self.slot(m)?).copied()
    }

    fn store_slot(&mut self, m: &Mem, v: Val) {
        if let Some(k) = self.slot(m) {
            self.slots.insert(k, v);
        }
    }
}

/// The largest table believed without a bound from a compare.
///
/// Low on purpose. An unbounded compact table always looks valid, so a large
/// unbounded result is a sign the recovery is wrong rather than that the switch
/// is big.
const SCAN_CAP: u64 = 256;

/// Try to resolve the indirect branch that ends `insns`.
///
/// `insns` is the instruction context in address order, ending with the branch;
/// giving it the predecessor blocks as well as the branch's own block is what
/// lets the guarding compare be found. `section` bounds every target and
/// `alignment` is the architecture's instruction alignment.
pub fn recover(
    insns: &[Insn],
    mem: &MemoryMap,
    section: AddrRange,
    caps: &Caps,
    alignment: u64,
) -> Option<JumpTable> {
    let alignment = alignment.max(1);
    let last = insns.last()?;
    if !matches!(last.flow, Flow::IndirectBranch) {
        return None;
    }

    // Everything before the branch: its operand is a read, and running it
    // through the model would clobber the register the table was built in.
    let mut regs = Regs::default();
    for i in &insns[..insns.len() - 1] {
        step(i, &mut regs);
    }

    let shape = match last.operands().first()? {
        Operand::Reg(r) => regs.get(*r),
        // `jmp qword ptr [rip + table + rax*8]`: the table is the operand.
        Operand::Mem(m) => {
            let table = if m.is_pc_relative() {
                m.pc_target(last.end())?.get()
            } else {
                match m.base.map(|b| regs.get(b)) {
                    Some(Val::Const(c)) => c.wrapping_add(m.disp as u64),
                    _ => return None,
                }
            };
            let (ix, _, scale) = m.index?;
            Val::Entry {
                table,
                size: 1u64 << scale,
                signed: false,
                index: key(ix),
                scale: 1u64 << scale,
                from_elem: false,
            }
        }
        _ => return None,
    };

    let (table, size, signed, index, scale, from_elem, kind, base, shift) = match shape {
        Val::Target {
            table,
            size,
            signed,
            index,
            scale,
            from_elem,
            base,
            shift,
        } => {
            let kind = if from_elem {
                TableKind::RelativeToEntry
            } else {
                TableKind::RelativeToBase
            };
            (
                table, size, signed, index, scale, from_elem, kind, base, shift,
            )
        }
        // A table of whole pointers needs no arithmetic after the load.
        Val::Entry {
            table,
            size,
            signed,
            index,
            scale,
            from_elem,
        } if size == 8 => (
            table,
            size,
            signed,
            index,
            scale,
            from_elem,
            TableKind::Absolute,
            0,
            0,
        ),
        _ => return None,
    };

    if size == 0 || scale == 0 || !mem.is_mapped(Addr(table)) {
        return None;
    }

    // The compare that guards the switch, matched to the index register.
    let bound = index.and_then(|ix| bound_for(ix, &insns[..insns.len() - 1]));
    // A compact table of byte or halfword offsets cannot be bounded by
    // scanning: every value in range yields a plausible target, so the scan
    // would stop wherever the following bytes happened to look wrong. Without
    // the guard there is no honest answer, so there is no answer.
    if bound.is_none() && size <= 2 && kind != TableKind::Absolute {
        return None;
    }
    let limit = match bound {
        Some(n) => n.min(caps.jump_table_entries),
        None => SCAN_CAP.min(caps.jump_table_entries),
    };

    let mut targets = Vec::new();
    for n in 0..limit {
        let at = match table.checked_add(n * scale) {
            Some(a) => Addr(a),
            None => break,
        };
        let Ok(raw) = mem.read_ptr(at, size, true) else {
            break;
        };
        let value = if signed {
            sign_extend(raw, size)
        } else {
            raw as i64
        };
        let from = if from_elem { at.get() } else { base };
        let target = match kind {
            TableKind::Absolute => Addr(raw),
            _ => Addr(from.wrapping_add((value << shift) as u64)),
        };
        if !section.contains(target) || !mem.is_executable(target) || target.get() % alignment != 0
        {
            break;
        }
        targets.push(target);
    }

    // Two entries is the smallest thing worth calling a switch, and an
    // unbounded result that ran to the cap is a recovery that went wrong.
    if targets.len() < 2 || (bound.is_none() && targets.len() as u64 >= limit) {
        return None;
    }

    Some(JumpTable {
        at: last.addr,
        table: Addr(table),
        entry_size: size,
        kind,
        base: Addr(base),
        shift,
        targets,
        bounded_by_scan: bound.is_none(),
    })
}

/// The switch bound from the compare that guards it.
///
/// `cmp <index>, #n` means at most `n + 1` entries. The register has to match,
/// or an unrelated comparison would size the table.
fn bound_for(index: RegKey, body: &[Insn]) -> Option<u64> {
    (0..body.len()).rev().find_map(|n| {
        let i = &body[n];
        // A subtraction whose only purpose is the flags it sets: an
        // unoptimized compiler writes `sub rax, 11` and branches on it rather
        // than comparing, and the difference itself is thrown away. The
        // branch immediately after is what says so.
        let comparison = match i.mnemonic {
            "cmp" | "subs" => true,
            "sub" => body
                .get(n + 1)
                .is_some_and(|next| matches!(next.flow, Flow::CondBranch(_))),
            _ => false,
        };
        if !comparison {
            return None;
        }
        let Some(Operand::Reg(r)) = i.operands().first() else {
            return None;
        };
        if key(*r) != Some(index) {
            return None;
        }
        match i.operands().get(1) {
            Some(Operand::Imm(v)) if *v >= 0 && *v < 1 << 20 => Some(*v as u64 + 1),
            Some(Operand::UImm(v)) if *v < 1 << 20 => Some(*v + 1),
            _ => None,
        }
    })
}

fn sign_extend(v: u64, bytes: u64) -> i64 {
    match bytes {
        1 => v as u8 as i8 as i64,
        2 => v as u16 as i16 as i64,
        4 => v as u32 as i32 as i64,
        _ => v as i64,
    }
}

/// Advance the value model by one instruction.
fn step(i: &Insn, regs: &mut Regs) {
    let ops = i.operands();
    let dest = match ops.first() {
        Some(Operand::Reg(r)) => Some(*r),
        _ => None,
    };

    let value = match i.mnemonic {
        // Address formation: AArch64 in two steps, x86 in one lea.
        "adrp" | "adr" => match ops.get(1) {
            Some(Operand::Addr(a)) => Some(Val::Const(a.get())),
            _ => None,
        },
        "lea" => match ops.get(1) {
            Some(Operand::Mem(m)) => {
                m.pc_target(i.end())
                    .map(|t| Val::Const(t.get()))
                    .or_else(|| match m.base.map(|b| regs.get(b)) {
                        Some(Val::Const(c)) => Some(Val::Const(c.wrapping_add(m.disp as u64))),
                        _ => None,
                    })
            }
            _ => None,
        },
        "add" => Some(add_value(ops, regs)),
        "ldr" | "ldrb" | "ldrh" | "ldrsw" | "ldrsb" | "ldrsh" | "mov" | "movsxd" | "movzx"
        | "movsx" => Some(load_value(i, ops, regs)),
        _ => None,
    };

    if let Some(d) = dest {
        regs.set(d, value.unwrap_or(Val::Unknown));
        return;
    }
    // A spill: the destination is memory and the source a register whose value
    // the model knows.
    if let (Some(Operand::Mem(m)), Some(Operand::Reg(source))) = (ops.first(), ops.get(1)) {
        if matches!(i.mnemonic, "mov" | "str" | "stur") {
            let v = regs.get(*source);
            regs.store_slot(m, v);
        }
    }
}

/// The value of an `add` whose parts the model knows.
fn add_value(ops: &[Operand], regs: &Regs) -> Val {
    // Three operands on AArch64, two on x86 where the destination is also the
    // first source. Reading the two-operand form as if it had three loses the
    // value entirely, which is how a switch stays unresolved.
    let (a, b) = if ops.len() >= 3 {
        (
            operand_value(ops.get(1), regs),
            operand_value(ops.get(2), regs),
        )
    } else {
        (
            operand_value(ops.first(), regs),
            operand_value(ops.get(1), regs),
        )
    };
    let shift = shift_of(ops);

    match (a, b) {
        (Val::Const(x), Val::Const(y)) => Val::Const(x.wrapping_add(y)),

        // A known address plus an unknown scaled register: a pointer to one
        // element of a table.
        (Val::Const(table), Val::Unknown) | (Val::Unknown, Val::Const(table)) => {
            match scaled_index(ops, regs) {
                Some(index) if shift > 0 => Val::Elem {
                    table,
                    scale: 1u64 << shift,
                    index,
                },
                _ => Val::Unknown,
            }
        }

        // An entry added to a base: the branch target.
        (
            Val::Entry {
                table,
                size,
                signed,
                index,
                scale,
                from_elem,
            },
            Val::Const(base),
        )
        | (
            Val::Const(base),
            Val::Entry {
                table,
                size,
                signed,
                index,
                scale,
                from_elem,
            },
        ) => Val::Target {
            table,
            size,
            // The extend on the add decides the sign, not the load: GCC reads
            // a table with `ldrb` and adds it with `sxtb`, so the byte is
            // signed even though the load was not.
            signed: signed_extend(ops).unwrap_or(signed),
            index,
            scale,
            from_elem,
            base,
            shift,
        },

        // An entry added to the element pointer it came from.
        (
            Val::Entry {
                table,
                size,
                signed,
                index,
                scale,
                ..
            },
            Val::Elem { .. },
        )
        | (
            Val::Elem { .. },
            Val::Entry {
                table,
                size,
                signed,
                index,
                scale,
                ..
            },
        ) => Val::Target {
            table,
            size,
            signed,
            index,
            scale,
            from_elem: true,
            base: 0,
            shift,
        },

        _ => Val::Unknown,
    }
}

/// Whether an `add`'s extend sign-extends its operand, when it has one.
fn signed_extend(ops: &[Operand]) -> Option<bool> {
    use r12e_arch::Extend::*;
    ops.iter().find_map(|o| match o {
        Operand::Extended(_, e, _) => Some(matches!(e, Sxtb | Sxth | Sxtw | Sxtx)),
        _ => None,
    })
}

/// The register an `add`'s shifted or extended operand names.
fn scaled_index(ops: &[Operand], _regs: &Regs) -> Option<RegKey> {
    ops.iter().find_map(|o| match o {
        Operand::Shifted(r, _, _) | Operand::Extended(r, _, _) => key(*r),
        _ => None,
    })
}

/// The scaling an `add` applies to its shifted or extended operand.
fn shift_of(ops: &[Operand]) -> u8 {
    ops.iter()
        .find_map(|o| match o {
            Operand::Shifted(_, _, n) | Operand::Extended(_, _, n) => Some(*n),
            _ => None,
        })
        .unwrap_or(0)
}

fn operand_value(op: Option<&Operand>, regs: &Regs) -> Val {
    match op {
        Some(Operand::Reg(r)) => regs.get(*r),
        Some(Operand::Shifted(r, _, _)) | Some(Operand::Extended(r, _, _)) => regs.get(*r),
        Some(Operand::Imm(v)) => Val::Const(*v as u64),
        Some(Operand::UImm(v)) => Val::Const(*v),
        _ => Val::Unknown,
    }
}

/// The value a load produces, when it reads something the model recognizes.
fn load_value(i: &Insn, ops: &[Operand], regs: &Regs) -> Val {
    let Some(Operand::Mem(m)) = ops.get(1) else {
        // A register move carries the value along.
        return match ops.get(1) {
            Some(Operand::Reg(src)) => regs.get(*src),
            _ => Val::Unknown,
        };
    };

    // A reload of something this function spilled: the value is what went in.
    if let Some(v) = regs.load_slot(m) {
        return v;
    }

    let signed = matches!(i.mnemonic, "ldrsw" | "ldrsb" | "ldrsh" | "movsxd" | "movsx");
    let size = if m.size == 0 { 8 } else { m.size };
    let base = m.base.map(|b| regs.get(b));

    match (base, m.index) {
        // An indexed read from a known address: a table read.
        (Some(Val::Const(table)), Some((ix, _, scale))) => Val::Entry {
            table: table.wrapping_add(m.disp as u64),
            size,
            signed,
            index: key(ix),
            scale: if scale == 0 { size } else { 1u64 << scale },
            from_elem: false,
        },
        // A read through an element pointer: the offset is from the element.
        (
            Some(Val::Elem {
                table,
                scale,
                index,
            }),
            None,
        ) => Val::Entry {
            table: table.wrapping_add(m.disp as u64),
            size,
            signed,
            index: Some(index),
            scale,
            from_elem: true,
        },
        _ => Val::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r12e_arch::{AddrMode, Extend, Mem, Width};
    use r12e_core::{Perms, Segment};

    const CODE: Addr = Addr(0x40_0000);
    const CODE_LEN: u64 = 0x1000;
    const TABLE_OFF: u64 = 0x800;

    /// One executable section of `nop`s with a table inside it.
    fn map_with(entries: &[i64], entry_size: usize) -> MemoryMap {
        let mut bytes: Vec<u8> =
            std::iter::repeat_n([0x1f, 0x20, 0x03, 0xd5], (CODE_LEN / 4) as usize)
                .flatten()
                .collect();
        let mut at = TABLE_OFF as usize;
        for e in entries {
            bytes[at..at + entry_size].copy_from_slice(&e.to_le_bytes()[..entry_size]);
            at += entry_size;
        }
        let mut m = MemoryMap::new();
        m.add(
            Segment::new(
                AddrRange::sized(CODE, CODE_LEN).unwrap(),
                Perms::RX,
                ".text",
                0,
                bytes,
            )
            .unwrap(),
        );
        m
    }

    fn table_addr() -> Addr {
        Addr(CODE.get() + TABLE_OFF)
    }

    fn section() -> AddrRange {
        AddrRange::sized(CODE, CODE_LEN).unwrap()
    }

    fn gpr(n: u8) -> Reg {
        Reg::gpr(n, Width::W64)
    }

    fn adrp(at: u64, d: u8, v: u64) -> Insn {
        let mut i = Insn::new(Addr(at), 4, "adrp", Flow::Next);
        i.push(Operand::Reg(gpr(d)));
        i.push(Operand::Addr(Addr(v)));
        i
    }

    fn cmp_imm(at: u64, r: u8, v: i64) -> Insn {
        let mut i = Insn::new(Addr(at), 4, "cmp", Flow::Next);
        i.push(Operand::Reg(gpr(r)));
        i.push(Operand::Imm(v));
        i
    }

    /// `ldrb wd, [xbase, xindex]`, the compact-table read.
    fn ldr_indexed(at: u64, d: u8, base: u8, index: u8, size: u64, signed: bool) -> Insn {
        let name = match (size, signed) {
            (1, false) => "ldrb",
            (2, false) => "ldrh",
            (4, true) => "ldrsw",
            _ => "ldr",
        };
        let mut i = Insn::new(Addr(at), 4, name, Flow::Next);
        i.push(Operand::Reg(gpr(d)));
        i.push(Operand::Mem(Mem {
            seg: None,
            base: Some(gpr(base)),
            index: Some((gpr(index), Extend::Lsl, 0)),
            disp: 0,
            mode: AddrMode::Offset,
            size,
        }));
        i
    }

    /// `add xd, xa, wb, sxtw #shift`.
    fn add_scaled(at: u64, d: u8, a: u8, b: u8, shift: u8) -> Insn {
        let mut i = Insn::new(Addr(at), 4, "add", Flow::Next);
        i.push(Operand::Reg(gpr(d)));
        i.push(Operand::Reg(gpr(a)));
        i.push(Operand::Extended(gpr(b), Extend::Sxtw, shift));
        i
    }

    fn br(at: u64, r: u8) -> Insn {
        let mut i = Insn::new(Addr(at), 4, "br", Flow::IndirectBranch);
        i.push(Operand::Reg(gpr(r)));
        i
    }

    /// The GCC compact form: byte offsets scaled by four from a fixed base.
    fn compact_switch(bound: Option<i64>) -> Vec<Insn> {
        let mut v = Vec::new();
        if let Some(n) = bound {
            v.push(cmp_imm(0x40_0000, 2, n));
        }
        v.push(adrp(0x40_0004, 1, table_addr().get()));
        v.push(ldr_indexed(0x40_0008, 0, 1, 2, 1, false));
        v.push(adrp(0x40_000c, 3, CODE.get()));
        v.push(add_scaled(0x40_0010, 3, 3, 0, 2));
        v.push(br(0x40_0014, 3));
        v
    }

    #[test]
    fn a_compact_table_needs_its_guard_to_be_sized() {
        // Every byte value yields a plausible target, so without the compare
        // there is no honest way to know where the table ends. Recovery must
        // refuse rather than invent 256 successors.
        let mem = map_with(&[1, 2, 3, 4], 1);
        assert!(recover(&compact_switch(None), &mem, section(), &Caps::default(), 4).is_none());

        let t = recover(
            &compact_switch(Some(3)),
            &mem,
            section(),
            &Caps::default(),
            4,
        )
        .expect("guarded table");
        assert_eq!(t.targets.len(), 4);
        assert!(!t.bounded_by_scan);
        assert_eq!(t.kind, TableKind::RelativeToBase);
        assert_eq!(t.shift, 2);
        assert_eq!(t.targets[0], Addr(CODE.get() + 4));
        assert_eq!(t.targets[3], Addr(CODE.get() + 16));
    }

    #[test]
    fn the_guard_has_to_name_the_index_register() {
        // A comparison of some other register must not size the table.
        let mem = map_with(&[1, 2, 3, 4], 1);
        let mut insns = compact_switch(None);
        insns.insert(0, cmp_imm(0x3f_fffc, 9, 3));
        assert!(recover(&insns, &mem, section(), &Caps::default(), 4).is_none());
    }

    #[test]
    fn an_entry_outside_the_section_ends_the_table() {
        // The guard says eight, but the fifth entry points outside the code.
        let mem = map_with(&[1, 2, 3, 4, 0x4000, 0, 0, 0], 2);
        let mut insns = compact_switch(Some(7));
        insns[2] = ldr_indexed(0x40_0008, 0, 1, 2, 2, false);
        let t = recover(&insns, &mem, section(), &Caps::default(), 4).unwrap();
        assert_eq!(t.targets.len(), 4);
    }

    #[test]
    fn misaligned_targets_are_refused() {
        // Offsets that do not land on an instruction boundary are not targets.
        let mem = map_with(&[1, 3, 5, 7], 1);
        let t = recover(
            &compact_switch(Some(3)),
            &mem,
            section(),
            &Caps::default(),
            4,
        );
        // 1 << 2 == 4, aligned; 3 << 2 == 12, aligned. All fine at shift 2.
        assert!(t.is_some());

        let unaligned = map_with(&[1, 2, 3, 4], 1);
        let mut insns = compact_switch(Some(3));
        insns[4] = add_scaled(0x40_0010, 3, 3, 0, 0);
        let t = recover(&insns, &unaligned, section(), &Caps::default(), 4);
        // Offsets 1, 2, 3 unscaled are not multiples of four, so nothing is
        // believed and there is no table.
        assert!(t.is_none());
    }

    #[test]
    fn a_branch_through_an_unknown_register_recovers_nothing() {
        let mem = map_with(&[1, 2], 1);
        assert!(recover(&[br(0x40_0000, 3)], &mem, section(), &Caps::default(), 4).is_none());
    }

    #[test]
    fn one_entry_is_not_a_switch() {
        let mem = map_with(&[1], 1);
        let t = recover(
            &compact_switch(Some(0)),
            &mem,
            section(),
            &Caps::default(),
            4,
        );
        assert!(t.is_none());
    }

    #[test]
    fn an_element_relative_table_is_recognized() {
        // add x6, x6, x14, lsl #2 ; ldr w7, [x6] ; add x6, x6, w7, sxtw ; br x6
        // Offsets are measured from each entry's own address.
        let mem = map_with(&[-0x800, -0x7fc, -0x7f8, -0x7f4], 4);
        let mut add_index = Insn::new(Addr(0x40_0004), 4, "add", Flow::Next);
        add_index.push(Operand::Reg(gpr(6)));
        add_index.push(Operand::Reg(gpr(6)));
        add_index.push(Operand::Shifted(gpr(14), r12e_arch::Shift::Lsl, 2));

        let mut load = Insn::new(Addr(0x40_0008), 4, "ldrsw", Flow::Next);
        load.push(Operand::Reg(gpr(7)));
        load.push(Operand::Mem(Mem {
            seg: None,
            base: Some(gpr(6)),
            index: None,
            disp: 0,
            mode: AddrMode::Offset,
            size: 4,
        }));

        let mut add_entry = Insn::new(Addr(0x40_000c), 4, "add", Flow::Next);
        add_entry.push(Operand::Reg(gpr(6)));
        add_entry.push(Operand::Reg(gpr(6)));
        add_entry.push(Operand::Extended(gpr(7), Extend::Sxtw, 0));

        let insns = vec![
            cmp_imm(0x40_0000, 14, 3),
            adrp(0x40_0000, 6, table_addr().get()),
            add_index,
            load,
            add_entry,
            br(0x40_0010, 6),
        ];
        let t = recover(&insns, &mem, section(), &Caps::default(), 4).expect("element-relative");
        assert_eq!(t.kind, TableKind::RelativeToEntry);
        assert_eq!(t.targets.len(), 4);
        assert_eq!(t.targets[0], Addr(CODE.get()));
    }
}
