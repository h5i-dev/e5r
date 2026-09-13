//! Cross references.
//!
//! Direct branches and calls come free from the decoder. Data references do
//! not: on AArch64 an address is built by an `adrp` that supplies the page and
//! a later `add` or `ldr` that supplies the offset, and the two can be several
//! instructions apart. Resolving that pair is what turns a listing full of
//! bare page numbers into one that names the string being loaded.
//!
//! The tracker is deliberately small: constants per register, forgotten at any
//! instruction that writes a register in a way it does not model, and reset at
//! every block boundary. It never guesses across a join.

use std::collections::BTreeMap;

use r12e_arch::{Flow, Insn, Operand, Reg, RegClass};
use r12e_core::{Addr, MemoryMap};
use serde::Serialize;

/// What kind of reference one address makes to another.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum XrefKind {
    /// A direct call.
    Call,
    /// A direct branch, conditional or not.
    Branch,
    /// An address formed in registers, usually a pointer to data.
    Data,
    /// A load or store through a computed address.
    Read,
    /// A store through a computed address.
    Write,
}

/// One reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct Xref {
    /// The instruction making the reference.
    pub from: Addr,
    /// What it refers to.
    pub to: Addr,
    /// What kind of reference it is.
    pub kind: XrefKind,
}

/// Every reference in a program, searchable in both directions.
#[derive(Debug, Clone, Default)]
pub struct XrefIndex {
    /// Sorted by `(from, to, kind)`.
    by_from: Vec<Xref>,
    /// Sorted by `(to, from, kind)`.
    by_to: Vec<Xref>,
}

impl XrefIndex {
    /// Build from an unsorted list.
    pub fn build(mut refs: Vec<Xref>) -> XrefIndex {
        refs.sort_unstable();
        refs.dedup();
        let mut by_to = refs.clone();
        by_to.sort_unstable_by_key(|x| (x.to, x.from, x.kind));
        XrefIndex {
            by_from: refs,
            by_to,
        }
    }

    /// Every reference.
    pub fn all(&self) -> &[Xref] {
        &self.by_from
    }

    /// How many references there are.
    pub fn len(&self) -> usize {
        self.by_from.len()
    }

    /// True when there are none.
    pub fn is_empty(&self) -> bool {
        self.by_from.is_empty()
    }

    /// References made by the instruction at `from`.
    pub fn from(&self, from: Addr) -> &[Xref] {
        let lo = self.by_from.partition_point(|x| x.from < from);
        let hi = self.by_from.partition_point(|x| x.from <= from);
        &self.by_from[lo..hi]
    }

    /// References pointing at `to`. The question an analyst asks most.
    pub fn to(&self, to: Addr) -> &[Xref] {
        let lo = self.by_to.partition_point(|x| x.to < to);
        let hi = self.by_to.partition_point(|x| x.to <= to);
        &self.by_to[lo..hi]
    }
}

/// Constants known to be in registers at one point in a block.
#[derive(Default)]
struct Regs(BTreeMap<u8, u64>);

impl Regs {
    fn get(&self, r: Reg) -> Option<u64> {
        (r.class == RegClass::Gpr).then(|| self.0.get(&r.num).copied())?
    }

    fn set(&mut self, r: Reg, v: u64) {
        if r.class == RegClass::Gpr {
            self.0.insert(r.num, v);
        }
    }

    fn forget(&mut self, r: Reg) {
        if r.class == RegClass::Gpr {
            self.0.remove(&r.num);
        }
    }
}

/// Collect references from one function's instructions.
///
/// `in_block_order` must be instructions in address order; the tracker resets
/// whenever the previous instruction did not fall through, which is a cheap
/// stand-in for block boundaries and never carries a value across a join.
pub fn collect(insns: &[Insn], mem: &MemoryMap, out: &mut Vec<Xref>) {
    let mut regs = Regs::default();
    let mut fresh = true;

    for (n, i) in insns.iter().enumerate() {
        if !fresh {
            regs = Regs::default();
        }
        // The next instruction continues this run only if this one falls
        // through to exactly it.
        fresh = i.flow == Flow::Next && insns.get(n + 1).map(|nx| nx.addr) == Some(i.next());

        match i.flow {
            Flow::Call(t) => out.push(Xref {
                from: i.addr,
                to: t,
                kind: XrefKind::Call,
            }),
            Flow::Branch(t) | Flow::CondBranch(t) => out.push(Xref {
                from: i.addr,
                to: t,
                kind: XrefKind::Branch,
            }),
            _ => {}
        }

        track(i, &mut regs, mem, out);
    }
}

/// Update the register model for one instruction and emit any data reference
/// it completes.
fn track(i: &Insn, regs: &mut Regs, mem: &MemoryMap, out: &mut Vec<Xref>) {
    let ops = i.operands();
    match i.mnemonic {
        // adrp and adr put a resolved address straight into a register.
        "adrp" | "adr" => {
            if let (Some(Operand::Reg(d)), Some(Operand::Addr(a))) = (ops.first(), ops.get(1)) {
                regs.set(*d, a.get());
                if i.mnemonic == "adr" && mem.is_mapped(*a) {
                    out.push(Xref {
                        from: i.addr,
                        to: *a,
                        kind: XrefKind::Data,
                    });
                }
            }
        }
        // add rd, rn, #imm completes the pair.
        "add" => match (ops.first(), ops.get(1), ops.get(2)) {
            (Some(Operand::Reg(d)), Some(Operand::Reg(n)), Some(Operand::Imm(v))) => {
                match regs.get(*n) {
                    Some(base) => {
                        let val = base.wrapping_add(*v as u64);
                        regs.set(*d, val);
                        if mem.is_mapped(Addr(val)) {
                            out.push(Xref {
                                from: i.addr,
                                to: Addr(val),
                                kind: XrefKind::Data,
                            });
                        }
                    }
                    None => regs.forget(*d),
                }
            }
            (Some(Operand::Reg(d)), _, _) => regs.forget(*d),
            _ => {}
        },
        // mov rd, #imm seeds a constant; mov rd, rn copies one.
        "mov" => match (ops.first(), ops.get(1)) {
            (Some(Operand::Reg(d)), Some(Operand::Imm(v))) => regs.set(*d, *v as u64),
            (Some(Operand::Reg(d)), Some(Operand::UImm(v))) => regs.set(*d, *v),
            (Some(Operand::Reg(d)), Some(Operand::Reg(n))) => match regs.get(*n) {
                Some(v) => regs.set(*d, v),
                None => regs.forget(*d),
            },
            _ => {}
        },
        // A load or store through a tracked base is a reference to that slot.
        "ldr" | "ldrb" | "ldrh" | "ldrsb" | "ldrsh" | "ldrsw" | "str" | "strb" | "strh" => {
            let write = i.mnemonic.starts_with("str");
            let mut referenced = None;
            for op in ops {
                match op {
                    // A literal load names its target outright.
                    Operand::Addr(a) => referenced = Some(*a),
                    Operand::Mem(m) if m.index.is_none() => {
                        if let Some(base) = regs.get(m.base) {
                            let at = base.wrapping_add(m.disp as u64);
                            if mem.is_mapped(Addr(at)) {
                                referenced = Some(Addr(at));
                            }
                        }
                    }
                    _ => {}
                }
            }
            if let Some(to) = referenced {
                out.push(Xref {
                    from: i.addr,
                    to,
                    kind: if write {
                        XrefKind::Write
                    } else {
                        XrefKind::Read
                    },
                });
            }
            // The loaded value is unknown, so the destination is no longer
            // a constant we can trust.
            if !write {
                if let Some(Operand::Reg(d)) = ops.first() {
                    regs.forget(*d);
                }
            }
        }
        _ => {
            // Anything else invalidates whatever it writes. The first operand
            // is the destination in every AArch64 form that has one.
            if let Some(Operand::Reg(d)) = ops.first() {
                regs.forget(*d);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r12e_core::{AddrRange, Perms, Segment};

    fn mem_with(at: u64, len: u64) -> MemoryMap {
        let mut m = MemoryMap::new();
        m.add(
            Segment::new(
                AddrRange::sized(Addr(at), len).unwrap(),
                Perms::R,
                "data",
                0,
                vec![0; len as usize],
            )
            .unwrap(),
        );
        m
    }

    #[test]
    fn adrp_plus_add_resolves_to_one_reference() {
        // At 0x400000: adrp x0, 0x41c000 ; add x0, x0, #0x123
        let mem = mem_with(0x41c000, 0x1000);
        let insns: Vec<Insn> = [0x9000_00e0u32, 0x9104_8c00]
            .iter()
            .enumerate()
            .filter_map(|(n, w)| r12e_arch::aarch64::decode_word(*w, Addr(0x400000 + n as u64 * 4)))
            .collect();
        let mut out = Vec::new();
        collect(&insns, &mem, &mut out);
        let data: Vec<_> = out.iter().filter(|x| x.kind == XrefKind::Data).collect();
        assert_eq!(data.len(), 1, "{out:?}");
        assert_eq!(data[0].to, Addr(0x41c123));
    }

    #[test]
    fn a_branch_between_the_pair_stops_the_tracker() {
        // adrp x0, ... ; ret ; add x0, x0, #0x123
        // The add is not reachable from the adrp, so no data reference.
        let mem = mem_with(0x41c000, 0x1000);
        let words = [0x9000_00e0u32, 0xd65f_03c0, 0x9104_8c00];
        let insns: Vec<Insn> = words
            .iter()
            .enumerate()
            .filter_map(|(n, w)| r12e_arch::aarch64::decode_word(*w, Addr(0x400000 + n as u64 * 4)))
            .collect();
        let mut out = Vec::new();
        collect(&insns, &mem, &mut out);
        assert!(!out.iter().any(|x| x.kind == XrefKind::Data), "{out:?}");
    }

    #[test]
    fn unmapped_targets_are_not_reported() {
        let mem = mem_with(0x900000, 0x10);
        let insns: Vec<Insn> = [0x9000_00e0u32, 0x9104_8c00]
            .iter()
            .enumerate()
            .filter_map(|(n, w)| r12e_arch::aarch64::decode_word(*w, Addr(0x400000 + n as u64 * 4)))
            .collect();
        let mut out = Vec::new();
        collect(&insns, &mem, &mut out);
        assert!(!out.iter().any(|x| x.kind == XrefKind::Data));
    }

    #[test]
    fn the_index_answers_in_both_directions() {
        let x = |f: u64, t: u64, k| Xref {
            from: Addr(f),
            to: Addr(t),
            kind: k,
        };
        let ix = XrefIndex::build(vec![
            x(0x10, 0x100, XrefKind::Call),
            x(0x20, 0x100, XrefKind::Call),
            x(0x10, 0x200, XrefKind::Data),
        ]);
        assert_eq!(ix.to(Addr(0x100)).len(), 2);
        assert_eq!(ix.from(Addr(0x10)).len(), 2);
        assert_eq!(ix.to(Addr(0x300)).len(), 0);
    }
}
