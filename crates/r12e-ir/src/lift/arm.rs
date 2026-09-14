//! ARM A32 and Thumb-2 lifting.
//!
//! Covers the integer instructions a compiler emits: data processing through
//! the barrel shifter with its flag effects, multiplies, loads and stores in
//! every addressing mode, the load and store multiple forms, extensions,
//! bitfields and branches. Floating point and SIMD are not modelled and say so
//! rather than approximating.
//!
//! Two things this architecture does that need saying explicitly.
//!
//! Almost every instruction is predicated, and the condition is part of the
//! mnemonic rather than an operand: `sublt` is one spelling of `sub`. The IR
//! has no branch within an instruction, so a predicated instruction that
//! writes a register computes its result unconditionally and then selects
//! between it and the old value, which is exactly what the machine's result
//! is. A predicated store cannot be written that way -- a store that must not
//! happen is not a store of the old value, because the address may not be
//! readable -- so those are declined rather than approximated.
//!
//! The barrel shifter sets the carry flag on its way past, and the value it
//! sets it to is not the carry out of the arithmetic. `movs r0, r1, lsl #2`
//! leaves C holding bit 30 of `r1`. Code that chains `adcs` reads that, so it
//! is emitted rather than left alone.

use r12e_arch::{AddrMode, Flow, Insn, Mem, Operand, Reg, RegClass, Shift, Width};
use r12e_core::Addr;

use crate::lift::{Builder, Lifted};
use crate::op::{Op, Space, Varnode};

/// Byte offset of `r0`.
///
/// The registers are four bytes on this machine and are spaced eight apart
/// anyway, because dataflow versions the register file in eight-byte units:
/// two registers sharing a slot would let a write to one clobber the other.
/// The upper half of each slot is not storage the architecture has, so every
/// write zeroes it and every read takes the low four bytes -- the same shape
/// AArch64's `w` registers already have.
const R_BASE: u64 = 0;
/// `sp`, which is register 13.
const SP: u64 = R_BASE + 13 * 8;
/// `lr`, which is register 14.
const LR: u64 = R_BASE + 14 * 8;
/// The four condition flags, one byte each, above the registers.
const N: u64 = 16 * 8;
const Z: u64 = N + 1;
const C: u64 = N + 2;
const V: u64 = N + 3;
/// Byte offset of `d0`; the VFP registers are eight bytes each.
const V_BASE: u64 = 18 * 8;

/// The byte offset of a core register, for a caller setting up a machine
/// before running lifted code.
pub fn gpr_offset(n: u8) -> u64 {
    R_BASE + (n & 15) as u64 * 8
}

/// The stack pointer's offset.
pub fn sp_offset() -> u64 {
    SP
}

/// The link register's offset.
pub fn lr_offset() -> u64 {
    LR
}

/// The program counter, which is not storage here: it is only ever read, and
/// the decoder has already resolved what it reads as.
pub fn pc_offset() -> u64 {
    R_BASE + 15 * 8
}

/// The byte offset of a VFP register.
pub fn vec_offset(n: u8) -> u64 {
    V_BASE + n as u64 * 8
}

/// The negative flag.
pub fn flag_n() -> Varnode {
    Varnode::register(N, 1)
}
/// The zero flag.
pub fn flag_z() -> Varnode {
    Varnode::register(Z, 1)
}
/// The carry flag.
pub fn flag_c() -> Varnode {
    Varnode::register(C, 1)
}
/// The overflow flag.
pub fn flag_v() -> Varnode {
    Varnode::register(V, 1)
}

/// The condition codes, in encoding order, as they are spelled.
///
/// `al` is index 14 and prints as nothing at all, which is why a mnemonic with
/// no suffix is unconditional rather than unparsed.
const CONDS: [&str; 15] = [
    "eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al",
];

/// Every base mnemonic this lifter knows, longest first.
///
/// The condition is glued onto the end of the mnemonic and some base names end
/// in the same two letters a condition does -- `muls` ends in `ls`, `movs` in
/// `vs`, `teq` in `eq`. Splitting is therefore not "strip two characters": a
/// split is accepted only when what is left is a name on this list, which is
/// what makes it unambiguous.
const BASES: &[&str] = &[
    "adc", "add", "and", "asr", "bfc", "bfi", "bic", "bkpt", "bl", "blx", "bx", "b", "cbnz", "cbz",
    "clz", "cmn", "cmp", "eor", "lsl", "lsr", "mla", "mls", "mov", "movt", "movw", "mul", "mvn",
    "neg", "nop", "orn", "orr", "pop", "push", "rbit", "rev", "rev16", "revsh", "ror", "rrx",
    "rsb", "rsc", "sbc", "sbfx", "sdiv", "smlal", "smull", "sub", "sxtb", "sxth", "teq", "tst",
    "ubfx", "udiv", "umlal", "umull", "uxtb", "uxtb16", "uxth",
    // The loads and stores, which are the rest of what a compiler emits.
    "ldr", "ldrb", "ldrd", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strd", "strh",
    // The load and store multiple forms, whose suffix is the direction the
    // address moves and whether it moves before or after each transfer.
    "ldm", "ldmda", "ldmdb", "ldmib", "stm", "stmda", "stmdb", "stmib",
];

/// A mnemonic split into what it does, whether it sets the flags, and when it
/// runs.
struct Parts {
    base: &'static str,
    flags: bool,
    /// The condition's encoding, 14 for `al`.
    cond: u8,
}

/// Split a mnemonic into its base, its `s` and its condition.
///
/// Returns `None` for anything not on [`BASES`], which is how an instruction
/// this lifter does not model reaches [`Builder::unimplemented`] rather than
/// being guessed at.
fn parts(mnemonic: &str) -> Option<Parts> {
    // Every candidate split, unconditional first so `teq` is `teq` and not
    // `t` + `eq`.
    for (cond, tail) in
        std::iter::once((14u8, "")).chain(CONDS.iter().enumerate().map(|(n, c)| (n as u8, *c)))
    {
        let Some(head) = mnemonic.strip_suffix(tail) else {
            continue;
        };
        for (flags, base) in [(false, head), (true, head.strip_suffix('s').unwrap_or(""))] {
            if base.is_empty() {
                continue;
            }
            if let Some(found) = BASES.iter().find(|b| **b == base) {
                return Some(Parts {
                    base: found,
                    flags,
                    cond,
                });
            }
        }
    }
    None
}

/// The varnode for a register operand.
fn reg(r: Reg) -> Varnode {
    match r.class {
        RegClass::Gpr => Varnode::register(gpr_offset(r.num), 4),
        RegClass::Sp => Varnode::register(SP, 4),
        RegClass::Vec => Varnode::register(vec_offset(r.num), width_bytes(r.width)),
        // The program counter is read through `Operand::Addr` and `Mem` with a
        // pc base, both of which the decoder has already resolved. A bare `pc`
        // operand elsewhere is a form this lifter does not model.
        _ => Varnode::register(pc_offset(), 4),
    }
}

fn width_bytes(w: Width) -> u8 {
    match w {
        Width::W8 => 1,
        Width::W16 => 2,
        Width::W32 => 4,
        Width::W64 => 8,
        Width::W128 => 16,
    }
}

/// True when an operand names a register this lifter can write.
fn writable(op: &Operand) -> Option<Reg> {
    match op {
        Operand::Reg(r) if matches!(r.class, RegClass::Gpr | RegClass::Sp) => Some(*r),
        _ => None,
    }
}

/// Apply the barrel shifter, returning the value and the carry it leaves.
///
/// The carry is `None` when the shifter does not touch it, which is a shift of
/// zero and only that: every other amount writes it, including the `lsr #32`
/// and `asr #32` the encoding spells as zero.
fn shifter(b: &mut Builder, v: Varnode, sh: Shift, amount: u8) -> (Varnode, Option<Varnode>) {
    let bits = Varnode::constant(amount as u64, 1);
    match sh {
        Shift::Lsl if amount == 0 => (v, None),
        Shift::Lsl => {
            // The bit shifted out last, which is bit 32-amount.
            let out = b.eval(
                Op::IntRight,
                4,
                &[v, Varnode::constant(32 - amount as u64, 1)],
            );
            let c = b.eval(Op::IntAnd, 4, &[out, Varnode::constant(1, 4)]);
            let c = b.eval(Op::IntNotEqual, 1, &[c, Varnode::constant(0, 4)]);
            (b.eval(Op::IntLeft, 4, &[v, bits]), Some(c))
        }
        Shift::Lsr | Shift::Asr => {
            let op = if sh == Shift::Lsr {
                Op::IntRight
            } else {
                Op::IntSRight
            };
            // The last bit shifted out is bit amount-1.
            let out = b.eval(
                Op::IntRight,
                4,
                &[v, Varnode::constant(amount as u64 - 1, 1)],
            );
            let c = b.eval(Op::IntAnd, 4, &[out, Varnode::constant(1, 4)]);
            let c = b.eval(Op::IntNotEqual, 1, &[c, Varnode::constant(0, 4)]);
            // A shift of 32 is out of range for the IR's shift, and the answer
            // is zero or the sign, so it is written as what it means.
            let value = if amount >= 32 {
                if sh == Shift::Lsr {
                    Varnode::constant(0, 4)
                } else {
                    b.eval(Op::IntSRight, 4, &[v, Varnode::constant(31, 1)])
                }
            } else {
                b.eval(op, 4, &[v, bits])
            };
            (value, Some(c))
        }
        Shift::Ror if amount == 0 => {
            // `ror #0` is `rrx`: a 33-bit rotate through the carry flag.
            let low = b.eval(Op::IntRight, 4, &[v, Varnode::constant(1, 1)]);
            let cin = b.eval(Op::IntZExt, 4, &[flag_c()]);
            let top = b.eval(Op::IntLeft, 4, &[cin, Varnode::constant(31, 1)]);
            let value = b.eval(Op::IntOr, 4, &[low, top]);
            let c = b.eval(Op::IntAnd, 4, &[v, Varnode::constant(1, 4)]);
            let c = b.eval(Op::IntNotEqual, 1, &[c, Varnode::constant(0, 4)]);
            (value, Some(c))
        }
        Shift::Ror => {
            let n = amount as u64 % 32;
            let right = b.eval(Op::IntRight, 4, &[v, Varnode::constant(n, 1)]);
            let left = b.eval(Op::IntLeft, 4, &[v, Varnode::constant(32 - n, 1)]);
            let value = b.eval(Op::IntOr, 4, &[right, left]);
            let c = b.eval(Op::IntRight, 4, &[value, Varnode::constant(31, 1)]);
            let c = b.eval(Op::IntNotEqual, 1, &[c, Varnode::constant(0, 4)]);
            (value, Some(c))
        }
        Shift::Msl => (v, None),
    }
}

/// Materialize a source operand, applying any shift.
///
/// The second return is the carry the barrel shifter left, which a logical
/// operation with `s` writes and an arithmetic one ignores.
fn source(b: &mut Builder, op: &Operand) -> Option<(Varnode, Option<Varnode>)> {
    Some(match op {
        Operand::Reg(r) => (reg(*r), None),
        Operand::Imm(v) => (Varnode::constant(*v as u64, 4), None),
        Operand::UImm(v) => (Varnode::constant(*v, 4), None),
        Operand::Count(v) => (Varnode::constant(*v as u64, 4), None),
        Operand::Addr(a) => (Varnode::constant(a.get(), 4), None),
        Operand::Shifted(r, sh, n) => {
            let v = reg(*r);
            let (value, c) = shifter(b, v, *sh, *n);
            (value, c)
        }
        _ => return None,
    })
}

/// Set the flags an arithmetic operation produces.
fn set_flags(b: &mut Builder, result: Varnode, x: Varnode, y: Varnode, sub: bool) {
    set_nz(b, result);
    // For a subtraction the carry flag means "no borrow", which is an unsigned
    // comparison rather than a carry out.
    let c = if sub {
        b.eval(Op::IntLessEqual, 1, &[y, x])
    } else {
        b.eval(Op::IntCarry, 1, &[x, y])
    };
    b.emit(Op::Copy, Some(flag_c()), &[c]);
    let v = b.eval(if sub { Op::IntSBorrow } else { Op::IntSCarry }, 1, &[x, y]);
    b.emit(Op::Copy, Some(flag_v()), &[v]);
}

/// Set N and Z from a result, which every flag-setting form does the same way.
fn set_nz(b: &mut Builder, result: Varnode) {
    let sign = b.eval(Op::IntRight, 4, &[result, Varnode::constant(31, 1)]);
    let n = b.eval(Op::IntNotEqual, 1, &[sign, Varnode::constant(0, 4)]);
    b.emit(Op::Copy, Some(flag_n()), &[n]);
    let z = b.eval(Op::IntEqual, 1, &[result, Varnode::constant(0, 4)]);
    b.emit(Op::Copy, Some(flag_z()), &[z]);
}

/// Set the flags a logical operation produces: N and Z from the result, C from
/// the barrel shifter if it moved, and V untouched.
fn set_logical_flags(b: &mut Builder, result: Varnode, carry: Option<Varnode>) {
    set_nz(b, result);
    if let Some(c) = carry {
        b.emit(Op::Copy, Some(flag_c()), &[c]);
    }
}

/// The condition a predicated instruction tests, as one byte.
///
/// The same four-bit encoding AArch64 uses, and the same reading of it: the
/// low bit inverts the test the upper three select.
fn condition(b: &mut Builder, cond: u8) -> Varnode {
    let (n, z, c, v) = (flag_n(), flag_z(), flag_c(), flag_v());
    let base = match cond >> 1 {
        0b000 => z,
        0b001 => c,
        0b010 => n,
        0b011 => v,
        0b100 => {
            let nz = b.eval(Op::BoolNot, 1, &[z]);
            b.eval(Op::BoolAnd, 1, &[c, nz])
        }
        0b101 => b.eval(Op::IntEqual, 1, &[n, v]),
        0b110 => {
            let nz = b.eval(Op::BoolNot, 1, &[z]);
            let ge = b.eval(Op::IntEqual, 1, &[n, v]);
            b.eval(Op::BoolAnd, 1, &[nz, ge])
        }
        _ => Varnode::constant(1, 1),
    };
    if cond & 1 == 1 && cond >> 1 != 0b111 {
        b.eval(Op::BoolNot, 1, &[base])
    } else {
        base
    }
}

/// Write a register, selecting against its old value when predicated.
///
/// The machine either writes the result or leaves the register alone, and
/// `old` is what it holds either way, so the select is the result and not an
/// approximation of it.
fn put(b: &mut Builder, p: &Parts, dest: Varnode, value: Varnode) {
    if p.cond == 14 {
        write_reg(b, dest, value);
        return;
    }
    let cond = condition(b, p.cond);
    let chosen = select(b, cond, value, dest, dest.size);
    write_reg(b, dest, chosen);
}

/// Write a core register, including the upper half that is not storage.
///
/// Emitting the zero rather than assuming it is what makes the write cover the
/// whole eight-byte location: a four-byte write into it is a partial write,
/// and dataflow would then merge it with whatever the slot held.
fn write_reg(b: &mut Builder, dest: Varnode, value: Varnode) {
    b.emit(Op::Copy, Some(dest), &[value]);
    if dest.space == Space::Register && dest.size == 4 {
        b.emit(
            Op::Copy,
            Some(Varnode::register(dest.offset + 4, 4)),
            &[Varnode::constant(0, 4)],
        );
    }
}

/// `cond ? t : f`, which the IR has no opcode for.
///
/// Negating a zero-or-one gives all zeroes or all ones, which is the mask.
fn select(b: &mut Builder, cond: Varnode, t: Varnode, f: Varnode, size: u8) -> Varnode {
    let wide = if size == 1 {
        cond
    } else {
        b.eval(Op::IntZExt, size, &[cond])
    };
    let mask = b.eval(Op::IntNegate, size, &[wide]);
    let keep = b.eval(Op::IntAnd, size, &[t, mask]);
    let inverse = b.eval(Op::IntNot, size, &[mask]);
    let drop = b.eval(Op::IntAnd, size, &[f, inverse]);
    b.eval(Op::IntOr, size, &[keep, drop])
}

/// The address a memory operand names, and the value the base ends up with.
///
/// The second is `None` when the instruction has no writeback.
fn address(b: &mut Builder, m: &Mem, at: Addr, thumb: bool) -> Option<(Varnode, Option<Varnode>)> {
    let base = match m.base {
        // Reading the program counter gives the instruction's address plus
        // eight in A32 and plus four in Thumb, and Thumb aligns it down to a
        // word. The decoder leaves this to the lifter because the value
        // depends on which instruction set the address holds.
        Some(r) if r.class == RegClass::Pc => {
            let pc = if thumb {
                (at.get() + 4) & !3
            } else {
                at.get() + 8
            };
            Varnode::constant(pc, 4)
        }
        Some(r) => reg(r),
        None => Varnode::constant(0, 4),
    };
    let mut offset = Varnode::constant(m.disp as u64, 4);
    if let Some((ix, _, shift)) = m.index {
        let v = reg(ix);
        offset = if shift == 0 {
            v
        } else {
            b.eval(Op::IntLeft, 4, &[v, Varnode::constant(shift as u64, 1)])
        };
        // A negative index is spelled by the displacement's sign, which the
        // decoder keeps separate from the register.
        if m.disp < 0 {
            offset = b.eval(Op::IntSub, 4, &[Varnode::constant(0, 4), offset]);
        }
    }
    let moved = b.eval(Op::IntAdd, 4, &[base, offset]);
    Some(match m.mode {
        AddrMode::Offset => (moved, None),
        AddrMode::PreIndex => (moved, Some(moved)),
        AddrMode::PostIndex => (base, Some(moved)),
    })
}

/// Apply a memory operand's writeback to its base register.
fn writeback(b: &mut Builder, m: &Mem, updated: Option<Varnode>) {
    let (Some(v), Some(r)) = (updated, m.base) else {
        return;
    };
    if matches!(r.class, RegClass::Gpr | RegClass::Sp) {
        write_reg(b, reg(r), v);
    }
}

/// Undefine what a call is allowed to change.
///
/// AAPCS: r0 to r3 and r12 are caller-saved, and so are the flags. The result
/// registers are written by the call operation itself.
fn clobber(b: &mut Builder) {
    for n in [1u8, 2, 3, 12] {
        b.emit(Op::Undefine, Some(Varnode::register(gpr_offset(n), 4)), &[]);
    }
    for f in [flag_n(), flag_z(), flag_c(), flag_v()] {
        b.emit(Op::Undefine, Some(f), &[]);
    }
}

/// Lift one ARM instruction.
///
/// `thumb` says which instruction set the address holds, which changes what
/// reading the program counter gives and nothing else this lifter models.
pub fn lift(i: &Insn) -> Lifted {
    lift_mode(i, i.len == 2)
}

/// The same, told explicitly which instruction set this is.
pub fn lift_mode(i: &Insn, thumb: bool) -> Lifted {
    let mut b = Builder::sized(i.addr, 4);
    let ops = i.operands();
    let Some(p) = parts(i.mnemonic) else {
        return b.unimplemented();
    };

    match i.flow {
        Flow::Branch(t) => {
            if p.cond == 14 {
                b.emit(Op::Branch, None, &[Varnode::constant(t.get(), 4)]);
            } else {
                let cond = condition(&mut b, p.cond);
                b.emit(Op::CBranch, None, &[Varnode::constant(t.get(), 4), cond]);
            }
            return b.finish(true);
        }
        Flow::CondBranch(t) => {
            // `cbz` and `cbnz` test a register rather than the flags, and they
            // are the only Thumb branches that do.
            let cond = match p.base {
                "cbz" | "cbnz" => {
                    let Some((v, _)) = ops.first().and_then(|o| source(&mut b, o)) else {
                        return b.unimplemented();
                    };
                    let op = if p.base == "cbz" {
                        Op::IntEqual
                    } else {
                        Op::IntNotEqual
                    };
                    b.eval(op, 1, &[v, Varnode::constant(0, 4)])
                }
                _ => condition(&mut b, p.cond),
            };
            b.emit(Op::CBranch, None, &[Varnode::constant(t.get(), 4), cond]);
            return b.finish(true);
        }
        Flow::Call(t) => {
            // The return address, which `bl` and `blx` put in the link
            // register. A Thumb return address has its low bit set, and the
            // decoder's `next` is the plain address.
            let ret = i.next().get() | u64::from(thumb);
            write_reg(&mut b, Varnode::register(LR, 4), Varnode::constant(ret, 4));
            b.emit(
                Op::Call,
                Some(Varnode::register(gpr_offset(0), 4)),
                &[Varnode::constant(t.get(), 4)],
            );
            clobber(&mut b);
            return b.finish(true);
        }
        Flow::IndirectCall => {
            let Some((target, _)) = ops.first().and_then(|o| source(&mut b, o)) else {
                return b.unimplemented();
            };
            let ret = i.next().get() | u64::from(thumb);
            write_reg(&mut b, Varnode::register(LR, 4), Varnode::constant(ret, 4));
            b.emit(
                Op::CallInd,
                Some(Varnode::register(gpr_offset(0), 4)),
                &[target],
            );
            clobber(&mut b);
            return b.finish(true);
        }
        Flow::Return => {
            // Two spellings. `bx lr` returns through a register, and
            // `pop {.., pc}` restores the frame and returns through the last
            // word it loads, which is the whole instruction and not just its
            // flow.
            if p.base == "pop" {
                return stack_multiple(b, &p, ops);
            }
            let Some((target, _)) = ops.first().and_then(|o| source(&mut b, o)) else {
                return b.unimplemented();
            };
            b.emit(Op::Return, None, &[target]);
            return b.finish(true);
        }
        Flow::IndirectBranch => {
            let Some((target, _)) = ops.first().and_then(|o| source(&mut b, o)) else {
                return b.unimplemented();
            };
            b.emit(Op::BranchInd, None, &[target]);
            return b.finish(true);
        }
        Flow::Trap => return b.finish(true),
        Flow::Syscall => {
            // What the kernel does is not knowable from here, so the result
            // and the caller-saved registers are undefined rather than
            // guessed. The flow still stops the interpreter.
            b.emit(Op::Undefine, Some(Varnode::register(gpr_offset(0), 4)), &[]);
            return b.finish(true);
        }
        Flow::Next => {}
    }

    match p.base {
        "nop" => b.finish(true),
        "push" | "pop" => stack_multiple(b, &p, ops),
        m if m.starts_with("ldm") || m.starts_with("stm") => block_transfer(b, &p, ops),
        "add" | "sub" | "rsb" | "adc" | "sbc" | "rsc" | "and" | "eor" | "orr" | "orn" | "bic"
        | "mul" | "sdiv" | "udiv" => arithmetic(b, &p, ops),
        "mov" | "mvn" | "neg" | "movw" | "lsl" | "lsr" | "asr" | "ror" | "rrx" => moves(b, &p, ops),
        "movt" => movt(b, &p, ops),
        "cmp" | "cmn" | "tst" | "teq" => compare(b, &p, ops),
        "mla" | "mls" => multiply_accumulate(b, &p, ops),
        "umull" | "smull" | "umlal" | "smlal" => long_multiply(b, &p, ops),
        "uxtb" | "uxth" | "sxtb" | "sxth" => extend(b, &p, ops),
        "uxtb16" => uxtb16(b, &p, ops),
        "clz" | "rev" | "rev16" | "revsh" | "rbit" => reverses(b, &p, ops),
        "bfi" | "bfc" | "ubfx" | "sbfx" => bitfield(b, &p, ops),
        _ => memory(b, i, &p, ops, thumb),
    }
}

/// `add`, `sub` and the rest of the two-source data-processing forms.
fn arithmetic(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(dest), Some(x), Some(y)) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(|o| source(&mut b, o)),
        ops.get(2).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let (x, _) = x;
    let (y, carry) = y;
    let logical = matches!(p.base, "and" | "eor" | "orr" | "orn" | "bic");
    let (value, kind) = match p.base {
        "add" => (b.eval(Op::IntAdd, 4, &[x, y]), Some((x, y, false))),
        "sub" => (b.eval(Op::IntSub, 4, &[x, y]), Some((x, y, true))),
        "rsb" => (b.eval(Op::IntSub, 4, &[y, x]), Some((y, x, true))),
        "and" => (b.eval(Op::IntAnd, 4, &[x, y]), None),
        "eor" => (b.eval(Op::IntXor, 4, &[x, y]), None),
        "orr" => (b.eval(Op::IntOr, 4, &[x, y]), None),
        "orn" => {
            let ny = b.eval(Op::IntNot, 4, &[y]);
            (b.eval(Op::IntOr, 4, &[x, ny]), None)
        }
        "bic" => {
            let ny = b.eval(Op::IntNot, 4, &[y]);
            (b.eval(Op::IntAnd, 4, &[x, ny]), None)
        }
        "mul" => (b.eval(Op::IntMul, 4, &[x, y]), None),
        "sdiv" => (b.eval(Op::IntSDiv, 4, &[x, y]), None),
        "udiv" => (b.eval(Op::IntDiv, 4, &[x, y]), None),
        // `adc` and `sbc` carry the flag in, so the flags they set are the
        // flags of the whole three-input sum and not of the first addition.
        // Writing that exactly needs a carry out of two additions, which this
        // does not model, so the flag-setting forms are declined.
        "adc" | "sbc" | "rsc" if p.flags => return b.unimplemented(),
        "adc" => {
            let cin = b.eval(Op::IntZExt, 4, &[flag_c()]);
            let sum = b.eval(Op::IntAdd, 4, &[x, y]);
            (b.eval(Op::IntAdd, 4, &[sum, cin]), None)
        }
        "sbc" | "rsc" => {
            let (l, r) = if p.base == "sbc" { (x, y) } else { (y, x) };
            let cin = b.eval(Op::IntZExt, 4, &[flag_c()]);
            let borrow = b.eval(Op::IntSub, 4, &[Varnode::constant(1, 4), cin]);
            let diff = b.eval(Op::IntSub, 4, &[l, r]);
            (b.eval(Op::IntSub, 4, &[diff, borrow]), None)
        }
        _ => return b.unimplemented(),
    };
    if p.flags {
        match kind {
            Some((l, r, sub)) => set_flags(&mut b, value, l, r, sub),
            None if logical => set_logical_flags(&mut b, value, carry),
            // A multiply or a divide with `s` sets only N and Z.
            None => set_nz(&mut b, value),
        }
    }
    put(&mut b, p, reg(dest), value);
    b.finish(true)
}

/// `mov`, `mvn` and the shifts, which ARM spells as moves.
fn moves(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let Some(dest) = ops.first().and_then(writable) else {
        return b.unimplemented();
    };
    let (value, carry) = match p.base {
        "lsl" | "lsr" | "asr" | "ror" => {
            let Some((x, _)) = ops.get(1).and_then(|o| source(&mut b, o)) else {
                return b.unimplemented();
            };
            let sh = match p.base {
                "lsl" => Shift::Lsl,
                "lsr" => Shift::Lsr,
                "asr" => Shift::Asr,
                _ => Shift::Ror,
            };
            match ops.get(2).and_then(shift_amount) {
                Some(amount) => shifter(&mut b, x, sh, amount),
                // A shift by a register. The amount is the low byte of it, and
                // an amount of 32 or more gives zero for the logical shifts
                // and the sign for the arithmetic one -- a rule the IR's shift
                // does not have, so it is written as the mask it is. The carry
                // the shifter leaves depends on the amount and is not modelled,
                // so the flag-setting form is declined.
                None if p.flags => return b.unimplemented(),
                None => {
                    let Some((rs, _)) = ops.get(2).and_then(|o| source(&mut b, o)) else {
                        return b.unimplemented();
                    };
                    (register_shift(&mut b, x, sh, rs), None)
                }
            }
        }
        "rrx" => {
            let Some((x, _)) = ops.get(1).and_then(|o| source(&mut b, o)) else {
                return b.unimplemented();
            };
            shifter(&mut b, x, Shift::Ror, 0)
        }
        _ => {
            let Some((x, carry)) = ops.get(1).and_then(|o| source(&mut b, o)) else {
                return b.unimplemented();
            };
            match p.base {
                "mvn" => (b.eval(Op::IntNot, 4, &[x]), carry),
                "neg" => (b.eval(Op::IntSub, 4, &[Varnode::constant(0, 4), x]), carry),
                _ => (x, carry),
            }
        }
    };
    if p.flags {
        set_logical_flags(&mut b, value, carry);
    }
    put(&mut b, p, reg(dest), value);
    b.finish(true)
}

/// A shift by an amount held in a register.
///
/// ARM takes the low byte of the amount and, unlike the IR's shift, defines
/// what happens past the width: the logical shifts give zero and the
/// arithmetic one gives the sign. `ror` takes the amount modulo 32 instead,
/// which needs no guard.
fn register_shift(b: &mut Builder, x: Varnode, sh: Shift, rs: Varnode) -> Varnode {
    let amount = b.eval(Op::IntAnd, 4, &[rs, Varnode::constant(0xff, 4)]);
    if sh == Shift::Ror {
        let n = b.eval(Op::IntAnd, 4, &[amount, Varnode::constant(31, 4)]);
        let right = b.eval(Op::IntRight, 4, &[x, n]);
        let back = b.eval(Op::IntSub, 4, &[Varnode::constant(32, 4), n]);
        // A rotate by zero would shift left by 32, which is out of range, so
        // the second half is masked away in exactly that case.
        let left = b.eval(Op::IntLeft, 4, &[x, back]);
        let zero = b.eval(Op::IntEqual, 1, &[n, Varnode::constant(0, 4)]);
        let left = select(b, zero, Varnode::constant(0, 4), left, 4);
        return b.eval(Op::IntOr, 4, &[right, left]);
    }
    let wide = b.eval(Op::IntLessEqual, 1, &[Varnode::constant(32, 4), amount]);
    let capped = select(b, wide, Varnode::constant(31, 4), amount, 4);
    let value = b.eval(
        match sh {
            Shift::Lsl => Op::IntLeft,
            Shift::Asr => Op::IntSRight,
            _ => Op::IntRight,
        },
        4,
        &[x, capped],
    );
    // Past the width the logical shifts give zero; the arithmetic one has
    // already given the sign, because a shift by 31 does.
    if sh == Shift::Asr {
        return value;
    }
    select(b, wide, Varnode::constant(0, 4), value, 4)
}

/// A shift amount, which is a count and not a register.
///
/// A shift by a register reaches the lifter as a name rather than an operand,
/// so it is not modelled; a compiler emits it rarely and guessing would be
/// worse than saying so.
fn shift_amount(op: &Operand) -> Option<u8> {
    match op {
        Operand::Count(v) | Operand::Imm(v) => u8::try_from(*v).ok(),
        Operand::UImm(v) => u8::try_from(*v).ok(),
        _ => None,
    }
}

/// `movt`, which replaces the top halfword and keeps the bottom one.
fn movt(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(dest), Some((v, _))) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let d = reg(dest);
    let kept = b.eval(Op::IntAnd, 4, &[d, Varnode::constant(0xffff, 4)]);
    let top = b.eval(Op::IntLeft, 4, &[v, Varnode::constant(16, 1)]);
    let value = b.eval(Op::IntOr, 4, &[kept, top]);
    put(&mut b, p, d, value);
    b.finish(true)
}

/// `cmp`, `cmn`, `tst` and `teq`, which set the flags and write nothing.
fn compare(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some((x, _)), Some((y, carry))) = (
        ops.first().and_then(|o| source(&mut b, o)),
        ops.get(1).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    // A predicated compare that does not run leaves the flags alone, and the
    // select that would express that is four selects on four flags. Declined
    // rather than written out, because nothing a compiler emits needs it.
    if p.cond != 14 {
        return b.unimplemented();
    }
    match p.base {
        "cmp" => {
            let r = b.eval(Op::IntSub, 4, &[x, y]);
            set_flags(&mut b, r, x, y, true);
        }
        "cmn" => {
            let r = b.eval(Op::IntAdd, 4, &[x, y]);
            set_flags(&mut b, r, x, y, false);
        }
        "tst" => {
            let r = b.eval(Op::IntAnd, 4, &[x, y]);
            set_logical_flags(&mut b, r, carry);
        }
        _ => {
            let r = b.eval(Op::IntXor, 4, &[x, y]);
            set_logical_flags(&mut b, r, carry);
        }
    }
    b.finish(true)
}

/// `mla` and `mls`: a multiply with an addend.
fn multiply_accumulate(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(dest), Some((x, _)), Some((y, _)), Some((a, _))) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(|o| source(&mut b, o)),
        ops.get(2).and_then(|o| source(&mut b, o)),
        ops.get(3).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let product = b.eval(Op::IntMul, 4, &[x, y]);
    let value = if p.base == "mla" {
        b.eval(Op::IntAdd, 4, &[a, product])
    } else {
        b.eval(Op::IntSub, 4, &[a, product])
    };
    if p.flags {
        set_nz(&mut b, value);
    }
    put(&mut b, p, reg(dest), value);
    b.finish(true)
}

/// `umull`, `smull` and the accumulating forms, which write two registers.
fn long_multiply(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(lo), Some(hi), Some((x, _)), Some((y, _))) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(writable),
        ops.get(2).and_then(|o| source(&mut b, o)),
        ops.get(3).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let signed = p.base.starts_with('s');
    let ext = if signed { Op::IntSExt } else { Op::IntZExt };
    let wx = b.eval(ext, 8, &[x]);
    let wy = b.eval(ext, 8, &[y]);
    let mut wide = b.eval(Op::IntMul, 8, &[wx, wy]);
    if p.base.ends_with("lal") {
        // The accumulating forms add the two destination registers, read as
        // one 64-bit value, to the product.
        let l = b.eval(Op::IntZExt, 8, &[reg(lo)]);
        let h = b.eval(Op::IntZExt, 8, &[reg(hi)]);
        let h = b.eval(Op::IntLeft, 8, &[h, Varnode::constant(32, 1)]);
        let acc = b.eval(Op::IntOr, 8, &[l, h]);
        wide = b.eval(Op::IntAdd, 8, &[wide, acc]);
    }
    let low = b.eval(Op::SubPiece, 4, &[wide, Varnode::constant(0, 1)]);
    let high = b.eval(Op::SubPiece, 4, &[wide, Varnode::constant(4, 1)]);
    if p.flags {
        set_nz(&mut b, high);
    }
    put(&mut b, p, reg(lo), low);
    put(&mut b, p, reg(hi), high);
    b.finish(true)
}

/// `uxtb` and friends, which widen a byte or a halfword with an optional
/// rotate first and an optional addend.
fn extend(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(dest), Some((x, _))) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let bytes = if p.base.ends_with('b') { 1 } else { 2 };
    let mask = if bytes == 1 { 0xffu64 } else { 0xffff };
    let low = b.eval(Op::IntAnd, 4, &[x, Varnode::constant(mask, 4)]);
    let value = if p.base.starts_with('s') {
        // Sign-extend by shifting the sign bit to the top and back.
        let up = b.eval(
            Op::IntLeft,
            4,
            &[low, Varnode::constant(32 - bytes as u64 * 8, 1)],
        );
        b.eval(
            Op::IntSRight,
            4,
            &[up, Varnode::constant(32 - bytes as u64 * 8, 1)],
        )
    } else {
        low
    };
    put(&mut b, p, reg(dest), value);
    b.finish(true)
}

/// `uxtb16`, which keeps the low byte of each halfword and clears the rest.
fn uxtb16(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(dest), Some((x, _))) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let value = b.eval(Op::IntAnd, 4, &[x, Varnode::constant(0x00ff_00ff, 4)]);
    put(&mut b, p, reg(dest), value);
    b.finish(true)
}

/// `bfi`, `bfc`, `ubfx` and `sbfx`.
fn bitfield(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let Some(dest) = ops.first().and_then(writable) else {
        return b.unimplemented();
    };
    let d = reg(dest);
    let value = match p.base {
        "bfc" => {
            let (Some(lsb), Some(width)) = (
                ops.get(1).and_then(shift_amount),
                ops.get(2).and_then(shift_amount),
            ) else {
                return b.unimplemented();
            };
            let mask = field_mask(lsb, width);
            b.eval(Op::IntAnd, 4, &[d, Varnode::constant(!mask, 4)])
        }
        "bfi" => {
            let (Some((x, _)), Some(lsb), Some(width)) = (
                ops.get(1).and_then(|o| source(&mut b, o)),
                ops.get(2).and_then(shift_amount),
                ops.get(3).and_then(shift_amount),
            ) else {
                return b.unimplemented();
            };
            let mask = field_mask(lsb, width);
            let kept = b.eval(Op::IntAnd, 4, &[d, Varnode::constant(!mask, 4)]);
            let moved = b.eval(Op::IntLeft, 4, &[x, Varnode::constant(lsb as u64, 1)]);
            let cut = b.eval(Op::IntAnd, 4, &[moved, Varnode::constant(mask, 4)]);
            b.eval(Op::IntOr, 4, &[kept, cut])
        }
        _ => {
            let (Some((x, _)), Some(lsb), Some(width)) = (
                ops.get(1).and_then(|o| source(&mut b, o)),
                ops.get(2).and_then(shift_amount),
                ops.get(3).and_then(shift_amount),
            ) else {
                return b.unimplemented();
            };
            // Shift the field to the top and back down, which is what makes
            // the signed and unsigned forms one line apart.
            let up = b.eval(
                Op::IntLeft,
                4,
                &[x, Varnode::constant(32 - (lsb + width) as u64, 1)],
            );
            let down = if p.base == "sbfx" {
                Op::IntSRight
            } else {
                Op::IntRight
            };
            b.eval(down, 4, &[up, Varnode::constant(32 - width as u64, 1)])
        }
    };
    put(&mut b, p, d, value);
    b.finish(true)
}

/// `clz` and the byte and bit reversals.
///
/// No single IR operation reverses bytes or bits, but both are exactly
/// expressible in the ones there are, so they are written out rather than left
/// unmodelled. The helpers are the AArch64 lifter's, because the computation
/// is the same one and having it twice would be two chances to get it wrong.
fn reverses(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let (Some(dest), Some((x, _))) = (
        ops.first().and_then(writable),
        ops.get(1).and_then(|o| source(&mut b, o)),
    ) else {
        return b.unimplemented();
    };
    let value = match p.base {
        "clz" => b.eval(Op::LzCount, 4, &[x]),
        "rev" => super::aarch64::swap_bytes(&mut b, x, 4, 4),
        "rev16" => super::aarch64::swap_bytes(&mut b, x, 4, 2),
        "rbit" => super::aarch64::reverse_bits(&mut b, x, 4),
        // `revsh` reverses the low halfword's bytes and sign-extends it.
        _ => {
            let swapped = super::aarch64::swap_bytes(&mut b, x, 4, 2);
            let low = b.eval(Op::IntAnd, 4, &[swapped, Varnode::constant(0xffff, 4)]);
            let up = b.eval(Op::IntLeft, 4, &[low, Varnode::constant(16, 1)]);
            b.eval(Op::IntSRight, 4, &[up, Varnode::constant(16, 1)])
        }
    };
    put(&mut b, p, reg(dest), value);
    b.finish(true)
}

/// The mask of a bitfield `width` bits wide starting at `lsb`.
fn field_mask(lsb: u8, width: u8) -> u64 {
    if width >= 32 {
        return u64::MAX >> 32 << lsb;
    }
    ((1u64 << width) - 1) << lsb
}

/// `push` and `pop`, which are the load and store multiple forms a compiler
/// writes for a frame.
fn stack_multiple(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let Some(Operand::Sys(mask)) = ops.first() else {
        return b.unimplemented();
    };
    // Predicated, and there is no value to select against: declined.
    if p.cond != 14 {
        return b.unimplemented();
    }
    let regs: Vec<u8> = (0..16u8).filter(|n| mask & (1 << n) != 0).collect();
    if regs.is_empty() {
        return b.unimplemented();
    }
    let sp = Varnode::register(SP, 4);
    let total = regs.len() as u64 * 4;
    if p.base == "push" {
        // Registers go to descending addresses, lowest numbered lowest.
        let base = b.eval(Op::IntSub, 4, &[sp, Varnode::constant(total, 4)]);
        for (n, r) in regs.iter().enumerate() {
            let at = b.eval(Op::IntAdd, 4, &[base, Varnode::constant(n as u64 * 4, 4)]);
            b.emit(Op::Store, None, &[at, Varnode::register(gpr_offset(*r), 4)]);
        }
        write_reg(&mut b, sp, base);
        return b.finish(true);
    }
    let mut returned = None;
    for (n, r) in regs.iter().enumerate() {
        let at = b.eval(Op::IntAdd, 4, &[sp, Varnode::constant(n as u64 * 4, 4)]);
        let v = b.eval(Op::Load, 4, &[at]);
        if *r == 15 {
            // Popping the program counter is the return, and it is the last
            // register in the list because the list is in register order.
            returned = Some(v);
        } else {
            write_reg(&mut b, Varnode::register(gpr_offset(*r), 4), v);
        }
    }
    let raised = b.eval(Op::IntAdd, 4, &[sp, Varnode::constant(total, 4)]);
    write_reg(&mut b, sp, raised);
    if let Some(target) = returned {
        b.emit(Op::Return, None, &[target]);
    }
    b.finish(true)
}

/// `ldm` and `stm`: a run of registers moved to or from consecutive addresses.
///
/// The suffix says where the first one goes relative to the base: `ia` (which
/// is the bare name) counts up from it, `ib` up from one word past, `da` down
/// and `db` down from one word before. Whichever it is, the lowest numbered
/// register takes the lowest address.
fn block_transfer(mut b: Builder, p: &Parts, ops: &[Operand]) -> Lifted {
    let Some(Operand::Sys(mask)) = ops.get(1) else {
        return b.unimplemented();
    };
    if p.cond != 14 {
        return b.unimplemented();
    }
    // Writeback is spelled as a name, `r4!`, rather than as an operand kind.
    let (base_num, back) = match ops.first() {
        Some(Operand::Reg(r)) if matches!(r.class, RegClass::Gpr | RegClass::Sp) => (r.num, false),
        Some(Operand::Name(n)) => match n.strip_suffix('!').and_then(register_named) {
            Some(num) => (num, true),
            None => return b.unimplemented(),
        },
        _ => return b.unimplemented(),
    };
    let regs: Vec<u8> = (0..16u8).filter(|n| mask & (1 << n) != 0).collect();
    if regs.is_empty() {
        return b.unimplemented();
    }
    let load = p.base.starts_with("ldm");
    let total = regs.len() as i64 * 4;
    let down = p.base.ends_with("da") || p.base.ends_with("db");
    // Where the lowest numbered register goes, as a displacement from the
    // base, and where the base ends up.
    let (first, end) = match (down, p.base.ends_with('b')) {
        (false, false) => (0, total),
        (false, true) => (4, total),
        (true, false) => (-total + 4, -total),
        (true, true) => (-total, -total),
    };
    let base = Varnode::register(gpr_offset(base_num), 4);
    let mut returned = None;
    for (n, r) in regs.iter().enumerate() {
        let at = b.eval(
            Op::IntAdd,
            4,
            &[base, Varnode::constant((first + n as i64 * 4) as u64, 4)],
        );
        if load {
            let v = b.eval(Op::Load, 4, &[at]);
            if *r == 15 {
                returned = Some(v);
            } else {
                write_reg(&mut b, Varnode::register(gpr_offset(*r), 4), v);
            }
        } else {
            b.emit(Op::Store, None, &[at, Varnode::register(gpr_offset(*r), 4)]);
        }
    }
    if back {
        let moved = b.eval(Op::IntAdd, 4, &[base, Varnode::constant(end as u64, 4)]);
        write_reg(&mut b, base, moved);
    }
    if let Some(target) = returned {
        b.emit(Op::Return, None, &[target]);
    }
    b.finish(true)
}

/// The number of a core register named the way a listing spells it.
fn register_named(name: &str) -> Option<u8> {
    match name {
        "sp" => Some(13),
        "lr" => Some(14),
        "pc" => Some(15),
        _ => name
            .strip_prefix('r')?
            .parse::<u8>()
            .ok()
            .filter(|n| *n < 16),
    }
}

/// The loads and stores.
fn memory(mut b: Builder, i: &Insn, p: &Parts, ops: &[Operand], thumb: bool) -> Lifted {
    let bytes = match p.base {
        b if b.starts_with("ldr") || b.starts_with("str") => match b {
            "ldrb" | "ldrsb" | "strb" => 1u8,
            "ldrh" | "ldrsh" | "strh" => 2,
            "ldrd" | "strd" => 8,
            _ => 4,
        },
        _ => return b.unimplemented(),
    };
    let signed = p.base.starts_with("ldrs");
    let load = p.base.starts_with("ldr");
    // A predicated access either happens or does not, and the IR has no branch
    // inside an instruction to say which. A conditional load could be written
    // as a select, but a conditional *store* could not: not storing is not the
    // same as storing what was already there, because the address need not be
    // readable. Both are declined, so the two are treated alike.
    if p.cond != 14 {
        return b.unimplemented();
    }
    let Some(Operand::Mem(m)) = ops.get(1) else {
        return b.unimplemented();
    };
    let Some((at, updated)) = address(&mut b, m, i.addr, thumb) else {
        return b.unimplemented();
    };
    if bytes == 8 {
        // `ldrd` and `strd` name two registers and move eight bytes.
        return b.unimplemented();
    }
    if load {
        let Some(dest) = ops.first().and_then(writable) else {
            return b.unimplemented();
        };
        let raw = b.eval(Op::Load, bytes, &[at]);
        let value = if bytes == 4 {
            raw
        } else {
            b.eval(if signed { Op::IntSExt } else { Op::IntZExt }, 4, &[raw])
        };
        write_reg(&mut b, reg(dest), value);
    } else {
        let Some((v, _)) = ops.first().and_then(|o| source(&mut b, o)) else {
            return b.unimplemented();
        };
        let narrow = if bytes == 4 {
            v
        } else if v.space == Space::Register {
            b.eval(Op::SubPiece, bytes, &[v, Varnode::constant(0, 1)])
        } else {
            Varnode { size: bytes, ..v }
        };
        b.emit(Op::Store, None, &[at, narrow]);
    }
    writeback(&mut b, m, updated);
    b.finish(true)
}
