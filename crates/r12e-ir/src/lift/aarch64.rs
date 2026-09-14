//! AArch64 lifting.
//!
//! Covers the integer instructions a compiler emits: arithmetic and logical
//! forms with their flag effects, shifts, multiplies and divides, conditional
//! selects, loads and stores, and branches. Floating point and SIMD are not
//! modelled and say so rather than approximating.
//!
//! The register file is byte-addressed, so `w0` is the low four bytes of `x0`
//! and the overlap is a property of the addresses rather than of a rule. A
//! 32-bit write zeroes the upper half on this architecture, which is a real
//! effect and is emitted rather than assumed.

use r12e_arch::{AddrMode, Extend, Flow, Insn, Mem, Operand, Reg, RegClass, Shift, Width};
use r12e_core::Addr;

use crate::lift::{Builder, Lifted};
use crate::op::{Op, Space, Varnode};

/// Byte offset of `x0` in the register file.
const X_BASE: u64 = 0;
/// Byte offset of the stack pointer.
const SP: u64 = 31 * 8;
/// Byte offset of the link register.
const LR: u64 = X_BASE + 30 * 8;
/// The four condition flags, one byte each.
const N: u64 = 33 * 8;
const Z: u64 = N + 1;
const C: u64 = N + 2;
const V: u64 = N + 3;
/// Byte offset of `v0`; vector registers are sixteen bytes each.
const V_BASE: u64 = 34 * 8;

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

/// The byte offset of a general purpose register, for a caller setting up a
/// machine before running lifted code.
pub fn gpr_offset(n: u8) -> u64 {
    X_BASE + n as u64 * 8
}

/// The stack pointer's offset.
pub fn sp_offset() -> u64 {
    SP
}

/// The byte offset of a vector register; they are sixteen bytes each.
pub fn vec_offset(n: u8) -> u64 {
    V_BASE + n as u64 * 16
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

/// The varnode for a register operand.
///
/// The zero register is not storage: it reads as zero and discards writes, so
/// it becomes a constant.
fn reg(r: Reg) -> Varnode {
    let size = width_bytes(r.width);
    match r.class {
        RegClass::Gpr => Varnode::register(gpr_offset(r.num), size),
        RegClass::Sp => Varnode::register(SP, size),
        RegClass::Zr => Varnode::constant(0, size),
        RegClass::Vec => Varnode::register(V_BASE + r.num as u64 * 16, size),
        _ => Varnode::constant(0, size),
    }
}

/// The low `size` bytes of a value.
///
/// Narrowing a register varnode to one byte would name storage of its own,
/// because dataflow versions the register file in eight-byte units and keeps
/// one-byte register locations for the flags. The byte a narrowing store
/// writes has to be cut out of the register instead, so that the store depends
/// on whatever last wrote it.
fn narrow(b: &mut Builder, v: Varnode, size: u8) -> Varnode {
    if v.size <= size {
        return v;
    }
    if v.space == Space::Register && size == 1 {
        return b.eval(Op::SubPiece, 1, &[v, Varnode::constant(0, 1)]);
    }
    Varnode { size, ..v }
}

/// Write a value to a register, including the upper-half zeroing a 32-bit
/// write performs.
fn write_reg(b: &mut Builder, r: Reg, value: Varnode) {
    if r.class == RegClass::Zr {
        return;
    }
    let dest = reg(r);
    b.emit(Op::Copy, Some(dest), &[value]);
    if r.width == Width::W32 && matches!(r.class, RegClass::Gpr | RegClass::Sp) {
        // Emitting this rather than assuming it is the difference between
        // modelling the machine and modelling what the reader expected.
        let high = Varnode::register(dest.offset + 4, 4);
        b.emit(Op::Copy, Some(high), &[Varnode::constant(0, 4)]);
    }
}

/// Materialize a source operand, applying any shift or extension.
fn source(b: &mut Builder, op: &Operand, size: u8) -> Option<Varnode> {
    Some(match op {
        Operand::Reg(r) => reg(*r),
        Operand::Imm(v) => Varnode::constant(*v as u64, size),
        Operand::UImm(v) => Varnode::constant(*v, size),
        Operand::Count(v) => Varnode::constant(*v as u64, size),
        Operand::Addr(a) => Varnode::constant(a.get(), 8),
        Operand::Shifted(r, sh, amount) => {
            let v = reg(*r);
            let n = Varnode::constant(*amount as u64, 1);
            match sh {
                Shift::Lsl => b.eval(Op::IntLeft, v.size, &[v, n]),
                Shift::Lsr => b.eval(Op::IntRight, v.size, &[v, n]),
                Shift::Asr => b.eval(Op::IntSRight, v.size, &[v, n]),
                // The machine has no rotate operation and neither does the IR.
                Shift::Ror => {
                    let bits = v.size as u64 * 8;
                    let right = b.eval(Op::IntRight, v.size, &[v, n]);
                    let left_amount = Varnode::constant(bits - *amount as u64, 1);
                    let left = b.eval(Op::IntLeft, v.size, &[v, left_amount]);
                    b.eval(Op::IntOr, v.size, &[right, left])
                }
                Shift::Msl => return None,
            }
        }
        Operand::Extended(r, ext, amount) => {
            let src = reg(*r);
            let narrow_size = match ext {
                Extend::Uxtb | Extend::Sxtb => 1,
                Extend::Uxth | Extend::Sxth => 2,
                Extend::Uxtw | Extend::Sxtw => 4,
                _ => size,
            };
            let narrowed = narrow(b, src, narrow_size.min(src.size));
            let signed = matches!(
                ext,
                Extend::Sxtb | Extend::Sxth | Extend::Sxtw | Extend::Sxtx
            );
            let widened = if narrowed.size == size {
                narrowed
            } else {
                b.eval(
                    if signed { Op::IntSExt } else { Op::IntZExt },
                    size,
                    &[narrowed],
                )
            };
            if *amount == 0 {
                widened
            } else {
                b.eval(
                    Op::IntLeft,
                    size,
                    &[widened, Varnode::constant(*amount as u64, 1)],
                )
            }
        }
        _ => return None,
    })
}

/// Set the four flags from an addition or a subtraction.
fn set_flags(b: &mut Builder, size: u8, result: Varnode, x: Varnode, y: Varnode, sub: bool) {
    let zero = Varnode::constant(0, size);
    let shift = Varnode::constant(size as u64 * 8 - 1, 1);
    let sign = b.eval(Op::IntRight, size, &[result, shift]);
    let n = b.eval(Op::IntNotEqual, 1, &[sign, Varnode::constant(0, size)]);
    b.emit(Op::Copy, Some(flag_n()), &[n]);

    let z = b.eval(Op::IntEqual, 1, &[result, zero]);
    b.emit(Op::Copy, Some(flag_z()), &[z]);

    // For a subtraction the carry flag means "no borrow", which is an
    // unsigned comparison rather than a carry out.
    let c = if sub {
        b.eval(Op::IntLessEqual, 1, &[y, x])
    } else {
        b.eval(Op::IntCarry, 1, &[x, y])
    };
    b.emit(Op::Copy, Some(flag_c()), &[c]);

    let v = b.eval(if sub { Op::IntSBorrow } else { Op::IntSCarry }, 1, &[x, y]);
    b.emit(Op::Copy, Some(flag_v()), &[v]);
}

/// Set the flags a logical operation produces: N and Z from the result, with
/// C and V cleared.
fn set_logical_flags(b: &mut Builder, size: u8, result: Varnode) {
    let zero = Varnode::constant(0, size);
    let shift = Varnode::constant(size as u64 * 8 - 1, 1);
    let sign = b.eval(Op::IntRight, size, &[result, shift]);
    let n = b.eval(Op::IntNotEqual, 1, &[sign, zero]);
    b.emit(Op::Copy, Some(flag_n()), &[n]);
    let z = b.eval(Op::IntEqual, 1, &[result, zero]);
    b.emit(Op::Copy, Some(flag_z()), &[z]);
    b.emit(Op::Copy, Some(flag_c()), &[Varnode::constant(0, 1)]);
    b.emit(Op::Copy, Some(flag_v()), &[Varnode::constant(0, 1)]);
}

/// The condition a test selects on, for a lifter in another module.
pub fn condition_value(b: &mut Builder, cond: u8) -> Varnode {
    condition(b, cond)
}

/// The condition a `b.<cond>` or a conditional select tests, as one byte.
fn condition(b: &mut Builder, cond: u8) -> Varnode {
    let (n, z, c, v) = (flag_n(), flag_z(), flag_c(), flag_v());
    // The low bit inverts the test the upper three bits select.
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
    // `al` and `nv` both mean always, so the inversion does not apply to them.
    if cond & 1 == 1 && cond >> 1 != 0b111 {
        b.eval(Op::BoolNot, 1, &[base])
    } else {
        base
    }
}

/// The address a memory operand names, and how many bytes it touches.
fn address(b: &mut Builder, m: &Mem, at: Addr) -> (Varnode, u8) {
    let base = match m.base {
        Some(r) if r.class == RegClass::Pc => Varnode::constant(at.get(), 8),
        Some(r) => reg(r),
        None => Varnode::constant(0, 8),
    };
    let mut addr = base;
    if let Some((ix, ext, shift)) = m.index {
        let narrow = if matches!(ext, Extend::Uxtw | Extend::Sxtw) {
            Varnode { size: 4, ..reg(ix) }
        } else {
            reg(ix)
        };
        let signed = matches!(ext, Extend::Sxtw | Extend::Sxtx);
        let widened = if narrow.size == 8 {
            narrow
        } else {
            b.eval(if signed { Op::IntSExt } else { Op::IntZExt }, 8, &[narrow])
        };
        let scaled = if shift == 0 {
            widened
        } else {
            b.eval(
                Op::IntLeft,
                8,
                &[widened, Varnode::constant(shift as u64, 1)],
            )
        };
        addr = b.eval(Op::IntAdd, 8, &[addr, scaled]);
    }
    // A post-indexed access uses the base unmodified; the displacement is the
    // writeback rather than part of the address.
    if m.disp != 0 && m.mode != AddrMode::PostIndex {
        addr = b.eval(Op::IntAdd, 8, &[addr, Varnode::constant(m.disp as u64, 8)]);
    }
    (addr, m.size.clamp(1, 16) as u8)
}

/// Update the base register of a pre- or post-indexed access.
fn writeback(b: &mut Builder, m: &Mem) {
    if m.mode == AddrMode::Offset {
        return;
    }
    let Some(base) = m.base else { return };
    if base.class == RegClass::Pc || base.class == RegClass::Zr {
        return;
    }
    let v = reg(base);
    let updated = b.eval(Op::IntAdd, 8, &[v, Varnode::constant(m.disp as u64, 8)]);
    b.emit(Op::Copy, Some(v), &[updated]);
}

/// Say that a call left the caller-saved registers holding anything.
///
/// Without this the dataflow believes whatever they held before the call, and
/// the decompiler prints it: a value the callee overwrote, read as if it had
/// survived.
fn clobber(b: &mut Builder) {
    let abi = crate::abi::of(&r12e_core::Arch::AArch64);
    for offset in &abi.caller_saved {
        // Not the result register: the call itself defines that.
        if *offset == gpr_offset(0) {
            continue;
        }
        b.emit(Op::Undefine, Some(Varnode::register(*offset, 8)), &[]);
    }
    for flag in [flag_n(), flag_z(), flag_c(), flag_v()] {
        b.emit(Op::Undefine, Some(flag), &[]);
    }
}

/// The four-bit encoding of a condition name.
fn cond_number(name: &str) -> Option<u8> {
    const NAMES: [&str; 16] = [
        "eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al",
        "nv",
    ];
    NAMES.iter().position(|n| *n == name).map(|i| i as u8)
}

/// Lift one AArch64 instruction.
pub fn lift(i: &Insn) -> Lifted {
    let mut b = Builder::new(i.addr);
    let ops = i.operands();
    let next = Varnode::constant(i.next().get(), 8);

    // The decoder's flow classification is authoritative; the mnemonic does
    // not have to be consulted twice for control transfer.
    match i.flow {
        Flow::Branch(t) => {
            b.emit(Op::Branch, None, &[Varnode::constant(t.get(), 8)]);
            return b.finish(true);
        }
        Flow::CondBranch(t) => return cond_branch(b, i, ops, t),
        Flow::Call(t) => {
            b.emit(Op::Copy, Some(Varnode::register(LR, 8)), &[next]);
            b.emit(
                Op::Call,
                Some(Varnode::register(gpr_offset(0), 8)),
                &[Varnode::constant(t.get(), 8)],
            );
            clobber(&mut b);
            return b.finish(true);
        }
        Flow::IndirectCall => {
            let Some(Operand::Reg(r)) = ops.first() else {
                return b.unimplemented();
            };
            let target = reg(*r);
            b.emit(Op::Copy, Some(Varnode::register(LR, 8)), &[next]);
            b.emit(
                Op::CallInd,
                Some(Varnode::register(gpr_offset(0), 8)),
                &[target],
            );
            clobber(&mut b);
            return b.finish(true);
        }
        Flow::Return => {
            let link = match ops.first() {
                Some(Operand::Reg(r)) => reg(*r),
                _ => Varnode::register(LR, 8),
            };
            b.emit(Op::Return, None, &[link]);
            return b.finish(true);
        }
        Flow::IndirectBranch => {
            let Some(Operand::Reg(r)) = ops.first() else {
                return b.unimplemented();
            };
            b.emit(Op::BranchInd, None, &[reg(*r)]);
            return b.finish(true);
        }
        // A trap raises an exception and changes no register on the way; a
        // supervisor call leaves the result and the caller-saved registers to
        // the kernel, which is not knowable from here, so they are undefined
        // rather than guessed. Both flows already stop the interpreter.
        Flow::Trap => return b.finish(true),
        Flow::Syscall => {
            let abi = crate::abi::of(&r12e_core::Arch::AArch64);
            for offset in &abi.caller_saved {
                b.emit(Op::Undefine, Some(Varnode::register(*offset, 8)), &[]);
            }
            for r in &abi.results {
                b.emit(Op::Undefine, Some(Varnode::register(*r, 8)), &[]);
            }
            return b.finish(true);
        }
        Flow::Next => {}
    }

    // Anything naming a vector register goes to the SIMD lifter, where a lane
    // is just a varnode inside the register.
    if crate::lift::neon::handles(i) {
        return crate::lift::neon::lift(b, i);
    }

    let dest = match ops.first() {
        Some(Operand::Reg(r)) if r.class != RegClass::Vec => Some(*r),
        _ => None,
    };
    let size = dest.map(|d| reg(d).size).unwrap_or(8);

    match i.mnemonic {
        "nop" | "hint" | "paciasp" | "autiasp" | "pacibsp" | "autibsp" | "bti" | "dmb" | "dsb"
        | "isb" | "sb" | "clrex" | "yield" | "xpaclri" => b.finish(true),

        "mov" => {
            let (Some(d), Some(src)) = (dest, ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(v) = source(&mut b, src, size) else {
                return b.unimplemented();
            };
            write_reg(&mut b, d, v);
            b.finish(true)
        }

        "mvn" => {
            let (Some(d), Some(src)) = (dest, ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(v) = source(&mut b, src, size) else {
                return b.unimplemented();
            };
            let r = b.eval(Op::IntNot, size, &[v]);
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "neg" | "negs" => {
            let (Some(d), Some(src)) = (dest, ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(v) = source(&mut b, src, size) else {
                return b.unimplemented();
            };
            let zero = Varnode::constant(0, size);
            let r = b.eval(Op::IntSub, size, &[zero, v]);
            if i.mnemonic == "negs" {
                set_flags(&mut b, size, r, zero, v, true);
            }
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "add" | "adds" | "sub" | "subs" | "cmp" | "cmn" => {
            let sub = matches!(i.mnemonic, "sub" | "subs" | "cmp");
            let flags = matches!(i.mnemonic, "adds" | "subs" | "cmp" | "cmn");
            let discards = matches!(i.mnemonic, "cmp" | "cmn");
            let (a_op, b_op, dst) = if discards {
                (ops.first(), ops.get(1), None)
            } else {
                (ops.get(1), ops.get(2), dest)
            };
            let (Some(a_op), Some(b_op)) = (a_op, b_op) else {
                return b.unimplemented();
            };
            let size = operand_size(dst, a_op, size);
            let (Some(x), Some(y)) = (source(&mut b, a_op, size), source(&mut b, b_op, size))
            else {
                return b.unimplemented();
            };
            let r = b.eval(if sub { Op::IntSub } else { Op::IntAdd }, size, &[x, y]);
            if flags {
                set_flags(&mut b, size, r, x, y, sub);
            }
            if let Some(d) = dst {
                write_reg(&mut b, d, r);
            }
            b.finish(true)
        }

        "and" | "ands" | "orr" | "eor" | "bic" | "bics" | "orn" | "eon" | "tst" => {
            let discards = i.mnemonic == "tst";
            let (a_op, b_op, dst) = if discards {
                (ops.first(), ops.get(1), None)
            } else {
                (ops.get(1), ops.get(2), dest)
            };
            let (Some(a_op), Some(b_op)) = (a_op, b_op) else {
                return b.unimplemented();
            };
            let size = operand_size(dst, a_op, size);
            let (Some(x), Some(mut y)) = (source(&mut b, a_op, size), source(&mut b, b_op, size))
            else {
                return b.unimplemented();
            };
            if matches!(i.mnemonic, "bic" | "bics" | "orn" | "eon") {
                y = b.eval(Op::IntNot, size, &[y]);
            }
            let op = match i.mnemonic {
                "and" | "ands" | "bic" | "bics" | "tst" => Op::IntAnd,
                "orr" | "orn" => Op::IntOr,
                _ => Op::IntXor,
            };
            let r = b.eval(op, size, &[x, y]);
            if matches!(i.mnemonic, "ands" | "bics" | "tst") {
                set_logical_flags(&mut b, size, r);
            }
            if let Some(d) = dst {
                write_reg(&mut b, d, r);
            }
            b.finish(true)
        }

        "lsl" | "lsr" | "asr" | "ror" => {
            let (Some(d), Some(a), Some(c)) = (dest, ops.get(1), ops.get(2)) else {
                return b.unimplemented();
            };
            let (Some(x), Some(mut amount)) = (source(&mut b, a, size), source(&mut b, c, size))
            else {
                return b.unimplemented();
            };
            // A variable shift uses only the low bits of the count.
            if !amount.is_const() {
                let mask = Varnode::constant(size as u64 * 8 - 1, size);
                amount = b.eval(Op::IntAnd, size, &[amount, mask]);
            }
            let r = match i.mnemonic {
                "lsl" => b.eval(Op::IntLeft, size, &[x, amount]),
                "lsr" => b.eval(Op::IntRight, size, &[x, amount]),
                "asr" => b.eval(Op::IntSRight, size, &[x, amount]),
                _ => {
                    let bits = Varnode::constant(size as u64 * 8, size);
                    let right = b.eval(Op::IntRight, size, &[x, amount]);
                    let inv = b.eval(Op::IntSub, size, &[bits, amount]);
                    let left = b.eval(Op::IntLeft, size, &[x, inv]);
                    b.eval(Op::IntOr, size, &[right, left])
                }
            };
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "mul" | "madd" | "msub" | "mneg" => {
            let (Some(d), Some(a), Some(c)) = (dest, ops.get(1), ops.get(2)) else {
                return b.unimplemented();
            };
            let (Some(x), Some(y)) = (source(&mut b, a, size), source(&mut b, c, size)) else {
                return b.unimplemented();
            };
            let product = b.eval(Op::IntMul, size, &[x, y]);
            let r = match (i.mnemonic, ops.get(3)) {
                ("madd", Some(acc)) => {
                    let Some(a) = source(&mut b, acc, size) else {
                        return b.unimplemented();
                    };
                    b.eval(Op::IntAdd, size, &[a, product])
                }
                ("msub", Some(acc)) => {
                    let Some(a) = source(&mut b, acc, size) else {
                        return b.unimplemented();
                    };
                    b.eval(Op::IntSub, size, &[a, product])
                }
                ("mneg", _) => {
                    let zero = Varnode::constant(0, size);
                    b.eval(Op::IntSub, size, &[zero, product])
                }
                _ => product,
            };
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "smull" | "umull" => {
            let (Some(d), Some(a), Some(c)) = (dest, ops.get(1), ops.get(2)) else {
                return b.unimplemented();
            };
            let (Some(x), Some(y)) = (source(&mut b, a, 4), source(&mut b, c, 4)) else {
                return b.unimplemented();
            };
            let signed = i.mnemonic.starts_with('s');
            let ext = if signed { Op::IntSExt } else { Op::IntZExt };
            let wx = b.eval(ext, 8, &[x]);
            let wy = b.eval(ext, 8, &[y]);
            let r = b.eval(Op::IntMul, 8, &[wx, wy]);
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        // The architecture defines division by zero as producing zero rather
        // than trapping, so the IR says so instead of letting the interpreter
        // stop.
        "udiv" | "sdiv" => {
            let (Some(d), Some(a), Some(c)) = (dest, ops.get(1), ops.get(2)) else {
                return b.unimplemented();
            };
            let (Some(x), Some(y)) = (source(&mut b, a, size), source(&mut b, c, size)) else {
                return b.unimplemented();
            };
            let zero = Varnode::constant(0, size);
            let one = Varnode::constant(1, size);
            let is_zero = b.eval(Op::IntEqual, 1, &[y, zero]);
            // Divide by one when the divisor is zero, then mask the result
            // away. Straight-line, so dataflow sees one definition.
            let zx = b.eval(Op::IntZExt, size, &[is_zero]);
            let denom = b.eval(Op::IntOr, size, &[y, zx]);
            let q = b.eval(
                if i.mnemonic == "udiv" {
                    Op::IntDiv
                } else {
                    Op::IntSDiv
                },
                size,
                &[x, denom],
            );
            let keep = b.eval(Op::IntSub, size, &[zx, one]);
            let r = b.eval(Op::IntAnd, size, &[q, keep]);
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "csel" | "csinc" | "csinv" | "csneg" | "cset" | "csetm" | "cinc" | "cinv" | "cneg" => {
            conditional_select(b, i, ops, size)
        }

        "sxtb" | "sxth" | "sxtw" | "uxtb" | "uxth" => {
            let (Some(d), Some(Operand::Reg(s))) = (dest, ops.get(1)) else {
                return b.unimplemented();
            };
            let narrow_size = match i.mnemonic {
                "sxtb" | "uxtb" => 1,
                "sxth" | "uxth" => 2,
                _ => 4,
            };
            let narrowed = narrow(&mut b, reg(*s), narrow_size);
            let signed = i.mnemonic.starts_with('s');
            let r = b.eval(
                if signed { Op::IntSExt } else { Op::IntZExt },
                size,
                &[narrowed],
            );
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "adr" | "adrp" => {
            let (Some(d), Some(Operand::Addr(a))) = (dest, ops.get(1)) else {
                return b.unimplemented();
            };
            write_reg(&mut b, d, Varnode::constant(a.get(), 8));
            b.finish(true)
        }

        "ubfx" | "sbfx" => {
            let (Some(d), Some(a), Some(Operand::Count(lsb)), Some(Operand::Count(width))) =
                (dest, ops.get(1), ops.get(2), ops.get(3))
            else {
                return b.unimplemented();
            };
            let Some(x) = source(&mut b, a, size) else {
                return b.unimplemented();
            };
            let shifted = b.eval(Op::IntRight, size, &[x, Varnode::constant(*lsb as u64, 1)]);
            let mask = if *width >= size as i64 * 8 {
                u64::MAX
            } else {
                (1u64 << *width) - 1
            };
            let r = b.eval(Op::IntAnd, size, &[shifted, Varnode::constant(mask, size)]);
            let r = if i.mnemonic == "sbfx" {
                // Sign-extend from the extracted width by shifting up and back.
                let up = size as u64 * 8 - *width as u64;
                let left = b.eval(Op::IntLeft, size, &[r, Varnode::constant(up, 1)]);
                b.eval(Op::IntSRight, size, &[left, Varnode::constant(up, 1)])
            } else {
                r
            };
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "ldr" | "ldrb" | "ldrh" | "ldrsb" | "ldrsh" | "ldrsw" | "ldur" | "ldurb" | "ldurh"
        | "ldursb" | "ldursh" | "ldursw" => load(b, i, ops),

        "str" | "strb" | "strh" | "stur" | "sturb" | "sturh" => store(b, i, ops),

        "ldp" | "stp" | "ldpsw" | "ldnp" | "stnp" => pair(b, i, ops),

        // A prefetch has no architectural effect beyond timing.
        "prfm" | "prfum" => b.finish(true),

        "movk" => {
            let Some(d) = dest else {
                return b.unimplemented();
            };
            let v = match ops.get(1) {
                Some(Operand::UImm(v)) => *v,
                Some(Operand::Imm(v)) if *v >= 0 => *v as u64,
                _ => return b.unimplemented(),
            };
            let shift = match ops.get(2) {
                Some(Operand::ShiftOp(_, n)) => *n as u64,
                _ => 0,
            };
            // Keep the other halfwords and replace this one.
            let keep = !(0xffffu64 << shift);
            let old = reg(d);
            let masked = b.eval(Op::IntAnd, size, &[old, Varnode::constant(keep, size)]);
            let inserted = b.eval(
                Op::IntOr,
                size,
                &[masked, Varnode::constant(v << shift, size)],
            );
            write_reg(&mut b, d, inserted);
            b.finish(true)
        }

        "sbfiz" | "ubfiz" | "bfi" | "bfxil" => bitfield(b, i, ops, size),

        "ccmp" | "ccmn" => {
            // A conditional compare either performs the comparison or writes
            // the flags the instruction carries. Both sides are computed and
            // selected, so the IR stays straight-line.
            let (Some(a), Some(second), Some(Operand::Imm(nzcv)), Some(Operand::Cond(c))) =
                (ops.first(), ops.get(1), ops.get(2), ops.get(3))
            else {
                return b.unimplemented();
            };
            let size = match a {
                Operand::Reg(r) => reg(*r).size,
                _ => size,
            };
            let (Some(x), Some(y)) = (source(&mut b, a, size), source(&mut b, second, size)) else {
                return b.unimplemented();
            };
            let taken = condition(&mut b, c.0);
            let sub = i.mnemonic == "ccmp";
            let r = b.eval(if sub { Op::IntSub } else { Op::IntAdd }, size, &[x, y]);
            set_flags(&mut b, size, r, x, y, sub);
            // When the condition failed, the carried flags win instead.
            let not_taken = b.eval(Op::BoolNot, 1, &[taken]);
            let flags = *nzcv as u64;
            for (n, f) in [flag_n(), flag_z(), flag_c(), flag_v()]
                .into_iter()
                .enumerate()
            {
                let bit = (flags >> (3 - n)) & 1;
                let carried = Varnode::constant(bit, 1);
                let keep = b.eval(Op::IntAnd, 1, &[f, taken]);
                let replace = b.eval(Op::IntAnd, 1, &[carried, not_taken]);
                let merged = b.eval(Op::IntOr, 1, &[keep, replace]);
                b.emit(Op::Copy, Some(f), &[merged]);
            }
            b.finish(true)
        }

        "adc" | "adcs" | "sbc" | "sbcs" => {
            let (Some(d), Some(a), Some(c)) = (dest, ops.get(1), ops.get(2)) else {
                return b.unimplemented();
            };
            let (Some(x), Some(y)) = (source(&mut b, a, size), source(&mut b, c, size)) else {
                return b.unimplemented();
            };
            let carry = b.eval(Op::IntZExt, size, &[flag_c()]);
            let sub = i.mnemonic.starts_with("sbc");
            let r = if sub {
                // With borrow: x - y - 1 + carry.
                let d1 = b.eval(Op::IntSub, size, &[x, y]);
                let d2 = b.eval(Op::IntAdd, size, &[d1, carry]);
                b.eval(Op::IntSub, size, &[d2, Varnode::constant(1, size)])
            } else {
                let s1 = b.eval(Op::IntAdd, size, &[x, y]);
                b.eval(Op::IntAdd, size, &[s1, carry])
            };
            if i.mnemonic.ends_with('s') {
                set_flags(&mut b, size, r, x, y, sub);
            }
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "smulh" | "umulh" => {
            let (Some(d), Some(x), Some(y)) = (dest, ops.get(1), ops.get(2)) else {
                return b.unimplemented();
            };
            let (Some(a), Some(c)) = (source(&mut b, x, 8), source(&mut b, y, 8)) else {
                return b.unimplemented();
            };
            let op = if i.mnemonic == "smulh" {
                Op::IntSMulHigh
            } else {
                Op::IntMulHigh
            };
            let r = b.eval(op, 8, &[a, c]);
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        // The widening multiply-accumulates: two 32-bit sources, a 64-bit
        // accumulator, and a product that needs the full width.
        "umaddl" | "smaddl" | "umsubl" | "smsubl" | "umnegl" | "smnegl" => {
            let (Some(d), Some(Operand::Reg(x)), Some(Operand::Reg(y))) =
                (dest, ops.get(1), ops.get(2))
            else {
                return b.unimplemented();
            };
            let signed = i.mnemonic.starts_with('s');
            let ext = if signed { Op::IntSExt } else { Op::IntZExt };
            let a = b.eval(ext, 8, &[Varnode { size: 4, ..reg(*x) }]);
            let c = b.eval(ext, 8, &[Varnode { size: 4, ..reg(*y) }]);
            let product = b.eval(Op::IntMul, 8, &[a, c]);
            let r = match ops.get(3) {
                Some(acc) => {
                    let Some(base) = source(&mut b, acc, 8) else {
                        return b.unimplemented();
                    };
                    let op = if i.mnemonic.ends_with("subl") {
                        Op::IntSub
                    } else {
                        Op::IntAdd
                    };
                    b.eval(op, 8, &[base, product])
                }
                // The negating forms have no accumulator.
                None if i.mnemonic.ends_with("negl") => b.eval(Op::IntNegate, 8, &[product]),
                None => product,
            };
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        "clz" | "rbit" | "rev" | "rev16" | "rev32" | "cls" => {
            let (Some(d), Some(Operand::Reg(s))) = (dest, ops.get(1)) else {
                return b.unimplemented();
            };
            let x = reg(*s);
            match i.mnemonic {
                "clz" => {
                    let r = b.eval(Op::LzCount, size, &[x]);
                    write_reg(&mut b, d, r);
                    b.finish(true)
                }
                // The byte reversals and the bit reversal have no single IR
                // operation and are not approximated.
                _ => b.unimplemented(),
            }
        }

        "extr" | "ror_extr" => {
            let (Some(d), Some(a), Some(c), Some(Operand::Count(lsb))) =
                (dest, ops.get(1), ops.get(2), ops.get(3))
            else {
                return b.unimplemented();
            };
            let (Some(hi), Some(lo)) = (source(&mut b, a, size), source(&mut b, c, size)) else {
                return b.unimplemented();
            };
            let bits = size as u64 * 8;
            let right = b.eval(Op::IntRight, size, &[lo, Varnode::constant(*lsb as u64, 1)]);
            let r = if *lsb as u64 == 0 {
                right
            } else {
                let left = b.eval(
                    Op::IntLeft,
                    size,
                    &[hi, Varnode::constant(bits - *lsb as u64, 1)],
                );
                b.eval(Op::IntOr, size, &[right, left])
            };
            write_reg(&mut b, d, r);
            b.finish(true)
        }

        _ => b.unimplemented(),
    }
}

/// The insert and extract bitfield forms.
fn bitfield(mut b: Builder, i: &Insn, ops: &[Operand], size: u8) -> Lifted {
    let (Some(Operand::Reg(d)), Some(src), Some(Operand::Count(a)), Some(Operand::Count(width))) =
        (ops.first(), ops.get(1), ops.get(2), ops.get(3))
    else {
        return b.unimplemented();
    };
    let Some(x) = source(&mut b, src, size) else {
        return b.unimplemented();
    };
    let bits = size as u64 * 8;
    let w = (*width as u64).min(bits);
    let field_mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };

    match i.mnemonic {
        // Take the low `width` bits and place them at `lsb`, zeroing the rest.
        "sbfiz" | "ubfiz" => {
            let lsb = *a as u64;
            let masked = b.eval(Op::IntAnd, size, &[x, Varnode::constant(field_mask, size)]);
            let placed = b.eval(Op::IntLeft, size, &[masked, Varnode::constant(lsb, 1)]);
            let r = if i.mnemonic == "sbfiz" {
                // Sign-extend from the top of the placed field.
                let up = bits.saturating_sub(lsb + w);
                let left = b.eval(Op::IntLeft, size, &[placed, Varnode::constant(up, 1)]);
                b.eval(Op::IntSRight, size, &[left, Varnode::constant(up, 1)])
            } else {
                placed
            };
            write_reg(&mut b, *d, r);
            b.finish(true)
        }
        // Place the field into the destination, leaving the other bits alone.
        "bfi" => {
            let lsb = *a as u64;
            let masked = b.eval(Op::IntAnd, size, &[x, Varnode::constant(field_mask, size)]);
            let placed = b.eval(Op::IntLeft, size, &[masked, Varnode::constant(lsb, 1)]);
            let hole = Varnode::constant(!(field_mask << lsb), size);
            let old = reg(*d);
            let cleared = b.eval(Op::IntAnd, size, &[old, hole]);
            let r = b.eval(Op::IntOr, size, &[cleared, placed]);
            write_reg(&mut b, *d, r);
            b.finish(true)
        }
        // Take a field from the source's low bits into the destination's.
        "bfxil" => {
            let lsb = *a as u64;
            let shifted = b.eval(Op::IntRight, size, &[x, Varnode::constant(lsb, 1)]);
            let masked = b.eval(
                Op::IntAnd,
                size,
                &[shifted, Varnode::constant(field_mask, size)],
            );
            let old = reg(*d);
            let cleared = b.eval(
                Op::IntAnd,
                size,
                &[old, Varnode::constant(!field_mask, size)],
            );
            let r = b.eval(Op::IntOr, size, &[cleared, masked]);
            write_reg(&mut b, *d, r);
            b.finish(true)
        }
        _ => b.unimplemented(),
    }
}

/// The operand size, taken from the destination when there is one and from the
/// first source when the result is discarded.
fn operand_size(dst: Option<Reg>, a: &Operand, fallback: u8) -> u8 {
    match (dst, a) {
        (Some(d), _) => reg(d).size,
        (None, Operand::Reg(r)) => reg(*r).size,
        _ => fallback,
    }
}

fn cond_branch(mut b: Builder, i: &Insn, ops: &[Operand], target: Addr) -> Lifted {
    let cond = match i.mnemonic {
        m if m.starts_with("b.") => {
            let Some(c) = cond_number(&m[2..]) else {
                return b.unimplemented();
            };
            condition(&mut b, c)
        }
        "cbz" | "cbnz" => {
            let Some(Operand::Reg(r)) = ops.first() else {
                return b.unimplemented();
            };
            let v = reg(*r);
            let zero = Varnode::constant(0, v.size);
            let op = if i.mnemonic == "cbz" {
                Op::IntEqual
            } else {
                Op::IntNotEqual
            };
            b.eval(op, 1, &[v, zero])
        }
        "tbz" | "tbnz" => {
            let (Some(Operand::Reg(r)), Some(Operand::Count(bit))) = (ops.first(), ops.get(1))
            else {
                return b.unimplemented();
            };
            let v = reg(*r);
            let shifted = b.eval(
                Op::IntRight,
                v.size,
                &[v, Varnode::constant(*bit as u64, 1)],
            );
            let masked = b.eval(Op::IntAnd, v.size, &[shifted, Varnode::constant(1, v.size)]);
            let zero = Varnode::constant(0, v.size);
            let op = if i.mnemonic == "tbz" {
                Op::IntEqual
            } else {
                Op::IntNotEqual
            };
            b.eval(op, 1, &[masked, zero])
        }
        _ => return b.unimplemented(),
    };
    b.emit(
        Op::CBranch,
        None,
        &[Varnode::constant(target.get(), 8), cond],
    );
    b.finish(true)
}

/// A conditional select, lifted without a branch: both values are masked and
/// combined, so the IR stays straight-line and dataflow sees one definition.
fn conditional_select(mut b: Builder, i: &Insn, ops: &[Operand], size: u8) -> Lifted {
    let Some(Operand::Reg(d)) = ops.first() else {
        return b.unimplemented();
    };
    let Some(cond_num) = ops.iter().rev().find_map(|o| match o {
        Operand::Cond(c) => Some(c.0),
        _ => None,
    }) else {
        return b.unimplemented();
    };
    let taken = condition(&mut b, cond_num);

    // The three-operand forms select the plain value when the condition holds
    // and the transformed one when it does not. The two-operand aliases are
    // the other way round: `cneg Rd, Rn, lt` negates *when* it is less than,
    // because the alias hides an inverted condition. Getting this backwards
    // turns an absolute value into a negation, which is what it did.
    let alias = matches!(i.mnemonic, "cinc" | "cinv" | "cneg");
    let (plain, to_transform) = match i.mnemonic {
        "cset" | "csetm" => (
            Varnode::constant(0, size),
            Varnode::constant(if i.mnemonic == "cset" { 1 } else { u64::MAX }, size),
        ),
        _ if alias => {
            let Some(src) = ops.get(1).and_then(|o| source(&mut b, o, size)) else {
                return b.unimplemented();
            };
            (src, src)
        }
        _ => {
            let (Some(x), Some(y)) = (
                ops.get(1).and_then(|o| source(&mut b, o, size)),
                ops.get(2).and_then(|o| source(&mut b, o, size)),
            ) else {
                return b.unimplemented();
            };
            (x, y)
        }
    };

    let transformed = match i.mnemonic {
        "csinc" | "cinc" => b.eval(
            Op::IntAdd,
            size,
            &[to_transform, Varnode::constant(1, size)],
        ),
        "csinv" | "cinv" => b.eval(Op::IntNot, size, &[to_transform]),
        "csneg" | "cneg" => {
            let zero = Varnode::constant(0, size);
            b.eval(Op::IntSub, size, &[zero, to_transform])
        }
        // cset and csetm need no transform: the constant is already the value.
        "cset" | "csetm" => to_transform,
        _ => to_transform,
    };

    // Which side the condition picks.
    let (yes, otherwise) = if alias || matches!(i.mnemonic, "cset" | "csetm") {
        (transformed, plain)
    } else {
        (plain, transformed)
    };

    let zero = Varnode::constant(0, size);
    let t = b.eval(Op::IntZExt, size, &[taken]);
    let mask = b.eval(Op::IntSub, size, &[zero, t]);
    let inv = b.eval(Op::IntNot, size, &[mask]);
    let a = b.eval(Op::IntAnd, size, &[yes, mask]);
    let c = b.eval(Op::IntAnd, size, &[otherwise, inv]);
    let r = b.eval(Op::IntOr, size, &[a, c]);
    write_reg(&mut b, *d, r);
    b.finish(true)
}

fn load(mut b: Builder, i: &Insn, ops: &[Operand]) -> Lifted {
    let (Some(Operand::Reg(d)), Some(second)) = (ops.first(), ops.get(1)) else {
        return b.unimplemented();
    };
    // A value wider than the IR carries is moved in eight-byte pieces rather
    // than truncated.
    if d.class == RegClass::Vec && width_bytes(d.width) > 8 {
        let addr = match second {
            Operand::Addr(a) => Varnode::constant(a.get(), 8),
            Operand::Mem(m) => address(&mut b, m, i.addr).0,
            _ => return b.unimplemented(),
        };
        crate::lift::neon::wide_transfer(&mut b, addr, d.num, 16, false);
        if let Operand::Mem(m) = second {
            writeback(&mut b, m);
        }
        return b.finish(true);
    }
    let out_size = reg(*d).size;
    let (addr, access) = match second {
        Operand::Addr(a) => (Varnode::constant(a.get(), 8), out_size),
        Operand::Mem(m) => address(&mut b, m, i.addr),
        _ => return b.unimplemented(),
    };
    let loaded = b.temp(access);
    b.emit(Op::Load, Some(loaded), &[addr]);
    let signed = matches!(
        i.mnemonic,
        "ldrsb" | "ldrsh" | "ldrsw" | "ldursb" | "ldursh" | "ldursw"
    );
    let value = if access == out_size {
        loaded
    } else {
        b.eval(
            if signed { Op::IntSExt } else { Op::IntZExt },
            out_size,
            &[loaded],
        )
    };
    write_reg(&mut b, *d, value);
    if let Operand::Mem(m) = second {
        writeback(&mut b, m);
    }
    b.finish(true)
}

fn store(mut b: Builder, i: &Insn, ops: &[Operand]) -> Lifted {
    let (Some(Operand::Reg(s)), Some(Operand::Mem(m))) = (ops.first(), ops.get(1)) else {
        return b.unimplemented();
    };
    if s.class == RegClass::Vec && width_bytes(s.width) > 8 {
        let (addr, _) = address(&mut b, m, i.addr);
        crate::lift::neon::wide_transfer(&mut b, addr, s.num, 16, true);
        writeback(&mut b, m);
        return b.finish(true);
    }
    let (addr, access) = address(&mut b, m, i.addr);
    let src = reg(*s);
    // A narrowing store writes the low bytes of the register.
    let value = narrow(&mut b, src, access.min(src.size));
    b.emit(Op::Store, None, &[addr, value]);
    writeback(&mut b, m);
    b.finish(true)
}

fn pair(mut b: Builder, i: &Insn, ops: &[Operand]) -> Lifted {
    let (Some(Operand::Reg(a)), Some(Operand::Reg(c)), Some(Operand::Mem(m))) =
        (ops.first(), ops.get(1), ops.get(2))
    else {
        return b.unimplemented();
    };
    if width_bytes(a.width) > 8 || width_bytes(c.width) > 8 {
        // A pair of vector registers, moved in eight-byte pieces.
        if a.class != RegClass::Vec || c.class != RegClass::Vec {
            return b.unimplemented();
        }
        let (addr, _) = address(&mut b, m, i.addr);
        let storing = i.mnemonic.starts_with('s');
        crate::lift::neon::wide_transfer(&mut b, addr, a.num, 16, storing);
        let second = b.eval(Op::IntAdd, 8, &[addr, Varnode::constant(16, 8)]);
        crate::lift::neon::wide_transfer(&mut b, second, c.num, 16, storing);
        writeback(&mut b, m);
        return b.finish(true);
    }
    let (addr, total) = address(&mut b, m, i.addr);
    let each = (total / 2).max(1);
    let second = b.eval(Op::IntAdd, 8, &[addr, Varnode::constant(each as u64, 8)]);
    // Every loading form starts with `ld`: `ldpsw` and `ldnp` are loads too,
    // and treating them as stores would write memory the program only reads.
    if i.mnemonic.starts_with("ld") {
        // `ldpsw` loads two words and sign-extends each to a doubleword.
        let widen = i.mnemonic == "ldpsw";
        for (slot, at) in [(*a, addr), (*c, second)] {
            let loaded = b.temp(each);
            b.emit(Op::Load, Some(loaded), &[at]);
            let value = if widen {
                b.eval(Op::IntSExt, 8, &[loaded])
            } else {
                loaded
            };
            write_reg(&mut b, slot, value);
        }
    } else {
        b.emit(Op::Store, None, &[addr, reg(*a)]);
        b.emit(Op::Store, None, &[second, reg(*c)]);
    }
    writeback(&mut b, m);
    b.finish(true)
}
