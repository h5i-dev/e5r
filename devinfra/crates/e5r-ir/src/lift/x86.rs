//! x86-64 lifting.
//!
//! Covers the integer instruction set a compiler emits, with every flag the
//! instruction actually writes. The flags are the point: x86 code branches on
//! them constantly, and a lifter that sets only zero and sign turns a correct
//! comparison into a wrong one several instructions later.
//!
//! Two things the architecture does that need saying explicitly. A write to a
//! 32-bit register clears the upper half, and a write to an 8- or 16-bit one
//! does not, which the byte-addressed register file expresses directly. And a
//! shift by zero leaves the flags untouched rather than recomputing them, so
//! the flag updates are selected on the count rather than assumed.

use e5r_arch::{Extend, Flow, Insn, Mem, Operand, Reg, RegClass, Width};
use e5r_core::Addr;

use crate::lift::{Builder, Lifted};
use crate::op::{Op, Space, Varnode};

/// Byte offset of `rax`; the sixteen general registers are eight bytes each.
const R_BASE: u64 = 0;
/// `rsp`, which is register 4.
const RSP: u64 = 4 * 8;
/// The instruction pointer.
const RIP: u64 = 16 * 8;
/// The flags, one byte each.
const CF: u64 = 17 * 8;
const PF: u64 = CF + 1;
const AF: u64 = CF + 2;
const ZF: u64 = CF + 3;
const SF: u64 = CF + 4;
const OF: u64 = CF + 5;
const DF: u64 = CF + 6;
/// Byte offset of `xmm0`; vector registers are sixteen bytes each.
const XMM_BASE: u64 = 18 * 8;

/// The byte offset of a vector register; they are sixteen bytes each.
pub fn vec_offset(n: u8) -> u64 {
    XMM_BASE + n as u64 * 16
}

/// The byte offset of a general purpose register, in encoding order: `rax`,
/// `rcx`, `rdx`, `rbx`, `rsp`, `rbp`, `rsi`, `rdi`, then `r8` upwards.
pub fn gpr_offset(n: u8) -> u64 {
    R_BASE + n as u64 * 8
}

/// The stack pointer's offset.
pub fn sp_offset() -> u64 {
    RSP
}

/// The instruction pointer's offset.
pub fn pc_offset() -> u64 {
    RIP
}

/// The carry flag.
pub fn flag_cf() -> Varnode {
    Varnode::register(CF, 1)
}
/// The zero flag.
pub fn flag_zf() -> Varnode {
    Varnode::register(ZF, 1)
}
/// The sign flag.
pub fn flag_sf() -> Varnode {
    Varnode::register(SF, 1)
}
/// The overflow flag.
pub fn flag_of() -> Varnode {
    Varnode::register(OF, 1)
}
/// The parity flag.
pub fn flag_pf() -> Varnode {
    Varnode::register(PF, 1)
}
/// The adjust flag.
pub fn flag_af() -> Varnode {
    Varnode::register(AF, 1)
}
/// The direction flag.
pub fn flag_df() -> Varnode {
    Varnode::register(DF, 1)
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

/// The varnode a register operand names.
///
/// `ah` is byte one of `rax` rather than a register of its own, which the byte
/// addressing says without a special case anywhere else.
fn reg(r: Reg) -> Option<Varnode> {
    let size = width_bytes(r.width);
    Some(match r.class {
        RegClass::Gpr => Varnode::register(gpr_offset(r.num), size),
        RegClass::GprHigh => Varnode::register(gpr_offset(r.num & 3) + 1, 1),
        RegClass::Vec => Varnode::register(XMM_BASE + r.num as u64 * 16, size.max(16)),
        RegClass::Pc => return None,
        _ => return None,
    })
}

/// The whole register a one-byte operand sits in, and which byte of it that is.
///
/// Dataflow versions the register file in eight-byte units and keeps one-byte
/// register locations for the flags, which sit above the registers. A varnode
/// naming `al` on its own is therefore storage no write to `rax` ever reaches:
/// the read misses its definition and the write is dead.
fn byte_slot(v: Varnode) -> Option<(Varnode, u64)> {
    (v.space == Space::Register && v.size == 1 && v.offset < CF)
        .then(|| (Varnode::register(v.offset & !7, 8), v.offset % 8))
}

/// Read a varnode, cutting a byte operand out of the register that holds it.
fn read(b: &mut Builder, v: Varnode) -> Varnode {
    match byte_slot(v) {
        Some((whole, index)) => b.eval(Op::SubPiece, 1, &[whole, Varnode::constant(index, 1)]),
        None => v,
    }
}

/// Write a varnode, merging a byte operand back into the register that holds
/// it. The merge is what keeps the other seven bytes alive, which is the
/// machine's behaviour: a write to `al` leaves the rest of `rax` untouched.
fn write(b: &mut Builder, dest: Varnode, value: Varnode) {
    let Some((whole, index)) = byte_slot(dest) else {
        b.emit(Op::Copy, Some(dest), &[value]);
        return;
    };
    let byte = if value.size == 1 {
        value
    } else {
        b.eval(Op::SubPiece, 1, &[value, Varnode::constant(0, 1)])
    };
    let shift = index * 8;
    let kept = b.eval(
        Op::IntAnd,
        8,
        &[whole, Varnode::constant(!(0xffu64 << shift), 8)],
    );
    let wide = b.eval(Op::IntZExt, 8, &[byte]);
    let placed = if shift == 0 {
        wide
    } else {
        b.eval(Op::IntLeft, 8, &[wide, Varnode::constant(shift, 1)])
    };
    b.emit(Op::IntOr, Some(whole), &[kept, placed]);
}

/// Write a register, including the upper-half clear a 32-bit write performs.
fn write_reg(b: &mut Builder, r: Reg, value: Varnode) {
    let Some(dest) = reg(r) else { return };
    write(b, dest, value);
    if r.width == Width::W32 && r.class == RegClass::Gpr {
        b.emit(
            Op::Copy,
            Some(Varnode::register(dest.offset + 4, 4)),
            &[Varnode::constant(0, 4)],
        );
    }
}

/// The address a memory operand names.
///
/// Returns `None` for a thread-local access through `fs` or `gs`, whose base is
/// not in the register file and cannot be invented.
pub(crate) fn address(b: &mut Builder, m: &Mem, at: Addr) -> Option<Varnode> {
    if let Some(s) = m.seg {
        // `fs` and `gs` are numbers 4 and 5 in the segment bank.
        if matches!(s.num, 4 | 5) {
            return None;
        }
    }
    let p = b.ptr;
    let mut addr = match m.base {
        Some(r) if r.class == RegClass::Pc => Varnode::constant(at.get(), p),
        Some(r) => Varnode { size: p, ..reg(r)? },
        None => Varnode::constant(0, p),
    };
    if let Some((ix, ext, scale)) = m.index {
        let base = reg(ix)?;
        let narrow = if matches!(ext, Extend::Uxtw | Extend::Sxtw) {
            Varnode { size: 4, ..base }
        } else {
            Varnode { size: p, ..base }
        };
        let widened = if narrow.size == p {
            narrow
        } else {
            let signed = matches!(ext, Extend::Sxtw);
            b.eval(if signed { Op::IntSExt } else { Op::IntZExt }, p, &[narrow])
        };
        let scaled = if scale == 0 {
            widened
        } else {
            b.eval(
                Op::IntLeft,
                p,
                &[widened, Varnode::constant(scale as u64, 1)],
            )
        };
        addr = if m.base.is_none() {
            scaled
        } else {
            b.eval(Op::IntAdd, p, &[addr, scaled])
        };
    }
    if m.disp != 0 {
        addr = b.eval(Op::IntAdd, p, &[addr, Varnode::constant(m.disp as u64, p)]);
    }
    Some(addr)
}

/// Read an operand, loading from memory when it names memory.
fn source(b: &mut Builder, op: &Operand, size: u8, at: Addr) -> Option<Varnode> {
    Some(match op {
        Operand::Reg(r) => read(b, reg(*r)?),
        Operand::Imm(v) => Varnode::constant(*v as u64, size),
        Operand::UImm(v) => Varnode::constant(*v, size),
        Operand::Count(v) => Varnode::constant(*v as u64, size),
        Operand::Addr(a) => Varnode::constant(a.get(), b.ptr),
        Operand::Mem(m) => {
            let addr = address(b, m, at)?;
            let bytes = if m.size == 0 {
                size
            } else {
                m.size.clamp(1, 16) as u8
            };
            b.eval(Op::Load, bytes, &[addr])
        }
        _ => return None,
    })
}

/// Write a value to whatever an operand names.
fn store(b: &mut Builder, op: &Operand, value: Varnode, at: Addr) -> Option<()> {
    match op {
        Operand::Reg(r) => write_reg(b, *r, value),
        Operand::Mem(m) => {
            let addr = address(b, m, at)?;
            b.emit(Op::Store, None, &[addr, value]);
        }
        _ => return None,
    }
    Some(())
}

/// The size an instruction operates at, taken from its destination.
fn operand_size(ops: &[Operand]) -> Option<u8> {
    for op in ops {
        match op {
            Operand::Reg(r) => return Some(width_bytes(r.width)),
            Operand::Mem(m) if m.size > 0 => return Some(m.size.clamp(1, 16) as u8),
            _ => {}
        }
    }
    None
}

/// Choose between two values without a branch: `cond ? t : f`.
///
/// Used wherever the machine makes an update conditional, which is a shift by
/// a variable count leaving the flags alone, and `cmov`.
fn select(b: &mut Builder, cond: Varnode, t: Varnode, f: Varnode, size: u8) -> Varnode {
    let wide = if size == 1 {
        cond
    } else {
        b.eval(Op::IntZExt, size, &[cond])
    };
    // Negating a zero-or-one gives all zeroes or all ones, which is the mask.
    let mask = b.eval(Op::IntNegate, size, &[wide]);
    let keep = b.eval(Op::IntAnd, size, &[t, mask]);
    let inverse = b.eval(Op::IntNot, size, &[mask]);
    let drop = b.eval(Op::IntAnd, size, &[f, inverse]);
    b.eval(Op::IntOr, size, &[keep, drop])
}

/// The sign bit of a value, as one byte.
fn sign_of(b: &mut Builder, v: Varnode) -> Varnode {
    let shift = Varnode::constant(v.size as u64 * 8 - 1, 1);
    let high = b.eval(Op::IntRight, v.size, &[v, shift]);
    b.eval(Op::IntNotEqual, 1, &[high, Varnode::constant(0, v.size)])
}

/// Set sign, zero and parity from a result. Every arithmetic and logical
/// instruction writes these three.
fn set_result_flags(b: &mut Builder, result: Varnode) {
    let sf = sign_of(b, result);
    b.emit(Op::Copy, Some(flag_sf()), &[sf]);
    let zf = b.eval(
        Op::IntEqual,
        1,
        &[result, Varnode::constant(0, result.size)],
    );
    b.emit(Op::Copy, Some(flag_zf()), &[zf]);
    // Parity is over the low byte only, on every width.
    let low = b.eval(
        Op::IntAnd,
        result.size,
        &[result, Varnode::constant(0xff, result.size)],
    );
    let ones = b.eval(Op::PopCount, 1, &[low]);
    let odd = b.eval(Op::IntAnd, 1, &[ones, Varnode::constant(1, 1)]);
    let pf = b.eval(Op::IntEqual, 1, &[odd, Varnode::constant(0, 1)]);
    b.emit(Op::Copy, Some(flag_pf()), &[pf]);
}

/// The adjust flag: a carry out of bit three, which is the same bit of
/// `x ^ y ^ result` on an addition and on a subtraction.
fn set_adjust_flag(b: &mut Builder, x: Varnode, y: Varnode, result: Varnode) {
    let size = result.size;
    let xy = b.eval(Op::IntXor, size, &[x, y]);
    let all = b.eval(Op::IntXor, size, &[xy, result]);
    let bit = b.eval(Op::IntAnd, size, &[all, Varnode::constant(0x10, size)]);
    let af = b.eval(Op::IntNotEqual, 1, &[bit, Varnode::constant(0, size)]);
    b.emit(Op::Copy, Some(flag_af()), &[af]);
}

/// Flags for an addition.
fn set_add_flags(b: &mut Builder, x: Varnode, y: Varnode, result: Varnode) {
    let cf = b.eval(Op::IntCarry, 1, &[x, y]);
    b.emit(Op::Copy, Some(flag_cf()), &[cf]);
    let of = b.eval(Op::IntSCarry, 1, &[x, y]);
    b.emit(Op::Copy, Some(flag_of()), &[of]);
    set_adjust_flag(b, x, y, result);
    set_result_flags(b, result);
}

/// Flags for a subtraction. The carry flag means a borrow, which is an
/// unsigned comparison rather than a carry out.
fn set_sub_flags(b: &mut Builder, x: Varnode, y: Varnode, result: Varnode) {
    let cf = b.eval(Op::IntLess, 1, &[x, y]);
    b.emit(Op::Copy, Some(flag_cf()), &[cf]);
    let of = b.eval(Op::IntSBorrow, 1, &[x, y]);
    b.emit(Op::Copy, Some(flag_of()), &[of]);
    set_adjust_flag(b, x, y, result);
    set_result_flags(b, result);
}

/// Flags for a logical operation: carry and overflow cleared, the rest from
/// the result.
fn set_logic_flags(b: &mut Builder, result: Varnode) {
    b.emit(Op::Copy, Some(flag_cf()), &[Varnode::constant(0, 1)]);
    b.emit(Op::Copy, Some(flag_of()), &[Varnode::constant(0, 1)]);
    b.emit(Op::Copy, Some(flag_af()), &[Varnode::constant(0, 1)]);
    set_result_flags(b, result);
}

/// Overflow and carry from the sign bits, for the forms that carry an incoming
/// flag and so cannot use the two-input operations.
fn set_signed_overflow(b: &mut Builder, x: Varnode, y: Varnode, result: Varnode, sub: bool) {
    let sx = sign_of(b, x);
    let sy = sign_of(b, y);
    let sr = sign_of(b, result);
    // An addition overflows when the addends agree in sign and the result does
    // not; a subtraction when they disagree and the result follows the second.
    let same = b.eval(Op::IntEqual, 1, &[sx, sy]);
    let differs = b.eval(Op::IntNotEqual, 1, &[sr, sx]);
    let of = if sub {
        let opposite = b.eval(Op::BoolNot, 1, &[same]);
        b.eval(Op::BoolAnd, 1, &[opposite, differs])
    } else {
        b.eval(Op::BoolAnd, 1, &[same, differs])
    };
    b.emit(Op::Copy, Some(flag_of()), &[of]);
}

/// The condition a `jcc`, `setcc` or `cmovcc` tests, taken from the suffix.
fn condition(b: &mut Builder, suffix: &str) -> Option<Varnode> {
    let (cf, zf, sf, of, pf) = (flag_cf(), flag_zf(), flag_sf(), flag_of(), flag_pf());
    let not = |b: &mut Builder, v: Varnode| b.eval(Op::BoolNot, 1, &[v]);
    Some(match suffix {
        "o" => of,
        "no" => not(b, of),
        "b" | "c" | "nae" => cf,
        "ae" | "nb" | "nc" => not(b, cf),
        "e" | "z" => zf,
        "ne" | "nz" => not(b, zf),
        "be" | "na" => b.eval(Op::BoolOr, 1, &[cf, zf]),
        "a" | "nbe" => {
            let ncf = not(b, cf);
            let nzf = not(b, zf);
            b.eval(Op::BoolAnd, 1, &[ncf, nzf])
        }
        "s" => sf,
        "ns" => not(b, sf),
        "p" | "pe" => pf,
        "np" | "po" => not(b, pf),
        "l" | "nge" => b.eval(Op::IntNotEqual, 1, &[sf, of]),
        "ge" | "nl" => b.eval(Op::IntEqual, 1, &[sf, of]),
        "le" | "ng" => {
            let lt = b.eval(Op::IntNotEqual, 1, &[sf, of]);
            b.eval(Op::BoolOr, 1, &[zf, lt])
        }
        "g" | "nle" => {
            let ge = b.eval(Op::IntEqual, 1, &[sf, of]);
            let nzf = not(b, zf);
            b.eval(Op::BoolAnd, 1, &[nzf, ge])
        }
        _ => return None,
    })
}

/// The suffix of a mnemonic beginning with `prefix`.
fn suffix<'a>(mnemonic: &'a str, prefix: &str) -> Option<&'a str> {
    mnemonic
        .strip_prefix(prefix)
        .filter(|s| !s.is_empty() && !s.contains(' '))
}

/// Write a pointer-wide value into a register that holds one.
///
/// In protected mode that is four bytes of an eight-byte slot, and the rest of
/// the slot does not exist on the machine. Zeroing it rather than leaving it
/// makes the write a whole-register write, which is the same rule the
/// architecture already applies to every 32-bit destination. Without it every
/// stack adjustment reads back as `sp & 0xffffffff00000000 | ...`, which is
/// true of the model and not of the machine.
fn write_ptr(b: &mut Builder, offset: u64, value: Varnode) {
    let p = b.ptr;
    b.emit(Op::Copy, Some(Varnode::register(offset, p)), &[value]);
    if p < 8 {
        b.emit(
            Op::Copy,
            Some(Varnode::register(offset + p as u64, 8 - p)),
            &[Varnode::constant(0, 8 - p)],
        );
    }
}

/// Push a value, which is one pointer wide: eight bytes in long mode, four in
/// protected mode.
fn push(b: &mut Builder, value: Varnode) {
    let p = b.ptr;
    let sp = Varnode::register(RSP, p);
    let lowered = b.eval(Op::IntSub, p, &[sp, Varnode::constant(p as u64, p)]);
    write_ptr(b, RSP, lowered);
    b.emit(Op::Store, None, &[Varnode::register(RSP, p), value]);
}

/// Pop into a varnode.
fn pop(b: &mut Builder, size: u8) -> Varnode {
    let p = b.ptr;
    let sp = Varnode::register(RSP, p);
    let value = b.eval(Op::Load, size, &[sp]);
    let raised = b.eval(Op::IntAdd, p, &[sp, Varnode::constant(p as u64, p)]);
    write_ptr(b, RSP, raised);
    value
}

/// Lift one x86-64 instruction.
pub fn lift(i: &Insn) -> Lifted {
    lift_sized(i, 8)
}

/// Lift one i386 instruction.
///
/// The same decoder and the same rules at half the pointer width. The two
/// modes differ in what a push moves the stack by, how wide a return address
/// is, and how wide an effective address is computed -- everything the
/// architecture calls the operand size is already carried by the operands.
pub fn lift32(i: &Insn) -> Lifted {
    lift_sized(i, 4)
}

fn lift_sized(i: &Insn, ptr: u8) -> Lifted {
    let mut b = Builder::sized(i.addr, ptr);
    let ops = i.operands();
    let next = Varnode::constant(i.next().get(), ptr);
    let at = i.next();

    // A repeated string operation is a loop, not one instruction, and is not
    // modelled rather than modelled as a single pass.
    if matches!(i.prefix, Some("rep") | Some("repne") | Some("repe")) {
        return b.unimplemented();
    }

    match i.flow {
        Flow::Branch(t) => {
            b.emit(Op::Branch, None, &[Varnode::constant(t.get(), ptr)]);
            return b.finish(true);
        }
        Flow::CondBranch(t) => {
            let Some(s) = suffix(i.mnemonic, "j") else {
                return b.unimplemented();
            };
            let Some(cond) = condition(&mut b, s) else {
                return b.unimplemented();
            };
            b.emit(Op::CBranch, None, &[Varnode::constant(t.get(), ptr), cond]);
            return b.finish(true);
        }
        Flow::Call(t) => {
            push(&mut b, next);
            b.emit(
                Op::Call,
                Some(Varnode::register(gpr_offset(0), ptr)),
                &[Varnode::constant(t.get(), ptr)],
            );
            clobber(&mut b);
            return b.finish(true);
        }
        Flow::IndirectCall => {
            let Some(target) = ops.first().and_then(|o| source(&mut b, o, ptr, at)) else {
                return b.unimplemented();
            };
            push(&mut b, next);
            b.emit(
                Op::CallInd,
                Some(Varnode::register(gpr_offset(0), ptr)),
                &[target],
            );
            clobber(&mut b);
            return b.finish(true);
        }
        Flow::IndirectBranch => {
            let Some(target) = ops.first().and_then(|o| source(&mut b, o, ptr, at)) else {
                return b.unimplemented();
            };
            b.emit(Op::BranchInd, None, &[target]);
            return b.finish(true);
        }
        Flow::Return => {
            let target = pop(&mut b, ptr);
            // `ret imm16` also drops the arguments the caller pushed.
            if let Some(Operand::Imm(n)) = ops.first() {
                let sp = Varnode::register(RSP, ptr);
                let raised = b.eval(Op::IntAdd, ptr, &[sp, Varnode::constant(*n as u64, ptr)]);
                write_ptr(&mut b, RSP, raised);
            }
            b.emit(Op::Return, None, &[target]);
            return b.finish(true);
        }
        Flow::Trap => {
            // A trap raises an exception and nothing after it runs, which the
            // flow already says. It changes no register on the way, so there
            // is nothing to model and nothing missing: complete, with no ops.
            return b.finish(true);
        }
        Flow::Syscall => {
            // What the instruction itself does to the register file is
            // specified: RCX takes the return address and R11 the flags. What
            // the kernel does is not knowable from here, so the result and
            // everything the convention lets it change is undefined rather
            // than guessed, and the flow still stops the interpreter.
            // Only `syscall` does that to RCX and R11. An i386 image reaches
            // the kernel through `int 0x80`, which leaves them alone, so the
            // one thing both forms have in common is the result.
            if ptr == 8 {
                let next = Varnode::constant(i.next().get(), 8);
                b.emit(Op::Copy, Some(Varnode::register(gpr_offset(1), 8)), &[next]);
                b.emit(
                    Op::Undefine,
                    Some(Varnode::register(gpr_offset(11), 8)),
                    &[],
                );
            }
            b.emit(Op::Undefine, Some(Varnode::register(gpr_offset(0), 8)), &[]);
            return b.finish(true);
        }
        Flow::Next => {}
    }

    // Anything naming a vector register goes to the SIMD lifter.
    if crate::lift::sse::handles(i) {
        return crate::lift::sse::lift(b, i);
    }

    let size = operand_size(ops).unwrap_or(8);
    let m = i.mnemonic;

    match m {
        "nop" | "endbr64" | "endbr32" | "hlt" | "pause" | "cld" | "std" | "lfence" | "mfence"
        | "sfence" | "prefetch" | "prefetchnta" | "prefetcht0" | "prefetcht1" | "prefetcht2" => {
            if m == "cld" {
                b.emit(Op::Copy, Some(flag_df()), &[Varnode::constant(0, 1)]);
            }
            if m == "std" {
                b.emit(Op::Copy, Some(flag_df()), &[Varnode::constant(1, 1)]);
            }
            b.finish(true)
        }
        "mov" | "movabs" => match two(&mut b, ops, size, at) {
            Some((_, src)) => {
                if store(&mut b, &ops[0], src, at).is_none() {
                    return b.unimplemented();
                }
                b.finish(true)
            }
            None => b.unimplemented(),
        },
        "lea" => {
            let Some(Operand::Mem(mem)) = ops.get(1) else {
                return b.unimplemented();
            };
            let Some(addr) = address(&mut b, mem, at) else {
                return b.unimplemented();
            };
            // Narrowing by relabelling the varnode names a location nothing
            // ever wrote: the address was computed at eight bytes, and its low
            // four are a piece of it, not a value of their own.
            let value = if size == addr.size {
                addr
            } else {
                b.eval(Op::SubPiece, size, &[addr, Varnode::constant(0, 1)])
            };
            match store(&mut b, &ops[0], value, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        "movzx" | "movsx" | "movsxd" => {
            let Some(dest) = ops.first() else {
                return b.unimplemented();
            };
            let dest_size = match dest {
                Operand::Reg(r) => width_bytes(r.width),
                _ => return b.unimplemented(),
            };
            let Some(src) = ops.get(1).and_then(|o| source(&mut b, o, dest_size, at)) else {
                return b.unimplemented();
            };
            let widened = if src.size >= dest_size {
                Varnode {
                    size: dest_size,
                    ..src
                }
            } else {
                let op = if m == "movzx" {
                    Op::IntZExt
                } else {
                    Op::IntSExt
                };
                b.eval(op, dest_size, &[src])
            };
            match store(&mut b, dest, widened, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        "push" => {
            let Some(v) = ops.first().and_then(|o| source(&mut b, o, ptr, at)) else {
                return b.unimplemented();
            };
            let wide = if v.size == ptr {
                v
            } else {
                b.eval(Op::IntSExt, ptr, &[v])
            };
            push(&mut b, wide);
            b.finish(true)
        }
        "pop" => {
            let v = pop(&mut b, ptr);
            match store(&mut b, &ops[0], v, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        "leave" => {
            // `mov rsp, rbp` then `pop rbp`.
            let bp = Varnode::register(gpr_offset(5), ptr);
            write_ptr(&mut b, RSP, bp);
            let saved = pop(&mut b, ptr);
            write_ptr(&mut b, gpr_offset(5), saved);
            b.finish(true)
        }
        // Bit test: the carry flag takes the selected bit and the rest are
        // left undefined, which is what the manual says and what the IR can
        // say exactly. The offset is taken modulo the operand width for a
        // register destination, which is the only form the decoder produces
        // here; a memory destination addresses a bit string and is declined.
        "bt" => {
            let (Some(x), Some(count)) = (
                ops.first().and_then(|o| source(&mut b, o, size, at)),
                ops.get(1).and_then(|o| source(&mut b, o, size, at)),
            ) else {
                return b.unimplemented();
            };
            if !matches!(ops.first(), Some(Operand::Reg(_))) {
                return b.unimplemented();
            }
            let bits = u64::from(size) * 8 - 1;
            let which = b.eval(Op::IntAnd, size, &[count, Varnode::constant(bits, size)]);
            let moved = b.eval(Op::IntRight, size, &[x, which]);
            let bit = b.eval(Op::IntAnd, size, &[moved, Varnode::constant(1, size)]);
            let one = b.eval(Op::IntNotEqual, 1, &[bit, Varnode::constant(0, size)]);
            b.emit(Op::Copy, Some(flag_cf()), &[one]);
            for f in [flag_of(), flag_sf(), flag_zf(), flag_af(), flag_pf()] {
                b.emit(Op::Undefine, Some(f), &[]);
            }
            b.finish(true)
        }

        "add" | "sub" | "and" | "or" | "xor" | "cmp" | "test" => {
            let Some((x, y)) = two(&mut b, ops, size, at) else {
                return b.unimplemented();
            };
            let (op, kind) = match m {
                "add" => (Op::IntAdd, Kind::Add),
                "sub" | "cmp" => (Op::IntSub, Kind::Sub),
                "and" | "test" => (Op::IntAnd, Kind::Logic),
                "or" => (Op::IntOr, Kind::Logic),
                _ => (Op::IntXor, Kind::Logic),
            };
            let result = b.eval(op, size, &[x, y]);
            match kind {
                Kind::Add => set_add_flags(&mut b, x, y, result),
                Kind::Sub => set_sub_flags(&mut b, x, y, result),
                Kind::Logic => set_logic_flags(&mut b, result),
            }
            // `cmp` and `test` discard the result and keep only the flags.
            if m != "cmp" && m != "test" && store(&mut b, &ops[0], result, at).is_none() {
                return b.unimplemented();
            }
            b.finish(true)
        }
        "adc" | "sbb" => {
            let Some((x, y)) = two(&mut b, ops, size, at) else {
                return b.unimplemented();
            };
            let carry_in = b.eval(Op::IntZExt, size, &[flag_cf()]);
            let (first, second) = if m == "adc" {
                (Op::IntAdd, Op::IntAdd)
            } else {
                (Op::IntSub, Op::IntSub)
            };
            let partial = b.eval(first, size, &[x, y]);
            let result = b.eval(second, size, &[partial, carry_in]);
            // The carry out happens in either step, so both are tested.
            let (c1, c2) = if m == "adc" {
                (
                    b.eval(Op::IntCarry, 1, &[x, y]),
                    b.eval(Op::IntCarry, 1, &[partial, carry_in]),
                )
            } else {
                (
                    b.eval(Op::IntLess, 1, &[x, y]),
                    b.eval(Op::IntLess, 1, &[partial, carry_in]),
                )
            };
            let cf = b.eval(Op::BoolOr, 1, &[c1, c2]);
            b.emit(Op::Copy, Some(flag_cf()), &[cf]);
            set_signed_overflow(&mut b, x, y, result, m == "sbb");
            set_adjust_flag(&mut b, x, y, result);
            set_result_flags(&mut b, result);
            if store(&mut b, &ops[0], result, at).is_none() {
                return b.unimplemented();
            }
            b.finish(true)
        }
        "inc" | "dec" => {
            let Some(x) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
                return b.unimplemented();
            };
            let one = Varnode::constant(1, size);
            let op = if m == "inc" { Op::IntAdd } else { Op::IntSub };
            let result = b.eval(op, size, &[x, one]);
            // These leave the carry flag alone, which is the whole reason a
            // compiler prefers them to `add`.
            let of = b.eval(
                if m == "inc" {
                    Op::IntSCarry
                } else {
                    Op::IntSBorrow
                },
                1,
                &[x, one],
            );
            b.emit(Op::Copy, Some(flag_of()), &[of]);
            set_adjust_flag(&mut b, x, one, result);
            set_result_flags(&mut b, result);
            if store(&mut b, &ops[0], result, at).is_none() {
                return b.unimplemented();
            }
            b.finish(true)
        }
        "neg" => {
            let Some(x) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
                return b.unimplemented();
            };
            let zero = Varnode::constant(0, size);
            let result = b.eval(Op::IntNegate, size, &[x]);
            // The carry flag is set unless the operand was zero.
            let cf = b.eval(Op::IntNotEqual, 1, &[x, zero]);
            b.emit(Op::Copy, Some(flag_cf()), &[cf]);
            let of = b.eval(Op::IntSBorrow, 1, &[zero, x]);
            b.emit(Op::Copy, Some(flag_of()), &[of]);
            set_adjust_flag(&mut b, zero, x, result);
            set_result_flags(&mut b, result);
            if store(&mut b, &ops[0], result, at).is_none() {
                return b.unimplemented();
            }
            b.finish(true)
        }
        "not" => {
            let Some(x) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
                return b.unimplemented();
            };
            let result = b.eval(Op::IntNot, size, &[x]);
            // `not` writes no flags at all.
            if store(&mut b, &ops[0], result, at).is_none() {
                return b.unimplemented();
            }
            b.finish(true)
        }
        "xchg" => {
            let Some((x, y)) = two(&mut b, ops, size, at) else {
                return b.unimplemented();
            };
            let tx = b.eval(Op::Copy, size, &[x]);
            let ty = b.eval(Op::Copy, size, &[y]);
            if store(&mut b, &ops[0], ty, at).is_none() || store(&mut b, &ops[1], tx, at).is_none()
            {
                return b.unimplemented();
            }
            b.finish(true)
        }
        "bswap" => {
            let Some(x) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
                return b.unimplemented();
            };
            let mut result: Option<Varnode> = None;
            for byte in 0..size {
                let from = Varnode::constant(byte as u64 * 8, 1);
                let to = (size - 1 - byte) as u64 * 8;
                let shifted = b.eval(Op::IntRight, size, &[x, from]);
                let isolated = b.eval(Op::IntAnd, size, &[shifted, Varnode::constant(0xff, size)]);
                let placed = b.eval(Op::IntLeft, size, &[isolated, Varnode::constant(to, 1)]);
                result = Some(match result {
                    None => placed,
                    Some(acc) => b.eval(Op::IntOr, size, &[acc, placed]),
                });
            }
            match result.and_then(|r| store(&mut b, &ops[0], r, at)) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        "shl" | "sal" | "shr" | "sar" | "rol" | "ror" => shift(b, i, ops, size, at),
        "imul" => imul(b, i, ops, size, at),
        "mul" => mul_one(b, ops, size, at),
        "div" | "idiv" => divide(b, ops, size, at, m == "idiv"),
        "cdq" | "cqo" | "cwd" => {
            // Sign-extend the accumulator into the high register.
            let acc_size: u8 = match m {
                "cdq" => 4,
                "cwd" => 2,
                _ => 8,
            };
            let acc = read(&mut b, Varnode::register(gpr_offset(0), acc_size));
            let sign = sign_of(&mut b, acc);
            let wide = if acc_size == 1 {
                sign
            } else {
                b.eval(Op::IntZExt, acc_size, &[sign])
            };
            let mask = b.eval(Op::IntNegate, acc_size, &[wide]);
            let dx = Varnode::register(gpr_offset(2), acc_size);
            b.emit(Op::Copy, Some(dx), &[mask]);
            if acc_size == 4 {
                b.emit(
                    Op::Copy,
                    Some(Varnode::register(gpr_offset(2) + 4, 4)),
                    &[Varnode::constant(0, 4)],
                );
            }
            b.finish(true)
        }
        "cdqe" => {
            let eax = Varnode::register(gpr_offset(0), 4);
            let wide = b.eval(Op::IntSExt, 8, &[eax]);
            b.emit(Op::Copy, Some(Varnode::register(gpr_offset(0), 8)), &[wide]);
            b.finish(true)
        }
        "cwde" => {
            let ax = Varnode::register(gpr_offset(0), 2);
            let wide = b.eval(Op::IntSExt, 4, &[ax]);
            write_reg(&mut b, Reg::gpr(0, Width::W32), wide);
            b.finish(true)
        }
        "popcnt" => {
            let Some(x) = ops.get(1).and_then(|o| source(&mut b, o, size, at)) else {
                return b.unimplemented();
            };
            let count = b.eval(Op::PopCount, size, &[x]);
            let zf = b.eval(Op::IntEqual, 1, &[x, Varnode::constant(0, size)]);
            b.emit(Op::Copy, Some(flag_zf()), &[zf]);
            for f in [flag_cf(), flag_of(), flag_sf(), flag_af(), flag_pf()] {
                b.emit(Op::Copy, Some(f), &[Varnode::constant(0, 1)]);
            }
            match store(&mut b, &ops[0], count, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        "lzcnt" | "tzcnt" | "bsf" | "bsr" => {
            let Some(x) = ops.get(1).and_then(|o| source(&mut b, o, size, at)) else {
                return b.unimplemented();
            };
            let zf = b.eval(Op::IntEqual, 1, &[x, Varnode::constant(0, size)]);
            let value = match m {
                "lzcnt" => b.eval(Op::LzCount, size, &[x]),
                "bsr" => {
                    // The index of the highest set bit: width minus one minus
                    // the leading zero count.
                    let lz = b.eval(Op::LzCount, size, &[x]);
                    b.eval(
                        Op::IntSub,
                        size,
                        &[Varnode::constant(size as u64 * 8 - 1, size), lz],
                    )
                }
                _ => {
                    // Trailing zeroes: the leading zeroes of the lowest set bit
                    // isolated by `x & -x`, counted from the other end.
                    let neg = b.eval(Op::IntNegate, size, &[x]);
                    let lowest = b.eval(Op::IntAnd, size, &[x, neg]);
                    let lz = b.eval(Op::LzCount, size, &[lowest]);
                    b.eval(
                        Op::IntSub,
                        size,
                        &[Varnode::constant(size as u64 * 8 - 1, size), lz],
                    )
                }
            };
            b.emit(Op::Copy, Some(flag_zf()), &[zf]);
            // For a zero input the destination is undefined on `bsf`/`bsr` and
            // the width on `lzcnt`/`tzcnt`; writing the computed value is
            // within what the architecture allows in both cases.
            match store(&mut b, &ops[0], value, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        _ if m.starts_with("set") => {
            let Some(s) = suffix(m, "set").and_then(|s| condition(&mut b, s)) else {
                return b.unimplemented();
            };
            match store(&mut b, &ops[0], s, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        _ if m.starts_with("cmov") => {
            let Some((dst, src)) = two(&mut b, ops, size, at) else {
                return b.unimplemented();
            };
            let Some(cond) = suffix(m, "cmov").and_then(|s| condition(&mut b, s)) else {
                return b.unimplemented();
            };
            let chosen = select(&mut b, cond, src, dst, size);
            match store(&mut b, &ops[0], chosen, at) {
                Some(()) => b.finish(true),
                None => b.unimplemented(),
            }
        }
        _ => b.unimplemented(),
    }
}

/// Say that a call left the caller-saved registers holding anything.
fn clobber(b: &mut Builder) {
    let abi = crate::abi::of(&e5r_core::Arch::X86_64);
    for offset in &abi.caller_saved {
        if *offset == gpr_offset(0) {
            continue;
        }
        b.emit(Op::Undefine, Some(Varnode::register(*offset, 8)), &[]);
    }
    for flag in [
        flag_cf(),
        flag_pf(),
        flag_af(),
        flag_zf(),
        flag_sf(),
        flag_of(),
    ] {
        b.emit(Op::Undefine, Some(flag), &[]);
    }
}

/// Which flag rule an arithmetic form follows.
enum Kind {
    Add,
    Sub,
    Logic,
}

/// The two operands of a binary form, destination first.
fn two(b: &mut Builder, ops: &[Operand], size: u8, at: Addr) -> Option<(Varnode, Varnode)> {
    let x = source(b, ops.first()?, size, at)?;
    let y = source(b, ops.get(1)?, size, at)?;
    let y = size_matched(b, y, size);
    Some((x, y))
}

/// Widen a source that is narrower than the operation, which happens for the
/// forms taking a byte immediate.
fn size_matched(b: &mut Builder, y: Varnode, size: u8) -> Varnode {
    if y.size == size {
        y
    } else if y.is_const() {
        Varnode { size, ..y }
    } else {
        b.eval(Op::IntSExt, size, &[y])
    }
}

/// Shifts and rotates.
fn shift(mut b: Builder, i: &Insn, ops: &[Operand], size: u8, at: Addr) -> Lifted {
    let Some(x) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
        return b.unimplemented();
    };
    // A one-operand form shifts by one.
    let raw = match ops.get(1) {
        Some(o) => match source(&mut b, o, 1, at) {
            Some(v) => v,
            None => return b.unimplemented(),
        },
        None => Varnode::constant(1, 1),
    };
    // The count is masked to the operand width, five bits below 64.
    let limit = if size == 8 { 0x3f } else { 0x1f };
    let count = b.eval(Op::IntAnd, 1, &[raw, Varnode::constant(limit, 1)]);
    let bits = size as u64 * 8;
    let m = i.mnemonic;

    let result = match m {
        "shl" | "sal" => b.eval(Op::IntLeft, size, &[x, count]),
        "shr" => b.eval(Op::IntRight, size, &[x, count]),
        "sar" => b.eval(Op::IntSRight, size, &[x, count]),
        "rol" | "ror" => {
            let other = b.eval(Op::IntSub, 1, &[Varnode::constant(bits, 1), count]);
            let (a, c) = if m == "rol" {
                (
                    b.eval(Op::IntLeft, size, &[x, count]),
                    b.eval(Op::IntRight, size, &[x, other]),
                )
            } else {
                (
                    b.eval(Op::IntRight, size, &[x, count]),
                    b.eval(Op::IntLeft, size, &[x, other]),
                )
            };
            // A rotate by zero would shift by the full width on the other
            // side, which this IR defines as zero, so the two halves still
            // recombine into the original.
            let joined = b.eval(Op::IntOr, size, &[a, c]);
            let zero_count = b.eval(Op::IntEqual, 1, &[count, Varnode::constant(0, 1)]);
            select(&mut b, zero_count, x, joined, size)
        }
        _ => return b.unimplemented(),
    };

    // The carry flag takes the last bit shifted out.
    let cf_new = match m {
        "shl" | "sal" | "rol" => {
            let back = b.eval(Op::IntSub, 1, &[Varnode::constant(bits, 1), count]);
            let moved = b.eval(Op::IntRight, size, &[x, back]);
            b.eval(
                Op::IntAnd,
                1,
                &[Varnode { size: 1, ..moved }, Varnode::constant(1, 1)],
            )
        }
        _ => {
            let back = b.eval(Op::IntSub, 1, &[count, Varnode::constant(1, 1)]);
            let moved = b.eval(Op::IntRight, size, &[x, back]);
            b.eval(
                Op::IntAnd,
                1,
                &[Varnode { size: 1, ..moved }, Varnode::constant(1, 1)],
            )
        }
    };
    // A shift by zero leaves every flag alone, so each update is selected on
    // the count rather than written unconditionally.
    let shifted = b.eval(Op::IntNotEqual, 1, &[count, Varnode::constant(0, 1)]);
    let cf = select(&mut b, shifted, cf_new, flag_cf(), 1);
    b.emit(Op::Copy, Some(flag_cf()), &[cf]);

    if matches!(m, "rol" | "ror") {
        // The rotates write only the carry and overflow flags.
        let top = sign_of(&mut b, result);
        let of_new = b.eval(Op::BoolXor, 1, &[top, cf]);
        let of = select(&mut b, shifted, of_new, flag_of(), 1);
        b.emit(Op::Copy, Some(flag_of()), &[of]);
    } else {
        let sf_new = sign_of(&mut b, result);
        let sf = select(&mut b, shifted, sf_new, flag_sf(), 1);
        b.emit(Op::Copy, Some(flag_sf()), &[sf]);
        let zf_new = b.eval(Op::IntEqual, 1, &[result, Varnode::constant(0, size)]);
        let zf = select(&mut b, shifted, zf_new, flag_zf(), 1);
        b.emit(Op::Copy, Some(flag_zf()), &[zf]);
        let low = b.eval(Op::IntAnd, size, &[result, Varnode::constant(0xff, size)]);
        let ones = b.eval(Op::PopCount, 1, &[low]);
        let odd = b.eval(Op::IntAnd, 1, &[ones, Varnode::constant(1, 1)]);
        let pf_new = b.eval(Op::IntEqual, 1, &[odd, Varnode::constant(0, 1)]);
        let pf = select(&mut b, shifted, pf_new, flag_pf(), 1);
        b.emit(Op::Copy, Some(flag_pf()), &[pf]);
        // Overflow is defined only for a shift by one; any value is allowed
        // otherwise, so the one-bit rule is used throughout.
        let of_new = match m {
            "shl" | "sal" => {
                let top = sign_of(&mut b, result);
                b.eval(Op::BoolXor, 1, &[top, cf])
            }
            "shr" => sign_of(&mut b, x),
            _ => Varnode::constant(0, 1),
        };
        let of = select(&mut b, shifted, of_new, flag_of(), 1);
        b.emit(Op::Copy, Some(flag_of()), &[of]);
    }

    if store(&mut b, &ops[0], result, at).is_none() {
        return b.unimplemented();
    }
    b.finish(true)
}

/// `imul` in its one, two and three operand forms.
fn imul(mut b: Builder, _i: &Insn, ops: &[Operand], size: u8, at: Addr) -> Lifted {
    if ops.len() == 1 {
        // The one-operand form multiplies the accumulator and writes both
        // halves of the product.
        let Some(y) = source(&mut b, &ops[0], size, at) else {
            return b.unimplemented();
        };
        let acc = read(&mut b, Varnode::register(gpr_offset(0), size));
        let low = b.eval(Op::IntMul, size, &[acc, y]);
        let high = b.eval(Op::IntSMulHigh, size, &[acc, y]);
        let expected = b.eval(
            Op::IntSRight,
            size,
            &[low, Varnode::constant(size as u64 * 8 - 1, 1)],
        );
        let fits = b.eval(Op::IntEqual, 1, &[high, expected]);
        let overflow = b.eval(Op::BoolNot, 1, &[fits]);
        b.emit(Op::Copy, Some(flag_cf()), &[overflow]);
        b.emit(Op::Copy, Some(flag_of()), &[overflow]);
        if size == 1 {
            // The byte form writes the whole product to `ax`.
            let wide = b.eval(Op::IntSExt, 2, &[low]);
            b.emit(Op::Copy, Some(Varnode::register(gpr_offset(0), 2)), &[wide]);
        } else {
            write_reg(&mut b, Reg::gpr(0, width_of(size)), low);
            write_reg(&mut b, Reg::gpr(2, width_of(size)), high);
        }
        set_result_flags(&mut b, low);
        return b.finish(true);
    }

    // Two and three operand forms write only the low half.
    let (x_op, y_op) = if ops.len() == 3 { (1, 2) } else { (0, 1) };
    let Some(x) = ops.get(x_op).and_then(|o| source(&mut b, o, size, at)) else {
        return b.unimplemented();
    };
    let Some(y) = ops.get(y_op).and_then(|o| source(&mut b, o, size, at)) else {
        return b.unimplemented();
    };
    let y = size_matched(&mut b, y, size);
    let low = b.eval(Op::IntMul, size, &[x, y]);
    let high = b.eval(Op::IntSMulHigh, size, &[x, y]);
    let expected = b.eval(
        Op::IntSRight,
        size,
        &[low, Varnode::constant(size as u64 * 8 - 1, 1)],
    );
    let fits = b.eval(Op::IntEqual, 1, &[high, expected]);
    let overflow = b.eval(Op::BoolNot, 1, &[fits]);
    b.emit(Op::Copy, Some(flag_cf()), &[overflow]);
    b.emit(Op::Copy, Some(flag_of()), &[overflow]);
    set_result_flags(&mut b, low);
    if store(&mut b, &ops[0], low, at).is_none() {
        return b.unimplemented();
    }
    b.finish(true)
}

/// The unsigned one-operand multiply.
fn mul_one(mut b: Builder, ops: &[Operand], size: u8, at: Addr) -> Lifted {
    let Some(y) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
        return b.unimplemented();
    };
    let acc = read(&mut b, Varnode::register(gpr_offset(0), size));
    let low = b.eval(Op::IntMul, size, &[acc, y]);
    let high = b.eval(Op::IntMulHigh, size, &[acc, y]);
    let overflow = b.eval(Op::IntNotEqual, 1, &[high, Varnode::constant(0, size)]);
    b.emit(Op::Copy, Some(flag_cf()), &[overflow]);
    b.emit(Op::Copy, Some(flag_of()), &[overflow]);
    if size == 1 {
        let wide = b.eval(Op::IntZExt, 2, &[low]);
        b.emit(Op::Copy, Some(Varnode::register(gpr_offset(0), 2)), &[wide]);
    } else {
        write_reg(&mut b, Reg::gpr(0, width_of(size)), low);
        write_reg(&mut b, Reg::gpr(2, width_of(size)), high);
    }
    set_result_flags(&mut b, low);
    b.finish(true)
}

/// The one-operand divides, whose dividend is twice the operand width.
fn divide(mut b: Builder, ops: &[Operand], size: u8, at: Addr, signed: bool) -> Lifted {
    let Some(d) = ops.first().and_then(|o| source(&mut b, o, size, at)) else {
        return b.unimplemented();
    };
    if size == 1 {
        // The byte form divides `ax`, not a pair of registers.
        let ax = Varnode::register(gpr_offset(0), 2);
        let wide = if signed {
            b.eval(Op::IntSExt, 2, &[d])
        } else {
            b.eval(Op::IntZExt, 2, &[d])
        };
        let q = b.eval(
            if signed { Op::IntSDiv } else { Op::IntDiv },
            2,
            &[ax, wide],
        );
        let r = b.eval(
            if signed { Op::IntSRem } else { Op::IntRem },
            2,
            &[ax, wide],
        );
        write(&mut b, Varnode::register(gpr_offset(0), 1), q);
        write(&mut b, Varnode::register(gpr_offset(0) + 1, 1), r);
        return b.finish(true);
    }
    let low = Varnode::register(gpr_offset(0), size);
    let high = Varnode::register(gpr_offset(2), size);
    let (div, rem) = if signed {
        (Op::IntSDiv128, Op::IntSRem128)
    } else {
        (Op::IntDiv128, Op::IntRem128)
    };
    let q = b.eval(div, size, &[high, low, d]);
    let r = b.eval(rem, size, &[high, low, d]);
    write_reg(&mut b, Reg::gpr(0, width_of(size)), q);
    write_reg(&mut b, Reg::gpr(2, width_of(size)), r);
    b.finish(true)
}

fn width_of(size: u8) -> Width {
    match size {
        1 => Width::W8,
        2 => Width::W16,
        4 => Width::W32,
        _ => Width::W64,
    }
}
