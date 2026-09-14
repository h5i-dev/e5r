//! x86-64 SIMD lifting, the integer part.
//!
//! Same idea as the NEON lifter: a vector register is sixteen bytes of the
//! register file and a lane is a varnode inside it. The packed integer
//! operations a compiler's vectorizer emits are all lane-wise, so they need
//! nothing the IR does not already have.
//!
//! The floating point instructions are a different matter and are not modelled
//! here, because the IR has no floating point operations and approximating
//! them with integer ones would produce answers that look right.

use r12e_arch::{Insn, Operand, RegClass};
use r12e_core::Addr;

use crate::lift::x86::{address, vec_offset};
use crate::lift::{Builder, Lifted};
use crate::op::{Op, Varnode};

/// One lane of a vector register.
fn lane(num: u8, index: u64, size: u8) -> Varnode {
    Varnode::register(vec_offset(num) + index * size as u64, size)
}

/// The vector register an operand names.
fn vector(op: &Operand) -> Option<u8> {
    match op {
        Operand::Reg(r) if r.class == RegClass::Vec => Some(r.num),
        _ => None,
    }
}

/// True when the SIMD lifter handles this instruction.
///
/// A conversion can name no vector register at all — `cvttsd2si rax, [rbp-8]`
/// reads memory and writes a general register — so the mnemonic decides for
/// those.
pub fn handles(i: &Insn) -> bool {
    i.operands()
        .iter()
        .any(|o| matches!(o, Operand::Reg(r) if r.class == RegClass::Vec))
        || i.mnemonic.starts_with("cvt")
}

/// Read sixteen bytes of a source operand into two temporaries, whichever
/// kind of operand it is.
fn read_wide(b: &mut Builder, op: &Operand, at: Addr) -> Option<[Varnode; 2]> {
    match op {
        Operand::Reg(r) if r.class == RegClass::Vec => Some([
            Varnode::register(vec_offset(r.num), 8),
            Varnode::register(vec_offset(r.num) + 8, 8),
        ]),
        Operand::Mem(m) => {
            let addr = address(b, m, at)?;
            let low = b.eval(Op::Load, 8, &[addr]);
            let next = b.eval(Op::IntAdd, 8, &[addr, Varnode::constant(8, 8)]);
            let high = b.eval(Op::Load, 8, &[next]);
            Some([low, high])
        }
        _ => None,
    }
}

/// The lane size a packed mnemonic works at, from its suffix letter.
fn lane_size(m: &str) -> Option<u8> {
    Some(match m.chars().last()? {
        'b' => 1,
        'w' => 2,
        'd' => 4,
        'q' => 8,
        _ => return None,
    })
}

/// Lift one SIMD instruction.
pub fn lift(mut b: Builder, i: &Insn) -> Lifted {
    let ops = i.operands();
    let at = i.next();
    let m = i.mnemonic;

    if let Some(l) = scalar_float(&mut b, i) {
        return l;
    }

    match m {
        // Whole-register moves, aligned or not: the IR does not model the
        // fault an unaligned access to the aligned form would take.
        "movdqa" | "movdqu" | "movaps" | "movups" | "movapd" | "movupd" | "lddqu" => {
            match (ops.first(), ops.get(1)) {
                (Some(dst), Some(src)) => {
                    let Some(value) = read_wide(&mut b, src, at) else {
                        return b.unimplemented();
                    };
                    match dst {
                        Operand::Reg(r) if r.class == RegClass::Vec => {
                            b.emit(Op::Copy, Some(lane(r.num, 0, 8)), &[value[0]]);
                            b.emit(Op::Copy, Some(lane(r.num, 1, 8)), &[value[1]]);
                        }
                        Operand::Mem(mem) => {
                            let Some(addr) = address(&mut b, mem, at) else {
                                return b.unimplemented();
                            };
                            b.emit(Op::Store, None, &[addr, value[0]]);
                            let next = b.eval(Op::IntAdd, 8, &[addr, Varnode::constant(8, 8)]);
                            b.emit(Op::Store, None, &[next, value[1]]);
                        }
                        _ => return b.unimplemented(),
                    }
                    b.finish(true)
                }
                _ => b.unimplemented(),
            }
        }
        // The narrow moves, which clear the rest of the register when the
        // destination is a vector one.
        "movd" | "movq" => {
            let size = if m == "movd" { 4 } else { 8 };
            match (ops.first(), ops.get(1)) {
                (Some(Operand::Reg(d)), Some(src)) if d.class == RegClass::Vec => {
                    let value = match src {
                        Operand::Reg(s) if s.class == RegClass::Vec => lane(s.num, 0, size),
                        Operand::Reg(s) => {
                            Varnode::register(crate::lift::x86::gpr_offset(s.num), size)
                        }
                        Operand::Mem(mem) => {
                            let Some(addr) = address(&mut b, mem, at) else {
                                return b.unimplemented();
                            };
                            b.eval(Op::Load, size, &[addr])
                        }
                        _ => return b.unimplemented(),
                    };
                    b.emit(Op::Copy, Some(lane(d.num, 0, size)), &[value]);
                    // Everything above the moved bytes becomes zero.
                    let mut off = size as u64;
                    while off < 16 {
                        let chunk = crate::lift::neon::aligned_chunk(off, 16);
                        b.emit(
                            Op::Copy,
                            Some(Varnode::register(vec_offset(d.num) + off, chunk)),
                            &[Varnode::constant(0, chunk)],
                        );
                        off += chunk as u64;
                    }
                    b.finish(true)
                }
                (Some(dst), Some(Operand::Reg(s))) if s.class == RegClass::Vec => {
                    let value = lane(s.num, 0, size);
                    match dst {
                        Operand::Reg(d) => {
                            b.emit(
                                Op::Copy,
                                Some(Varnode::register(crate::lift::x86::gpr_offset(d.num), size)),
                                &[value],
                            );
                            if size == 4 {
                                b.emit(
                                    Op::Copy,
                                    Some(Varnode::register(
                                        crate::lift::x86::gpr_offset(d.num) + 4,
                                        4,
                                    )),
                                    &[Varnode::constant(0, 4)],
                                );
                            }
                        }
                        Operand::Mem(mem) => {
                            let Some(addr) = address(&mut b, mem, at) else {
                                return b.unimplemented();
                            };
                            b.emit(Op::Store, None, &[addr, value]);
                        }
                        _ => return b.unimplemented(),
                    }
                    b.finish(true)
                }
                _ => b.unimplemented(),
            }
        }
        // The bitwise operations, which have no lanes.
        "pxor" | "pand" | "por" | "pandn" | "xorps" | "xorpd" | "andps" | "andpd" | "orps"
        | "orpd" | "andnps" | "andnpd" => {
            let (Some(d), Some(src)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            for half in 0..2u64 {
                let x = lane(d, half, 8);
                let r = match m {
                    "pxor" | "xorps" | "xorpd" => b.eval(Op::IntXor, 8, &[x, y[half as usize]]),
                    "por" | "orps" | "orpd" => b.eval(Op::IntOr, 8, &[x, y[half as usize]]),
                    "pandn" | "andnps" | "andnpd" => {
                        let inverted = b.eval(Op::IntNot, 8, &[x]);
                        b.eval(Op::IntAnd, 8, &[inverted, y[half as usize]])
                    }
                    _ => b.eval(Op::IntAnd, 8, &[x, y[half as usize]]),
                };
                b.emit(Op::Copy, Some(lane(d, half, 8)), &[r]);
            }
            b.finish(true)
        }
        // Lane-wise arithmetic.
        "paddb" | "paddw" | "paddd" | "paddq" | "psubb" | "psubw" | "psubd" | "psubq"
        | "pmullw" | "pmulld" | "pminub" | "pmaxub" | "pminsd" | "pmaxsd" | "pcmpeqb"
        | "pcmpeqw" | "pcmpeqd" | "pcmpeqq" | "pcmpgtb" | "pcmpgtw" | "pcmpgtd" => {
            let (Some(d), Some(src)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(size) = lane_size(m) else {
                return b.unimplemented();
            };
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            // Name the source halves so a lane can be cut out of them.
            let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
            let count = 16 / size as u64;
            for n in 0..count {
                let x = lane(d, n, size);
                let c = piece(&mut b, source, n, size);
                let r = match m {
                    _ if m.starts_with("padd") => b.eval(Op::IntAdd, size, &[x, c]),
                    _ if m.starts_with("psub") => b.eval(Op::IntSub, size, &[x, c]),
                    _ if m.starts_with("pmul") => b.eval(Op::IntMul, size, &[x, c]),
                    _ if m.starts_with("pcmpeq") => {
                        let equal = b.eval(Op::IntEqual, 1, &[x, c]);
                        all_bits(&mut b, equal, size)
                    }
                    _ if m.starts_with("pcmpgt") => {
                        let greater = b.eval(Op::IntSLess, 1, &[c, x]);
                        all_bits(&mut b, greater, size)
                    }
                    "pminub" | "pminsd" => {
                        let op = if m == "pminub" {
                            Op::IntLess
                        } else {
                            Op::IntSLess
                        };
                        let less = b.eval(op, 1, &[x, c]);
                        select(&mut b, less, x, c, size)
                    }
                    _ => {
                        let op = if m == "pmaxub" {
                            Op::IntLess
                        } else {
                            Op::IntSLess
                        };
                        let less = b.eval(op, 1, &[x, c]);
                        select(&mut b, less, c, x, size)
                    }
                };
                b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
            }
            b.finish(true)
        }
        // The even 32-bit lanes multiplied into 64-bit results.
        "pmuludq" => {
            let (Some(d), Some(src)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
            let mut results = Vec::new();
            for half in 0..2u64 {
                let x = lane(d, half * 2, 4);
                let c = piece(&mut b, source, half * 2, 4);
                let wx = b.eval(Op::IntZExt, 8, &[x]);
                let wc = b.eval(Op::IntZExt, 8, &[c]);
                results.push(b.eval(Op::IntMul, 8, &[wx, wc]));
            }
            for (half, r) in results.into_iter().enumerate() {
                b.emit(Op::Copy, Some(lane(d, half as u64, 8)), &[r]);
            }
            b.finish(true)
        }
        // Lane permutation by an immediate.
        "pshufd" => {
            let (Some(d), Some(src), Some(order)) =
                (ops.first().and_then(vector), ops.get(1), ops.get(2))
            else {
                return b.unimplemented();
            };
            let control = match order {
                Operand::Imm(v) => *v as u64,
                Operand::UImm(v) => *v,
                Operand::Count(v) => *v as u64,
                _ => return b.unimplemented(),
            };
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
            let mut picked = Vec::new();
            for n in 0..4u64 {
                let from = (control >> (n * 2)) & 3;
                picked.push(piece(&mut b, source, from, 4));
            }
            for (n, v) in picked.into_iter().enumerate() {
                let named = b.eval(Op::Copy, 4, &[v]);
                b.emit(Op::Copy, Some(lane(d, n as u64, 4)), &[named]);
            }
            b.finish(true)
        }
        // Interleaving the low or high halves.
        "punpcklbw" | "punpcklwd" | "punpckldq" | "punpcklqdq" | "punpckhbw" | "punpckhwd"
        | "punpckhdq" | "punpckhqdq" => {
            let (Some(d), Some(src)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let size: u8 = match m {
                "punpcklbw" | "punpckhbw" => 1,
                "punpcklwd" | "punpckhwd" => 2,
                "punpckldq" | "punpckhdq" => 4,
                _ => 8,
            };
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
            let count = 16 / size as u64;
            let base = if m.starts_with("punpckh") {
                count / 2
            } else {
                0
            };
            let mut picked = Vec::new();
            for n in 0..count {
                let index = base + n / 2;
                let v = if n % 2 == 0 {
                    let l = lane(d, index, size);
                    b.eval(Op::Copy, size, &[l])
                } else {
                    let p = piece(&mut b, source, index, size);
                    b.eval(Op::Copy, size, &[p])
                };
                picked.push(v);
            }
            for (n, v) in picked.into_iter().enumerate() {
                b.emit(Op::Copy, Some(lane(d, n as u64, size)), &[v]);
            }
            b.finish(true)
        }
        // Packing with saturation: two registers of wide lanes become one of
        // narrow ones, each clamped to what the narrow lane can hold.
        "packssdw" | "packsswb" | "packusdw" | "packuswb" => {
            let (Some(d), Some(src)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let wide: u8 = if m.ends_with("dw") { 4 } else { 2 };
            let narrow = wide / 2;
            let signed = m.starts_with("packs");
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
            let per = 16 / wide as u64;
            let mut packed = Vec::new();
            for n in 0..per {
                let v = lane(d, n, wide);
                packed.push(saturate(&mut b, v, wide, narrow, signed));
            }
            for n in 0..per {
                let v = piece(&mut b, source, n, wide);
                packed.push(saturate(&mut b, v, wide, narrow, signed));
            }
            for (n, v) in packed.into_iter().enumerate() {
                b.emit(Op::Copy, Some(lane(d, n as u64, narrow)), &[v]);
            }
            b.finish(true)
        }
        // Shuffling one half's words, leaving the other half alone.
        "pshuflw" | "pshufhw" => {
            let (Some(d), Some(src), Some(order)) =
                (ops.first().and_then(vector), ops.get(1), ops.get(2))
            else {
                return b.unimplemented();
            };
            let control = match order {
                Operand::Imm(v) => *v as u64,
                Operand::UImm(v) => *v,
                Operand::Count(v) => *v as u64,
                _ => return b.unimplemented(),
            };
            let Some(y) = read_wide(&mut b, src, at) else {
                return b.unimplemented();
            };
            let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
            let base = if m == "pshufhw" { 4u64 } else { 0 };
            let mut picked = Vec::new();
            for n in 0..4u64 {
                let from = base + ((control >> (n * 2)) & 3);
                picked.push(piece(&mut b, source, from, 2));
            }
            // The untouched half is copied across, because the source may be
            // memory or another register.
            let other = if m == "pshufhw" { 0u64 } else { 4 };
            let mut kept = Vec::new();
            for n in 0..4u64 {
                kept.push(piece(&mut b, source, other + n, 2));
            }
            for (n, v) in picked.into_iter().enumerate() {
                let named = b.eval(Op::Copy, 2, &[v]);
                b.emit(Op::Copy, Some(lane(d, base + n as u64, 2)), &[named]);
            }
            for (n, v) in kept.into_iter().enumerate() {
                let named = b.eval(Op::Copy, 2, &[v]);
                b.emit(Op::Copy, Some(lane(d, other + n as u64, 2)), &[named]);
            }
            b.finish(true)
        }
        // One lane out to a general register.
        "pextrw" | "pextrb" | "pextrd" | "pextrq" => {
            let size: u8 = match m {
                "pextrb" => 1,
                "pextrw" => 2,
                "pextrd" => 4,
                _ => 8,
            };
            let (Some(dst), Some(s), Some(index)) =
                (ops.first(), ops.get(1).and_then(vector), ops.get(2))
            else {
                return b.unimplemented();
            };
            let n = match index {
                Operand::Imm(v) => *v as u64,
                Operand::UImm(v) => *v,
                Operand::Count(v) => *v as u64,
                _ => return b.unimplemented(),
            } % (16 / size as u64);
            let value = lane(s, n, size);
            match dst {
                Operand::Reg(r) if r.class != RegClass::Vec => {
                    // The destination is a full register and the lane is
                    // zero-extended into it.
                    let dest_size = if size == 8 { 8 } else { 4 };
                    let widened = if size == dest_size {
                        value
                    } else {
                        b.eval(Op::IntZExt, dest_size, &[value])
                    };
                    b.emit(
                        Op::Copy,
                        Some(Varnode::register(
                            crate::lift::x86::gpr_offset(r.num),
                            dest_size,
                        )),
                        &[widened],
                    );
                    if dest_size == 4 {
                        b.emit(
                            Op::Copy,
                            Some(Varnode::register(
                                crate::lift::x86::gpr_offset(r.num) + 4,
                                4,
                            )),
                            &[Varnode::constant(0, 4)],
                        );
                    }
                    b.finish(true)
                }
                Operand::Mem(mem) => {
                    let Some(addr) = address(&mut b, mem, at) else {
                        return b.unimplemented();
                    };
                    b.emit(Op::Store, None, &[addr, value]);
                    b.finish(true)
                }
                _ => b.unimplemented(),
            }
        }
        // Shifts of whole lanes by an immediate.
        "psllq" | "psrlq" | "pslld" | "psrld" | "psllw" | "psrlw" | "psrad" | "psraw" => {
            let (Some(d), Some(amount)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let Some(size) = lane_size(m) else {
                return b.unimplemented();
            };
            let op = match &m[0..4] {
                "psll" => Op::IntLeft,
                "psrl" => Op::IntRight,
                _ => Op::IntSRight,
            };
            let lanes = 16 / size as u64;
            // A count in a register, which is the low 64 bits of the source
            // vector. A count at or above the lane's width gives zero for a
            // logical shift, so the shift is forced into range and the result
            // masked to nothing, which is exact. The arithmetic form
            // saturates to the sign instead and is declined rather than
            // approximated.
            if let Some(src) = vector(amount) {
                if op == Op::IntSRight {
                    return b.unimplemented();
                }
                let raw = lane(src, 0, 8);
                let bits = Varnode::constant(u64::from(size) * 8, 8);
                let ok = b.eval(Op::IntLess, 1, &[raw, bits]);
                let wide = b.eval(Op::IntZExt, size, &[ok]);
                let mask = b.eval(Op::IntSub, size, &[Varnode::constant(0, size), wide]);
                let narrow = b.eval(Op::SubPiece, size, &[raw, Varnode::constant(0, 1)]);
                let count = b.eval(Op::IntAnd, size, &[narrow, mask]);
                for k in 0..lanes {
                    let x = lane(d, k, size);
                    let r = b.eval(op, size, &[x, count]);
                    let r = b.eval(Op::IntAnd, size, &[r, mask]);
                    b.emit(Op::Copy, Some(lane(d, k, size)), &[r]);
                }
                return b.finish(true);
            }
            let n = match amount {
                Operand::Imm(v) => *v as u64,
                Operand::UImm(v) => *v,
                Operand::Count(v) => *v as u64,
                _ => return b.unimplemented(),
            };
            for k in 0..lanes {
                let x = lane(d, k, size);
                let r = b.eval(op, size, &[x, Varnode::constant(n, 1)]);
                b.emit(Op::Copy, Some(lane(d, k, size)), &[r]);
            }
            b.finish(true)
        }
        // Shifting the whole register by whole bytes.
        "pslldq" | "psrldq" => {
            let (Some(d), Some(amount)) = (ops.first().and_then(vector), ops.get(1)) else {
                return b.unimplemented();
            };
            let n = match amount {
                Operand::Imm(v) => (*v as u64).min(16),
                Operand::UImm(v) => (*v).min(16),
                Operand::Count(v) => (*v as u64).min(16),
                _ => return b.unimplemented(),
            };
            let mut bytes = Vec::new();
            for k in 0..16u64 {
                let from = if m == "pslldq" {
                    k.checked_sub(n)
                } else {
                    (k + n < 16).then_some(k + n)
                };
                bytes.push(match from {
                    Some(index) => b.eval(Op::Copy, 1, &[lane(d, index, 1)]),
                    None => Varnode::constant(0, 1),
                });
            }
            for (k, v) in bytes.into_iter().enumerate() {
                b.emit(Op::Copy, Some(lane(d, k as u64, 1)), &[v]);
            }
            b.finish(true)
        }
        _ => b.unimplemented(),
    }
}

/// The scalar floating point instructions, which operate on the low lane and
/// leave the rest of the register alone.
fn scalar_float(b: &mut Builder, i: &Insn) -> Option<Lifted> {
    let m = i.mnemonic;
    let ops = i.operands();
    let at = i.next();
    // The trailing `ss` or `sd` says single or double, scalar either way.
    let size: u8 = if m.ends_with("ss") {
        4
    } else if m.ends_with("sd") {
        8
    } else if m.ends_with("ps") {
        4
    } else if m.ends_with("pd") {
        8
    } else {
        0
    };

    // The scalar moves, which behave differently from register and from
    // memory: from memory the rest of the register is cleared.
    if matches!(m, "movss" | "movsd") {
        let (dst, src) = (ops.first()?, ops.get(1)?);
        let value = match src {
            Operand::Reg(r) if r.class == RegClass::Vec => lane(r.num, 0, size),
            Operand::Mem(mem) => {
                let addr = address(b, mem, at)?;
                b.eval(Op::Load, size, &[addr])
            }
            _ => return None,
        };
        match dst {
            Operand::Reg(d) if d.class == RegClass::Vec => {
                b.emit(Op::Copy, Some(lane(d.num, 0, size)), &[value]);
                if matches!(src, Operand::Mem(_)) {
                    let mut off = size as u64;
                    while off < 16 {
                        let chunk = crate::lift::neon::aligned_chunk(off, 16);
                        b.emit(
                            Op::Copy,
                            Some(Varnode::register(vec_offset(d.num) + off, chunk)),
                            &[Varnode::constant(0, chunk)],
                        );
                        off += chunk as u64;
                    }
                }
            }
            Operand::Mem(mem) => {
                let addr = address(b, mem, at)?;
                b.emit(Op::Store, None, &[addr, value]);
            }
            _ => return None,
        }
        return Some(b.clone_finish());
    }

    let arithmetic = matches!(
        &m[..m.len().saturating_sub(2)],
        "add" | "sub" | "mul" | "div" | "min" | "max" | "sqrt"
    );
    if arithmetic && size != 0 {
        let d = match ops.first()? {
            Operand::Reg(r) if r.class == RegClass::Vec => r.num,
            _ => return None,
        };
        let packed = m.ends_with("ps") || m.ends_with("pd");
        let count = if packed { 16 / size as u64 } else { 1 };
        let y = read_wide(b, ops.get(1)?, at)?;
        let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
        for n in 0..count {
            let x = lane(d, n, size);
            let c = piece(b, source, n, size);
            let op = match &m[..m.len() - 2] {
                "add" => Op::FloatAdd,
                "sub" => Op::FloatSub,
                "mul" => Op::FloatMul,
                "div" => Op::FloatDiv,
                "min" => Op::FloatMin,
                "max" => Op::FloatMax,
                _ => Op::FloatSqrt,
            };
            let r = if op == Op::FloatSqrt {
                b.eval(op, size, &[c])
            } else {
                b.eval(op, size, &[x, c])
            };
            b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
        }
        return Some(b.clone_finish());
    }

    // The ordered and unordered compares, which write the integer flags.
    if matches!(m, "ucomiss" | "ucomisd" | "comiss" | "comisd") {
        let width: u8 = if m.ends_with("ss") { 4 } else { 8 };
        let d = match ops.first()? {
            Operand::Reg(r) if r.class == RegClass::Vec => r.num,
            _ => return None,
        };
        let x = lane(d, 0, width);
        let c = match ops.get(1)? {
            Operand::Reg(r) if r.class == RegClass::Vec => lane(r.num, 0, width),
            Operand::Mem(mem) => {
                let addr = address(b, mem, at)?;
                b.eval(Op::Load, width, &[addr])
            }
            _ => return None,
        };
        use crate::lift::x86::{flag_af, flag_cf, flag_of, flag_pf, flag_sf, flag_zf};
        // Unordered sets all three of zero, parity and carry; otherwise they
        // carry the comparison and the other three are cleared.
        let nan_x = b.eval(Op::FloatNan, 1, &[x]);
        let nan_y = b.eval(Op::FloatNan, 1, &[c]);
        let unordered = b.eval(Op::BoolOr, 1, &[nan_x, nan_y]);
        let less = b.eval(Op::FloatLess, 1, &[x, c]);
        let equal = b.eval(Op::FloatEqual, 1, &[x, c]);
        let zf = b.eval(Op::BoolOr, 1, &[unordered, equal]);
        let cf = b.eval(Op::BoolOr, 1, &[unordered, less]);
        b.emit(Op::Copy, Some(flag_zf()), &[zf]);
        b.emit(Op::Copy, Some(flag_cf()), &[cf]);
        b.emit(Op::Copy, Some(flag_pf()), &[unordered]);
        for f in [flag_of(), flag_sf(), flag_af()] {
            b.emit(Op::Copy, Some(f), &[Varnode::constant(0, 1)]);
        }
        return Some(b.clone_finish());
    }

    // The compares that write a mask rather than flags: the mnemonic carries
    // the predicate.
    if m.starts_with("cmp") && size != 0 && m.len() > 5 {
        let predicate = &m[3..m.len() - 2];
        let packed = m.ends_with("ps") || m.ends_with("pd");
        let d = match ops.first()? {
            Operand::Reg(r) if r.class == RegClass::Vec => r.num,
            _ => return None,
        };
        let y = read_wide(b, ops.get(1)?, at)?;
        let source = [b.eval(Op::Copy, 8, &[y[0]]), b.eval(Op::Copy, 8, &[y[1]])];
        let count = if packed { 16 / size as u64 } else { 1 };
        for n in 0..count {
            let x = lane(d, n, size);
            let c = piece(b, source, n, size);
            let truth = match predicate {
                "eq" => b.eval(Op::FloatEqual, 1, &[x, c]),
                "lt" => b.eval(Op::FloatLess, 1, &[x, c]),
                "le" => b.eval(Op::FloatLessEqual, 1, &[x, c]),
                "neq" => b.eval(Op::FloatNotEqual, 1, &[x, c]),
                "nlt" => {
                    let less = b.eval(Op::FloatLess, 1, &[x, c]);
                    b.eval(Op::BoolNot, 1, &[less])
                }
                "nle" => {
                    let le = b.eval(Op::FloatLessEqual, 1, &[x, c]);
                    b.eval(Op::BoolNot, 1, &[le])
                }
                "unord" => {
                    let a = b.eval(Op::FloatNan, 1, &[x]);
                    let e = b.eval(Op::FloatNan, 1, &[c]);
                    b.eval(Op::BoolOr, 1, &[a, e])
                }
                "ord" => {
                    let a = b.eval(Op::FloatNan, 1, &[x]);
                    let e = b.eval(Op::FloatNan, 1, &[c]);
                    let either = b.eval(Op::BoolOr, 1, &[a, e]);
                    b.eval(Op::BoolNot, 1, &[either])
                }
                _ => return None,
            };
            let mask = all_bits(b, truth, size);
            b.emit(Op::Copy, Some(lane(d, n, size)), &[mask]);
        }
        return Some(b.clone_finish());
    }

    // The conversions.
    let converted = match m {
        "cvtsi2ss" | "cvtsi2sd" => {
            let to: u8 = if m.ends_with("ss") { 4 } else { 8 };
            let d = match ops.first()? {
                Operand::Reg(r) if r.class == RegClass::Vec => r.num,
                _ => return None,
            };
            let src = match ops.get(1)? {
                Operand::Reg(r) => Varnode::register(
                    crate::lift::x86::gpr_offset(r.num),
                    if r.width == r12e_arch::Width::W64 {
                        8
                    } else {
                        4
                    },
                ),
                Operand::Mem(mem) => {
                    let addr = address(b, mem, at)?;
                    let bytes = if mem.size == 0 { 4 } else { mem.size as u8 };
                    b.eval(Op::Load, bytes, &[addr])
                }
                _ => return None,
            };
            let v = b.eval(Op::IntToFloat, to, &[src]);
            b.emit(Op::Copy, Some(lane(d, 0, to)), &[v]);
            true
        }
        "cvttss2si" | "cvttsd2si" | "cvtss2si" | "cvtsd2si" => {
            let from: u8 = if m.contains("ss") { 4 } else { 8 };
            let (dest, dest_size) = match ops.first()? {
                Operand::Reg(r) => (
                    r.num,
                    if r.width == r12e_arch::Width::W64 {
                        8u8
                    } else {
                        4
                    },
                ),
                _ => return None,
            };
            let src = match ops.get(1)? {
                Operand::Reg(r) if r.class == RegClass::Vec => lane(r.num, 0, from),
                Operand::Mem(mem) => {
                    let addr = address(b, mem, at)?;
                    b.eval(Op::Load, from, &[addr])
                }
                _ => return None,
            };
            let v = b.eval(Op::FloatToInt, dest_size, &[src]);
            b.emit(
                Op::Copy,
                Some(Varnode::register(
                    crate::lift::x86::gpr_offset(dest),
                    dest_size,
                )),
                &[v],
            );
            if dest_size == 4 {
                b.emit(
                    Op::Copy,
                    Some(Varnode::register(crate::lift::x86::gpr_offset(dest) + 4, 4)),
                    &[Varnode::constant(0, 4)],
                );
            }
            true
        }
        "cvtss2sd" | "cvtsd2ss" => {
            let (from, to): (u8, u8) = if m == "cvtss2sd" { (4, 8) } else { (8, 4) };
            let d = match ops.first()? {
                Operand::Reg(r) if r.class == RegClass::Vec => r.num,
                _ => return None,
            };
            let src = match ops.get(1)? {
                Operand::Reg(r) if r.class == RegClass::Vec => lane(r.num, 0, from),
                Operand::Mem(mem) => {
                    let addr = address(b, mem, at)?;
                    b.eval(Op::Load, from, &[addr])
                }
                _ => return None,
            };
            let v = b.eval(Op::FloatConvert, to, &[src]);
            b.emit(Op::Copy, Some(lane(d, 0, to)), &[v]);
            true
        }
        _ => false,
    };
    if converted {
        return Some(b.clone_finish());
    }
    None
}

/// One lane cut out of a pair of eight-byte temporaries.
fn piece(b: &mut Builder, source: [Varnode; 2], index: u64, size: u8) -> Varnode {
    let per_half = 8 / size as u64;
    let half = source[(index / per_half) as usize];
    let within = index % per_half;
    if within == 0 && size == 8 {
        return half;
    }
    let shifted = if within == 0 {
        half
    } else {
        b.eval(
            Op::IntRight,
            8,
            &[half, Varnode::constant(within * size as u64 * 8, 1)],
        )
    };
    b.eval(Op::SubPiece, size, &[shifted, Varnode::constant(0, 1)])
}

/// Clamp a wide lane into a narrow one, which is what packing does.
fn saturate(b: &mut Builder, v: Varnode, wide: u8, narrow: u8, signed: bool) -> Varnode {
    let bits = narrow as u64 * 8;
    let (low, high) = if signed {
        ((!0u64 << (bits - 1)) & mask(wide), (1u64 << (bits - 1)) - 1)
    } else {
        (0, (1u64 << bits) - 1)
    };
    let hi = Varnode::constant(high, wide);
    let lo = Varnode::constant(low, wide);
    let above = if signed {
        b.eval(Op::IntSLess, 1, &[hi, v])
    } else {
        b.eval(Op::IntLess, 1, &[hi, v])
    };
    let clamped_high = select(b, above, hi, v, wide);
    let below = if signed {
        b.eval(Op::IntSLess, 1, &[clamped_high, lo])
    } else {
        b.eval(Op::IntLess, 1, &[clamped_high, lo])
    };
    let clamped = select(b, below, lo, clamped_high, wide);
    b.eval(Op::SubPiece, narrow, &[clamped, Varnode::constant(0, 1)])
}

/// The mask of a value of this many bytes.
fn mask(size: u8) -> u64 {
    if size >= 8 {
        u64::MAX
    } else {
        (1u64 << (size as u64 * 8)) - 1
    }
}

/// Spread a zero-or-one across a whole lane, which is what a packed compare
/// writes.
fn all_bits(b: &mut Builder, truth: Varnode, size: u8) -> Varnode {
    let wide = if size == 1 {
        truth
    } else {
        b.eval(Op::IntZExt, size, &[truth])
    };
    b.eval(Op::IntNegate, size, &[wide])
}

/// A branch-free choice between two lanes.
fn select(b: &mut Builder, cond: Varnode, t: Varnode, f: Varnode, size: u8) -> Varnode {
    let mask = all_bits(b, cond, size);
    let keep = b.eval(Op::IntAnd, size, &[t, mask]);
    let inverse = b.eval(Op::IntNot, size, &[mask]);
    let drop = b.eval(Op::IntAnd, size, &[f, inverse]);
    b.eval(Op::IntOr, size, &[keep, drop])
}
