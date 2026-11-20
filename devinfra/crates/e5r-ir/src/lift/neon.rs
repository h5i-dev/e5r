//! AArch64 SIMD lifting.
//!
//! A vector register is sixteen bytes of the register file and a lane is a
//! varnode inside it, so a lane operation is an ordinary operation on an
//! ordinary varnode. Nothing here needs values wider than the IR has: the
//! width lives in the addressing.
//!
//! A write through a 64-bit view clears the upper half of the register, which
//! is emitted rather than assumed, the same as the general registers.

use e5r_arch::{Insn, Lanes, Operand, RegClass, Width};

use crate::lift::aarch64::{flag_c, flag_n, flag_v, flag_z, gpr_offset, sp_offset, vec_offset};
use crate::lift::{Builder, Lifted};
use crate::op::{Op, Varnode};

/// Lane count and lane size in bytes.
fn shape(l: Lanes) -> (u64, u8) {
    match l {
        Lanes::B8 => (8, 1),
        Lanes::B16 => (16, 1),
        Lanes::H4 => (4, 2),
        Lanes::H8 => (8, 2),
        Lanes::S2 => (2, 4),
        Lanes::S4 => (4, 4),
        Lanes::D1 => (1, 8),
        Lanes::D2 => (2, 8),
        Lanes::Q1 => (1, 16),
    }
}

/// One lane of a vector register.
fn lane(num: u8, index: u64, size: u8) -> Varnode {
    Varnode::register(vec_offset(num) + index * size as u64, size)
}

/// The register a vector operand names, with its shape.
fn vector(op: &Operand) -> Option<(u8, u64, u8)> {
    match op {
        Operand::Vector(n, l) => {
            let (count, size) = shape(*l);
            Some((*n, count, size))
        }
        Operand::Reg(r) if r.class == RegClass::Vec => {
            let size = match r.width {
                Width::W8 => 1,
                Width::W16 => 2,
                Width::W32 => 4,
                Width::W64 => 8,
                Width::W128 => 16,
            };
            Some((r.num, 1, size))
        }
        _ => None,
    }
}

/// Clear the bytes of a vector register above `bytes`, which a write through a
/// narrower view performs.
fn clear_above(b: &mut Builder, num: u8, bytes: u64) {
    let mut at = bytes;
    while at < 16 {
        // Aligned pieces only: a write that crosses an eight-byte boundary is
        // two writes as far as the dataflow is concerned.
        let chunk = aligned_chunk(at, 16);
        b.emit(
            Op::Copy,
            Some(Varnode::register(vec_offset(num) + at, chunk)),
            &[Varnode::constant(0, chunk)],
        );
        at += chunk as u64;
    }
}

/// True when this instruction is one the SIMD lifter handles.
///
/// Memory transfers are not among them: a vector load is still a load, and the
/// ordinary path handles it by moving the register in pieces.
pub fn handles(i: &Insn) -> bool {
    let m = i.mnemonic;
    if m.starts_with("ld") || m.starts_with("st") || m.starts_with("prf") {
        return false;
    }
    i.operands().iter().any(|o| {
        matches!(
            o,
            Operand::Vector(..) | Operand::VectorLane(..) | Operand::VectorList(..)
        ) || matches!(o, Operand::Reg(r) if r.class == RegClass::Vec)
    })
}

/// Lift one SIMD instruction, or say it is not modelled.
pub fn lift(mut b: Builder, i: &Insn) -> Lifted {
    let ops = i.operands();
    match i.mnemonic {
        "movi" | "mvni" => {
            let Some((d, count, size)) = ops.first().and_then(vector) else {
                return b.unimplemented();
            };
            let Some(raw) = immediate(ops) else {
                return b.unimplemented();
            };
            let value = if i.mnemonic == "mvni" { !raw } else { raw };
            for n in 0..count {
                b.emit(
                    Op::Copy,
                    Some(lane(d, n, size)),
                    &[Varnode::constant(value, size)],
                );
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "add" | "sub" | "mul" | "and" | "orr" | "eor" | "bic" | "orn" | "umax" | "umin"
        | "smax" | "smin" => {
            let (Some((d, count, size)), Some((x, ..)), Some((y, ..))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
            ) else {
                return b.unimplemented();
            };
            for n in 0..count {
                let a = lane(x, n, size);
                let c = lane(y, n, size);
                let r = match i.mnemonic {
                    "add" => b.eval(Op::IntAdd, size, &[a, c]),
                    "sub" => b.eval(Op::IntSub, size, &[a, c]),
                    "mul" => b.eval(Op::IntMul, size, &[a, c]),
                    "and" => b.eval(Op::IntAnd, size, &[a, c]),
                    "orr" => b.eval(Op::IntOr, size, &[a, c]),
                    "eor" => b.eval(Op::IntXor, size, &[a, c]),
                    "bic" => {
                        let inverted = b.eval(Op::IntNot, size, &[c]);
                        b.eval(Op::IntAnd, size, &[a, inverted])
                    }
                    "orn" => {
                        let inverted = b.eval(Op::IntNot, size, &[c]);
                        b.eval(Op::IntOr, size, &[a, inverted])
                    }
                    // The maxima and minima pick a lane, which is a select on
                    // the comparison rather than an operation of its own.
                    _ => {
                        let op = match i.mnemonic {
                            "umax" => Op::IntLess,
                            "umin" => Op::IntLess,
                            "smax" => Op::IntSLess,
                            _ => Op::IntSLess,
                        };
                        let takes_second = matches!(i.mnemonic, "umax" | "smax");
                        let less = b.eval(op, 1, &[a, c]);
                        let (t, f) = if takes_second { (c, a) } else { (a, c) };
                        select(&mut b, less, t, f, size)
                    }
                };
                b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "mla" | "mls" => {
            let (Some((d, count, size)), Some((x, ..)), Some((y, ..))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
            ) else {
                return b.unimplemented();
            };
            for n in 0..count {
                let product = b.eval(Op::IntMul, size, &[lane(x, n, size), lane(y, n, size)]);
                let acc = lane(d, n, size);
                let op = if i.mnemonic == "mla" {
                    Op::IntAdd
                } else {
                    Op::IntSub
                };
                let r = b.eval(op, size, &[acc, product]);
                b.emit(Op::Copy, Some(acc), &[r]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "neg" | "not" | "mvn" | "abs" => {
            let (Some((d, count, size)), Some((x, xc, xs))) =
                (ops.first().and_then(vector), ops.get(1).and_then(vector))
            else {
                return b.unimplemented();
            };
            let (count, size) = if count == 1 && xc > 1 {
                (xc, xs)
            } else {
                (count, size)
            };
            for n in 0..count {
                let a = lane(x, n, size);
                let r = match i.mnemonic {
                    "neg" => b.eval(Op::IntNegate, size, &[a]),
                    "abs" => {
                        let negated = b.eval(Op::IntNegate, size, &[a]);
                        let negative = b.eval(Op::IntSLess, 1, &[a, Varnode::constant(0, size)]);
                        select(&mut b, negative, negated, a, size)
                    }
                    _ => b.eval(Op::IntNot, size, &[a]),
                };
                b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        // The bitwise selects: each bit of the destination comes from one of
        // two registers according to a mask.
        "bsl" | "bit" | "bif" => {
            let (Some((d, count, size)), Some((x, ..)), Some((y, ..))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
            ) else {
                return b.unimplemented();
            };
            let bytes = count * size as u64;
            for at in (0..bytes).step_by(8) {
                let chunk = if bytes - at >= 8 {
                    8u8
                } else {
                    (bytes - at) as u8
                };
                let dst = Varnode::register(vec_offset(d) + at, chunk);
                let a = Varnode::register(vec_offset(x) + at, chunk);
                let c = Varnode::register(vec_offset(y) + at, chunk);
                // `bsl` selects with the destination as the mask; `bit` and
                // `bif` use the third register, inverted for `bif`.
                let (mask, from_mask, other) = match i.mnemonic {
                    "bsl" => (dst, a, c),
                    "bit" => (c, a, dst),
                    _ => {
                        let inverted = b.eval(Op::IntNot, chunk, &[c]);
                        (inverted, a, dst)
                    }
                };
                let keep = b.eval(Op::IntAnd, chunk, &[from_mask, mask]);
                let inverse = b.eval(Op::IntNot, chunk, &[mask]);
                let rest = b.eval(Op::IntAnd, chunk, &[other, inverse]);
                let r = b.eval(Op::IntOr, chunk, &[keep, rest]);
                b.emit(Op::Copy, Some(dst), &[r]);
            }
            if bytes == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "cmeq" | "cmgt" | "cmge" | "cmhi" | "cmhs" => {
            let (Some((d, count, size)), Some((x, ..)), Some((y, ..))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
            ) else {
                return b.unimplemented();
            };
            for n in 0..count {
                let a = lane(x, n, size);
                let c = lane(y, n, size);
                let truth = match i.mnemonic {
                    "cmeq" => b.eval(Op::IntEqual, 1, &[a, c]),
                    "cmgt" => b.eval(Op::IntSLess, 1, &[c, a]),
                    "cmge" => b.eval(Op::IntSLessEqual, 1, &[c, a]),
                    "cmhi" => b.eval(Op::IntLess, 1, &[c, a]),
                    _ => b.eval(Op::IntLessEqual, 1, &[c, a]),
                };
                // A true comparison sets every bit of the lane.
                let wide = if size == 1 {
                    truth
                } else {
                    b.eval(Op::IntZExt, size, &[truth])
                };
                let r = b.eval(Op::IntNegate, size, &[wide]);
                b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "addv" | "uaddlv" | "saddlv" => {
            let Some((x, count, size)) = ops.get(1).and_then(vector) else {
                return b.unimplemented();
            };
            let Some(Operand::Reg(dest)) = ops.first() else {
                return b.unimplemented();
            };
            let wide = if i.mnemonic == "addv" { size } else { size * 2 };
            let mut acc = if wide == size {
                lane(x, 0, size)
            } else {
                let op = if i.mnemonic == "saddlv" {
                    Op::IntSExt
                } else {
                    Op::IntZExt
                };
                b.eval(op, wide, &[lane(x, 0, size)])
            };
            for n in 1..count {
                let next = if wide == size {
                    lane(x, n, size)
                } else {
                    let op = if i.mnemonic == "saddlv" {
                        Op::IntSExt
                    } else {
                        Op::IntZExt
                    };
                    b.eval(op, wide, &[lane(x, n, size)])
                };
                acc = b.eval(Op::IntAdd, wide, &[acc, next]);
            }
            b.emit(Op::Copy, Some(lane(dest.num, 0, wide)), &[acc]);
            clear_above(&mut b, dest.num, wide as u64);
            b.finish(true)
        }
        "addp" => {
            // The scalar form folds a pair; the vector form interleaves two
            // registers pairwise.
            match (ops.first(), ops.get(1), ops.get(2)) {
                (Some(Operand::Reg(d)), Some(src), None) => {
                    let Some((x, count, size)) = vector(src) else {
                        return b.unimplemented();
                    };
                    if count != 2 {
                        return b.unimplemented();
                    }
                    let sum = b.eval(Op::IntAdd, size, &[lane(x, 0, size), lane(x, 1, size)]);
                    b.emit(Op::Copy, Some(lane(d.num, 0, size)), &[sum]);
                    clear_above(&mut b, d.num, size as u64);
                    b.finish(true)
                }
                (Some(dst), Some(a), Some(c)) => {
                    let (Some((d, count, size)), Some((x, ..)), Some((y, ..))) =
                        (vector(dst), vector(a), vector(c))
                    else {
                        return b.unimplemented();
                    };
                    let half = count / 2;
                    let mut values = Vec::new();
                    for n in 0..half {
                        values.push(b.eval(
                            Op::IntAdd,
                            size,
                            &[lane(x, n * 2, size), lane(x, n * 2 + 1, size)],
                        ));
                    }
                    for n in 0..half {
                        values.push(b.eval(
                            Op::IntAdd,
                            size,
                            &[lane(y, n * 2, size), lane(y, n * 2 + 1, size)],
                        ));
                    }
                    for (n, v) in values.into_iter().enumerate() {
                        b.emit(Op::Copy, Some(lane(d, n as u64, size)), &[v]);
                    }
                    if count * size as u64 == 8 {
                        clear_above(&mut b, d, 8);
                    }
                    b.finish(true)
                }
                _ => b.unimplemented(),
            }
        }
        "dup" => {
            let Some((d, count, size)) = ops.first().and_then(vector) else {
                return b.unimplemented();
            };
            let value = match ops.get(1) {
                Some(Operand::Reg(r)) if r.class != RegClass::Vec => {
                    Varnode::register(gpr_offset(r.num), size)
                }
                Some(Operand::VectorLane(n, _, index)) => lane(*n, *index as u64, size),
                _ => return b.unimplemented(),
            };
            for n in 0..count {
                b.emit(Op::Copy, Some(lane(d, n, size)), &[value]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "umov" | "smov" => {
            let (Some(Operand::Reg(d)), Some(Operand::VectorLane(n, w, index))) =
                (ops.first(), ops.get(1))
            else {
                return b.unimplemented();
            };
            let size = match w {
                Width::W8 => 1,
                Width::W16 => 2,
                Width::W32 => 4,
                _ => 8,
            };
            let value = lane(*n, *index as u64, size);
            let dest_size = if d.width == Width::W64 { 8 } else { 4 };
            let widened = if size == dest_size {
                value
            } else if i.mnemonic == "smov" {
                b.eval(Op::IntSExt, dest_size, &[value])
            } else {
                b.eval(Op::IntZExt, dest_size, &[value])
            };
            b.emit(
                Op::Copy,
                Some(Varnode::register(gpr_offset(d.num), dest_size)),
                &[widened],
            );
            if dest_size == 4 {
                b.emit(
                    Op::Copy,
                    Some(Varnode::register(gpr_offset(d.num) + 4, 4)),
                    &[Varnode::constant(0, 4)],
                );
            }
            b.finish(true)
        }
        "fmov" => {
            // Only the forms that move bits between banks; the arithmetic ones
            // are floating point and not modelled.
            match (ops.first(), ops.get(1)) {
                (Some(Operand::Reg(d)), Some(Operand::Reg(s)))
                    if d.class != RegClass::Vec && s.class == RegClass::Vec =>
                {
                    let size = if d.width == Width::W64 { 8 } else { 4 };
                    let value = lane(s.num, 0, size);
                    b.emit(
                        Op::Copy,
                        Some(Varnode::register(gpr_offset(d.num), size)),
                        &[value],
                    );
                    if size == 4 {
                        b.emit(
                            Op::Copy,
                            Some(Varnode::register(gpr_offset(d.num) + 4, 4)),
                            &[Varnode::constant(0, 4)],
                        );
                    }
                    b.finish(true)
                }
                (Some(Operand::Reg(d)), Some(Operand::Reg(s)))
                    if d.class == RegClass::Vec && s.class != RegClass::Vec =>
                {
                    let size = if s.width == Width::W64 { 8 } else { 4 };
                    let src = if s.class == RegClass::Zr {
                        Varnode::constant(0, size)
                    } else {
                        Varnode::register(gpr_offset(s.num), size)
                    };
                    b.emit(Op::Copy, Some(lane(d.num, 0, size)), &[src]);
                    clear_above(&mut b, d.num, size as u64);
                    b.finish(true)
                }
                // A literal, which the encoding spells as a small set of
                // representable values.
                (Some(Operand::Reg(d)), Some(Operand::FpImm(bits))) if d.class == RegClass::Vec => {
                    let size = if d.width == Width::W64 { 8 } else { 4 };
                    let value = if size == 4 {
                        (f64::from_bits(*bits) as f32).to_bits() as u64
                    } else {
                        *bits
                    };
                    b.emit(
                        Op::Copy,
                        Some(lane(d.num, 0, size)),
                        &[Varnode::constant(value, size)],
                    );
                    clear_above(&mut b, d.num, size as u64);
                    b.finish(true)
                }
                (Some(Operand::Reg(d)), Some(Operand::Reg(s)))
                    if d.class == RegClass::Vec && s.class == RegClass::Vec =>
                {
                    let size = if d.width == Width::W64 { 8 } else { 4 };
                    let value = lane(s.num, 0, size);
                    b.emit(Op::Copy, Some(lane(d.num, 0, size)), &[value]);
                    clear_above(&mut b, d.num, size as u64);
                    b.finish(true)
                }
                _ => b.unimplemented(),
            }
        }
        "mov" | "ins" => {
            match (ops.first(), ops.get(1)) {
                // Inserting one lane, from a general register or another lane.
                (Some(Operand::VectorLane(d, w, index)), Some(src)) => {
                    let size = match w {
                        Width::W8 => 1,
                        Width::W16 => 2,
                        Width::W32 => 4,
                        _ => 8,
                    };
                    let value = match src {
                        Operand::Reg(r) if r.class == RegClass::Zr => Varnode::constant(0, size),
                        Operand::Reg(r) if r.class != RegClass::Vec => {
                            Varnode::register(gpr_offset(r.num), size)
                        }
                        Operand::VectorLane(n, _, from) => lane(*n, *from as u64, size),
                        _ => return b.unimplemented(),
                    };
                    // The rest of the register keeps what it held.
                    b.emit(Op::Copy, Some(lane(*d, *index as u64, size)), &[value]);
                    b.finish(true)
                }
                // A whole-register move between vector registers.
                (Some(a), Some(c)) if vector(a).is_some() && vector(c).is_some() => {
                    let ((d, count, size), (s, ..)) = (vector(a).unwrap(), vector(c).unwrap());
                    let bytes = count * size as u64;
                    let mut at = 0;
                    while at < bytes {
                        let chunk = if bytes - at >= 8 {
                            8
                        } else {
                            (bytes - at) as u8
                        };
                        b.emit(
                            Op::Copy,
                            Some(Varnode::register(vec_offset(d) + at, chunk)),
                            &[Varnode::register(vec_offset(s) + at, chunk)],
                        );
                        at += chunk as u64;
                    }
                    if bytes == 8 {
                        clear_above(&mut b, d, 8);
                    }
                    b.finish(true)
                }
                _ => b.unimplemented(),
            }
        }
        "ext" => {
            let (Some((d, count, size)), Some((x, ..)), Some((y, ..)), Some(Operand::Count(n))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
                ops.get(3),
            ) else {
                return b.unimplemented();
            };
            // Bytes taken from the top of the first register then the bottom of
            // the second, which is a rotation when the two are the same.
            let total = count * size as u64;
            let start = *n as u64;
            let mut bytes = Vec::new();
            for k in 0..total {
                let at = start + k;
                let source = if at < total {
                    Varnode::register(vec_offset(x) + at, 1)
                } else {
                    Varnode::register(vec_offset(y) + (at - total), 1)
                };
                bytes.push(b.eval(Op::Copy, 1, &[source]));
            }
            for (k, v) in bytes.into_iter().enumerate() {
                b.emit(
                    Op::Copy,
                    Some(Varnode::register(vec_offset(d) + k as u64, 1)),
                    &[v],
                );
            }
            if total == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "zip1" | "zip2" | "uzp1" | "uzp2" | "trn1" | "trn2" => {
            let (Some((d, count, size)), Some((x, ..)), Some((y, ..))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
            ) else {
                return b.unimplemented();
            };
            let mut picked: Vec<Varnode> = Vec::new();
            for n in 0..count {
                let (from, index) = match i.mnemonic {
                    "zip1" | "zip2" => {
                        let base = if i.mnemonic == "zip2" { count / 2 } else { 0 };
                        let half = base + n / 2;
                        if n % 2 == 0 { (x, half) } else { (y, half) }
                    }
                    "uzp1" | "uzp2" => {
                        let odd = u64::from(i.mnemonic == "uzp2");
                        if n < count / 2 {
                            (x, n * 2 + odd)
                        } else {
                            (y, (n - count / 2) * 2 + odd)
                        }
                    }
                    _ => {
                        let odd = u64::from(i.mnemonic == "trn2");
                        if n % 2 == 0 {
                            (x, n + odd)
                        } else {
                            (y, n - 1 + odd)
                        }
                    }
                };
                picked.push(b.eval(Op::Copy, size, &[lane(from, index, size)]));
            }
            for (n, v) in picked.into_iter().enumerate() {
                b.emit(Op::Copy, Some(lane(d, n as u64, size)), &[v]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        "shl" | "ushr" | "sshr" | "sli" | "sri" => {
            let (Some((d, count, size)), Some((x, ..)), Some(Operand::Count(n))) = (
                ops.first().and_then(vector),
                ops.get(1).and_then(vector),
                ops.get(2),
            ) else {
                return b.unimplemented();
            };
            let amount = Varnode::constant(*n as u64, 1);
            for k in 0..count {
                let a = lane(x, k, size);
                let r = match i.mnemonic {
                    "shl" => b.eval(Op::IntLeft, size, &[a, amount]),
                    "ushr" => b.eval(Op::IntRight, size, &[a, amount]),
                    "sshr" => b.eval(Op::IntSRight, size, &[a, amount]),
                    _ => return b.unimplemented(),
                };
                b.emit(Op::Copy, Some(lane(d, k, size)), &[r]);
            }
            if count * size as u64 == 8 {
                clear_above(&mut b, d, 8);
            }
            b.finish(true)
        }
        _ => float(b, i),
    }
}

/// The floating point instructions, scalar and packed.
///
/// The lane size comes from the register width for a scalar and from the
/// arrangement for a vector, and the operations are the IR's own: nothing here
/// approximates a rounding rule with integer arithmetic.
fn float(mut b: Builder, i: &Insn) -> Lifted {
    let ops = i.operands();
    let m = i.mnemonic;
    // The conversions from integers do not start with `f`, and everything
    // else here does.
    if !m.starts_with('f') && !matches!(m, "scvtf" | "ucvtf") {
        return b.unimplemented();
    }

    // The forms whose destination is a general register, or none at all.
    match m {
        "fcmp" | "fcmpe" => {
            let Some((x, _, size)) = ops.first().and_then(vector) else {
                return b.unimplemented();
            };
            let a = lane(x, 0, size);
            // The second operand is either a register or the literal zero.
            let c = match ops.get(1) {
                Some(o) if vector(o).is_some() => {
                    let (y, ..) = vector(o).unwrap();
                    lane(y, 0, size)
                }
                // The compare-with-zero form, which the decoder spells out.
                Some(Operand::FpImm(0)) | Some(Operand::Imm(0)) | Some(Operand::Name(_)) | None => {
                    Varnode::constant(0, size)
                }
                _ => return b.unimplemented(),
            };
            let less = b.eval(Op::FloatLess, 1, &[a, c]);
            let equal = b.eval(Op::FloatEqual, 1, &[a, c]);
            let nan_a = b.eval(Op::FloatNan, 1, &[a]);
            let nan_c = b.eval(Op::FloatNan, 1, &[c]);
            let unordered = b.eval(Op::BoolOr, 1, &[nan_a, nan_c]);
            let carry = b.eval(Op::BoolNot, 1, &[less]);
            b.emit(Op::Copy, Some(flag_n()), &[less]);
            b.emit(Op::Copy, Some(flag_z()), &[equal]);
            b.emit(Op::Copy, Some(flag_c()), &[carry]);
            b.emit(Op::Copy, Some(flag_v()), &[unordered]);
            return b.finish(true);
        }
        "fcvtzs" | "fcvtzu" => {
            let (Some(Operand::Reg(dest)), Some(src)) = (ops.first(), ops.get(1)) else {
                return b.unimplemented();
            };
            let Some((x, _, from)) = vector(src) else {
                return b.unimplemented();
            };
            let to = if dest.width == Width::W64 { 8u8 } else { 4 };
            let op = if m == "fcvtzs" {
                Op::FloatToInt
            } else {
                Op::FloatToUInt
            };
            let v = b.eval(op, to, &[lane(x, 0, from)]);
            b.emit(
                Op::Copy,
                Some(Varnode::register(gpr_offset(dest.num), to)),
                &[v],
            );
            if to == 4 {
                b.emit(
                    Op::Copy,
                    Some(Varnode::register(gpr_offset(dest.num) + 4, 4)),
                    &[Varnode::constant(0, 4)],
                );
            }
            return b.finish(true);
        }
        "scvtf" | "ucvtf" => {
            let (Some(dst), Some(Operand::Reg(src))) = (ops.first(), ops.get(1)) else {
                return b.unimplemented();
            };
            let Some((d, _, to)) = vector(dst) else {
                return b.unimplemented();
            };
            let from = if src.width == Width::W64 { 8u8 } else { 4 };
            let value = if src.class == RegClass::Zr {
                Varnode::constant(0, from)
            } else if src.class == RegClass::Vec {
                lane(src.num, 0, from)
            } else {
                Varnode::register(gpr_offset(src.num), from)
            };
            let op = if m == "scvtf" {
                Op::IntToFloat
            } else {
                Op::UIntToFloat
            };
            let v = b.eval(op, to, &[value]);
            b.emit(Op::Copy, Some(lane(d, 0, to)), &[v]);
            clear_above(&mut b, d, to as u64);
            return b.finish(true);
        }
        "fcvt" => {
            let (Some(dst), Some(src)) = (ops.first(), ops.get(1)) else {
                return b.unimplemented();
            };
            let (Some((d, _, to)), Some((x, _, from))) = (vector(dst), vector(src)) else {
                return b.unimplemented();
            };
            if !matches!(to, 4 | 8) || !matches!(from, 4 | 8) {
                return b.unimplemented();
            }
            let v = b.eval(Op::FloatConvert, to, &[lane(x, 0, from)]);
            b.emit(Op::Copy, Some(lane(d, 0, to)), &[v]);
            clear_above(&mut b, d, to as u64);
            return b.finish(true);
        }
        "fcsel" => {
            let (Some(dst), Some(a), Some(c), Some(Operand::Cond(cond))) =
                (ops.first(), ops.get(1), ops.get(2), ops.get(3))
            else {
                return b.unimplemented();
            };
            let (Some((d, _, size)), Some((x, ..)), Some((y, ..))) =
                (vector(dst), vector(a), vector(c))
            else {
                return b.unimplemented();
            };
            let taken = crate::lift::aarch64::condition_value(&mut b, cond.0);
            let r = select(&mut b, taken, lane(x, 0, size), lane(y, 0, size), size);
            b.emit(Op::Copy, Some(lane(d, 0, size)), &[r]);
            clear_above(&mut b, d, size as u64);
            return b.finish(true);
        }
        _ => {}
    }

    // The shape of the destination decides scalar or packed.
    let (d, count, size) = match ops.first().and_then(vector) {
        Some(v) => v,
        None => return b.unimplemented(),
    };
    if size != 4 && size != 8 {
        return b.unimplemented();
    }

    let binary = |m: &str| -> Option<Op> {
        Some(match m {
            "fadd" => Op::FloatAdd,
            "fsub" => Op::FloatSub,
            "fmul" => Op::FloatMul,
            "fdiv" => Op::FloatDiv,
            "fmax" | "fmaxnm" => Op::FloatMax,
            "fmin" | "fminnm" => Op::FloatMin,
            _ => return None,
        })
    };

    if let Some(op) = binary(m) {
        let (Some((x, ..)), Some((y, ..))) =
            (ops.get(1).and_then(vector), ops.get(2).and_then(vector))
        else {
            return b.unimplemented();
        };
        for n in 0..count {
            let r = b.eval(op, size, &[lane(x, n, size), lane(y, n, size)]);
            b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
        }
        clear_tail(&mut b, d, count * size as u64);
        return b.finish(true);
    }

    match m {
        "fneg" | "fabs" | "fsqrt" | "frintz" | "frintn" | "frintp" | "frintm" | "frinta" => {
            let Some((x, ..)) = ops.get(1).and_then(vector) else {
                return b.unimplemented();
            };
            let op = match m {
                "fneg" => Op::FloatNeg,
                "fabs" => Op::FloatAbs,
                "fsqrt" => Op::FloatSqrt,
                "frintz" => Op::FloatTrunc,
                "frintp" => Op::FloatCeil,
                "frintm" => Op::FloatFloor,
                _ => Op::FloatRound,
            };
            for n in 0..count {
                let r = b.eval(op, size, &[lane(x, n, size)]);
                b.emit(Op::Copy, Some(lane(d, n, size)), &[r]);
            }
            clear_tail(&mut b, d, count * size as u64);
            b.finish(true)
        }
        // The fused multiply-adds, which round once: `fmadd` is `a + n * m`,
        // and the other three negate one side or the other.
        "fmadd" | "fmsub" | "fnmadd" | "fnmsub" => {
            let (Some((x, ..)), Some((y, ..)), Some((a, ..))) = (
                ops.get(1).and_then(vector),
                ops.get(2).and_then(vector),
                ops.get(3).and_then(vector),
            ) else {
                return b.unimplemented();
            };
            let mut multiplicand = lane(x, 0, size);
            if matches!(m, "fmsub" | "fnmadd") {
                multiplicand = b.eval(Op::FloatNeg, size, &[multiplicand]);
            }
            let mut addend = lane(a, 0, size);
            if matches!(m, "fnmadd" | "fnmsub") {
                addend = b.eval(Op::FloatNeg, size, &[addend]);
            }
            let r = b.eval(
                Op::FloatMulAdd,
                size,
                &[multiplicand, lane(y, 0, size), addend],
            );
            b.emit(Op::Copy, Some(lane(d, 0, size)), &[r]);
            clear_tail(&mut b, d, size as u64);
            b.finish(true)
        }
        _ => b.unimplemented(),
    }
}

/// Clear whatever sits above a write of this many bytes.
fn clear_tail(b: &mut Builder, num: u8, bytes: u64) {
    if bytes < 16 {
        clear_above(b, num, bytes);
    }
}

/// A vector immediate, with any shift the encoding carries applied.
fn immediate(ops: &[Operand]) -> Option<u64> {
    let mut value = match ops.get(1)? {
        Operand::UImm(v) => *v,
        Operand::Imm(v) => *v as u64,
        _ => return None,
    };
    if let Some(Operand::ShiftOp(shift, amount)) = ops.get(2) {
        use e5r_arch::Shift;
        value = match shift {
            Shift::Lsl => value << amount,
            // Shifting in ones, which the modified immediate encoding uses.
            Shift::Msl => (value << amount) | ((1u64 << amount) - 1),
            _ => return None,
        };
    }
    Some(value)
}

/// A branch-free choice between two lanes.
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

/// The largest aligned piece that starts at `at` and ends by `limit`.
pub fn aligned_chunk(at: u64, limit: u64) -> u8 {
    let mut chunk = 8u64;
    while chunk > 1 && (at % chunk != 0 || at + chunk > limit) {
        chunk /= 2;
    }
    chunk as u8
}

/// A sixteen-byte load or store, which the ordinary path cannot express
/// because the IR carries no value that wide.
pub fn wide_transfer(b: &mut Builder, addr: Varnode, num: u8, bytes: u64, store: bool) {
    let mut at = 0;
    while at < bytes {
        let chunk = if bytes - at >= 8 {
            8
        } else {
            (bytes - at) as u8
        };
        let here = if at == 0 {
            addr
        } else {
            b.eval(Op::IntAdd, 8, &[addr, Varnode::constant(at, 8)])
        };
        let slot = Varnode::register(vec_offset(num) + at, chunk);
        if store {
            b.emit(Op::Store, None, &[here, slot]);
        } else {
            let value = b.eval(Op::Load, chunk, &[here]);
            b.emit(Op::Copy, Some(slot), &[value]);
        }
        at += chunk as u64;
    }
    if !store && bytes == 8 {
        clear_above(b, num, 8);
    }
}

/// The stack pointer, re-exported so the loads can reach it.
pub fn stack() -> Varnode {
    Varnode::register(sp_offset(), 8)
}
