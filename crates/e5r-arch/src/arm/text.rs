//! ARM text output, formatted the way llvm-objdump formats it.
//!
//! Matching the oracle exactly is what makes the parity gate a string
//! comparison instead of a judgment call, so the quirks are copied rather than
//! tidied: a data-processing immediate prints as a signed decimal, a `movw`
//! immediate as hex, and a memory displacement as whichever LLVM's printer for
//! that addressing mode chose.

use std::fmt::Write;

use crate::insn::{AddrMode, Extend, Insn, Mem, Operand, Reg, RegClass, Shift, Width};

use super::COND_NAMES;

/// Register names, where three of the sixteen have a role name instead.
pub(crate) fn reg(out: &mut String, r: Reg) {
    match r.class {
        RegClass::Sp => out.push_str("sp"),
        RegClass::Pc => out.push_str("pc"),
        RegClass::Gpr if r.num == 14 => out.push_str("lr"),
        RegClass::Gpr => {
            let _ = write!(out, "r{}", r.num);
        }
        RegClass::Vec => {
            let prefix = match r.width {
                Width::W128 => 'q',
                Width::W64 => 'd',
                _ => 's',
            };
            let _ = write!(out, "{prefix}{}", r.num);
        }
        _ => out.push('?'),
    }
}

/// A register list, `{r4, r5, lr}` or a run of VFP registers.
fn list(out: &mut String, v: u32) {
    out.push('{');
    let mut first = true;
    let mut sep = |out: &mut String| {
        if !first {
            out.push_str(", ");
        }
        first = false;
    };
    match v >> 28 {
        0 => {
            for n in 0..16 {
                if v >> n & 1 == 1 {
                    sep(out);
                    reg(out, super::reg(n));
                }
            }
        }
        tag => {
            let (base, count) = ((v >> 8) & 0xff, v & 0xff);
            for n in 0..count {
                sep(out);
                reg(out, super::vreg(base + n, tag == 2));
            }
        }
    }
    out.push('}');
}

/// A shift that follows a register operand. A `ror` by zero is `rrx`.
fn shift(out: &mut String, sh: Shift, n: u8) {
    if sh == Shift::Ror && n == 0 {
        out.push_str(", rrx");
    } else {
        let _ = write!(out, ", {} #{n}", sh.as_str());
    }
}

fn mem(out: &mut String, m: Mem) {
    let flags = m.seg.map_or(0, |r| r.num);
    let decimal = flags & DEC != 0;
    let force = flags & ALW != 0;
    let neg_zero = flags & NEG != 0;
    let disp = |out: &mut String, v: i64| {
        if neg_zero {
            out.push_str(if decimal { "#-0" } else { "#-0x0" });
        } else if decimal {
            let _ = write!(out, "#{v}");
        } else if v < 0 {
            let _ = write!(out, "#-{:#x}", v.unsigned_abs());
        } else {
            let _ = write!(out, "#{v:#x}");
        }
    };
    out.push('[');
    if let Some(b) = m.base {
        reg(out, b);
    }
    let index = |out: &mut String| {
        if let Some((ix, _, amount)) = m.index {
            out.push_str(", ");
            reg(out, ix);
            if amount != 0 {
                let _ = write!(out, ", lsl #{amount}");
            }
            true
        } else {
            false
        }
    };
    match m.mode {
        AddrMode::PostIndex => {
            out.push(']');
            if !index(out) {
                out.push_str(", ");
                disp(out, m.disp);
            }
        }
        AddrMode::Offset => {
            if !index(out) && (m.disp != 0 || force || neg_zero) {
                out.push_str(", ");
                disp(out, m.disp);
            }
            out.push(']');
        }
        AddrMode::PreIndex => {
            if !index(out) {
                out.push_str(", ");
                disp(out, m.disp);
            }
            out.push_str("]!");
        }
    }
}

/// A VFP literal in LLVM's `%e` spelling, which is six fraction digits and at
/// least two exponent digits.
fn fp_text(bits: u64) -> String {
    let s = format!("{:.6e}", f64::from_bits(bits));
    match s.split_once('e') {
        Some((m, e)) => {
            let exp: i32 = e.parse().unwrap_or(0);
            format!("{m}e{}{:02}", if exp < 0 { '-' } else { '+' }, exp.abs())
        }
        None => s,
    }
}

fn operand(out: &mut String, op: &Operand) {
    match op {
        Operand::Reg(r) => reg(out, *r),
        Operand::Shifted(r, sh, n) => {
            reg(out, *r);
            shift(out, *sh, *n);
        }
        Operand::Extended(r, ext, n) => {
            reg(out, *r);
            let _ = write!(out, ", {} #{n}", ext.as_str());
        }
        Operand::Imm(v) => {
            if *v < 0 {
                let _ = write!(out, "#-{:#x}", v.unsigned_abs());
            } else {
                let _ = write!(out, "#{v:#x}");
            }
        }
        Operand::UImm(v) => {
            let _ = write!(out, "#{v:#x}");
        }
        Operand::Count(v) => {
            let _ = write!(out, "#{v}");
        }
        Operand::ShiftOp(sh, n) => {
            let _ = write!(out, "{} #{n}", sh.as_str());
        }
        Operand::Name(n) => out.push_str(n),
        Operand::FpImm(b) => {
            let _ = write!(out, "#{}", fp_text(*b));
        }
        Operand::Addr(a) => {
            let _ = write!(out, "{:#x}", a.get());
        }
        Operand::Mem(m) => mem(out, *m),
        Operand::Cond(c) => out.push_str(COND_NAMES[(c.0 & 15) as usize]),
        Operand::Sys(v) => list(out, *v),
        // AArch64 lane spellings, which no ARM encoding here produces.
        Operand::Vector(..) | Operand::VectorLane(..) | Operand::VectorList(..) => out.push('?'),
    }
}

/// Render a whole instruction as `mnemonic\toperands`.
pub fn format(i: &Insn) -> String {
    let mut out = String::with_capacity(32);
    out.push_str(i.mnemonic);
    for (n, op) in i.operands().iter().enumerate() {
        out.push_str(if n == 0 { "\t" } else { ", " });
        operand(&mut out, op);
    }
    out
}

/// The segment field is dead on ARM, so it carries the two things [`Mem`] has
/// nowhere else to say, both of them the addressing mode's rather than the
/// instruction's: whether the displacement prints in decimal, and whether a
/// zero one prints at all. `Seg` is an x86 bank, so the marker can never be
/// mistaken for a real ARM operand.
const DEC: u8 = 1;
const ALW: u8 = 2;
const NEG: u8 = 4;

fn mark(mut m: Mem, flags: u8) -> Mem {
    m.seg = Some(Reg {
        class: RegClass::Seg,
        num: m.seg.map_or(0, |r| r.num) | flags,
        width: Width::W32,
    });
    m
}

/// The eight-bit and scaled displacements, which print in decimal.
pub(crate) fn decimal(m: Mem) -> Mem {
    mark(m, DEC)
}

/// The literal loads, which print `[pc, #0x0]` rather than `[pc]`.
pub(crate) fn always(m: Mem) -> Mem {
    mark(m, ALW)
}

/// A subtracting offset of zero, which a listing spells `#-0`: the sign is in
/// the encoding and survives the arithmetic that loses it.
pub(crate) fn minus_zero(m: Mem) -> Mem {
    mark(m, NEG)
}

/// An index register with no scale and no sign, the only indexed form the
/// shared [`Mem`] can hold: its `Extend` cannot say `lsr` and it cannot say
/// subtract, so the decoders decline those rather than print them wrong.
pub(crate) fn index(rm: Reg, amount: u8) -> Option<(Reg, Extend, u8)> {
    Some((rm, Extend::Lsl, amount))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::insn::Flow;
    use e5r_core::Addr;

    #[test]
    fn role_registers_print_by_name() {
        let mut s = String::new();
        for n in [3, 12, 13, 14, 15] {
            reg(&mut s, super::super::reg(n));
            s.push(' ');
        }
        assert_eq!(s, "r3 r12 sp lr pc ");
    }

    #[test]
    fn a_ror_by_zero_is_rrx() {
        let mut s = String::new();
        shift(&mut s, Shift::Ror, 0);
        shift(&mut s, Shift::Ror, 3);
        assert_eq!(s, ", rrx, ror #3");
    }

    #[test]
    fn register_lists_expand() {
        let mut s = String::new();
        list(&mut s, 0x5030);
        assert_eq!(s, "{r4, r5, r12, lr}");
        let mut v = String::new();
        list(&mut v, 2 << 28 | 8 << 8 | 3);
        assert_eq!(v, "{d8, d9, d10}");
    }

    #[test]
    fn displacements_follow_the_addressing_mode() {
        let base = Mem::base_disp(super::super::reg(1), -4, 4);
        let mut hex = String::new();
        mem(&mut hex, base);
        assert_eq!(hex, "[r1, #-0x4]");
        let mut dec = String::new();
        mem(&mut dec, decimal(base));
        assert_eq!(dec, "[r1, #-4]");
    }

    #[test]
    fn fp_literals_match_llvms_spelling() {
        assert_eq!(fp_text(1.0f64.to_bits()), "1.000000e+00");
        assert_eq!(fp_text((-0.125f64).to_bits()), "-1.250000e-01");
    }

    #[test]
    fn targets_keep_their_prefix() {
        let mut i = Insn::new(Addr(0x1000), 4, "b", Flow::Branch(Addr(0x2000)));
        i.push(Operand::Addr(Addr(0x2000)));
        assert_eq!(format(&i), "b\t0x2000");
    }
}
