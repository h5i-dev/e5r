//! AArch64 text output, formatted the way objdump formats it.
//!
//! Matching objdump is not an aesthetic choice: it is what makes the G3 parity
//! gate a string comparison instead of a judgment call.

use std::fmt::Write;

use crate::insn::{AddrMode, Extend, Insn, Mem, Operand, Reg, RegClass, Width};

use super::cond_name;

/// How to render addresses and immediates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Style {
    /// Print branch targets as bare hex with no `0x`, which is what objdump
    /// does. Off, they print as `0x...` for a reader.
    pub objdump: bool,
}

/// Render a register.
fn reg(out: &mut String, r: Reg) {
    match r.class {
        RegClass::Sp => out.push_str(if r.width == Width::W64 { "sp" } else { "wsp" }),
        RegClass::Zr => out.push_str(if r.width == Width::W64 { "xzr" } else { "wzr" }),
        RegClass::Gpr => {
            let _ = write!(
                out,
                "{}{}",
                if r.width == Width::W64 { 'x' } else { 'w' },
                r.num
            );
        }
        RegClass::Vec => {
            let prefix = match r.width {
                Width::W8 => 'b',
                Width::W16 => 'h',
                Width::W32 => 's',
                Width::W64 => 'd',
                Width::W128 => 'q',
            };
            let _ = write!(out, "{prefix}{}", r.num);
        }
        RegClass::Sys => {
            let _ = write!(out, "s{}", r.num);
        }
        RegClass::Pc => out.push_str("pc"),
        // x86 banks, which AArch64 never produces.
        RegClass::GprHigh | RegClass::Seg => out.push('?'),
        RegClass::Flags => out.push_str("nzcv"),
    }
}

/// Plain immediates print as hex; negatives keep a minus rather than wrapping.
fn imm(out: &mut String, v: i64) {
    if v < 0 {
        let _ = write!(out, "#-{:#x}", v.unsigned_abs());
    } else {
        let _ = write!(out, "#{v:#x}");
    }
}

/// Counts, indices and displacements print as decimal.
fn count(out: &mut String, v: i64) {
    let _ = write!(out, "#{v}");
}

fn mem(out: &mut String, m: Mem, _style: Style) {
    out.push('[');
    if let Some(b) = m.base {
        reg(out, b);
    }
    match m.mode {
        AddrMode::PostIndex => {
            out.push_str("], ");
            count(out, m.disp);
        }
        AddrMode::Offset | AddrMode::PreIndex => {
            if let Some((ix, ext, amount)) = m.index {
                out.push_str(", ");
                reg(out, ix);
                // A plain lsl #0 is not printed.
                if ext == Extend::LslZero {
                    out.push_str(", lsl #0");
                } else if !(ext == Extend::Lsl && amount == 0) {
                    let _ = write!(out, ", {}", ext.as_str());
                    if amount != 0 {
                        let _ = write!(out, " #{amount}");
                    }
                }
            } else if m.disp != 0 {
                out.push_str(", ");
                count(out, m.disp);
            }
            out.push(']');
            if m.mode == AddrMode::PreIndex {
                out.push('!');
            }
        }
    }
}

/// Render one operand.
fn operand(out: &mut String, op: &Operand, style: Style) {
    match op {
        Operand::Reg(r) => reg(out, *r),
        Operand::Shifted(r, sh, n) => {
            reg(out, *r);
            let _ = write!(out, ", {} #{n}", sh.as_str());
        }
        Operand::Extended(r, ext, n) => {
            reg(out, *r);
            let _ = write!(out, ", {}", ext.as_str());
            if *n != 0 {
                let _ = write!(out, " #{n}");
            }
        }
        Operand::Imm(v) => imm(out, *v),
        Operand::UImm(v) => {
            let _ = write!(out, "#{v:#x}");
        }
        Operand::Count(v) => count(out, *v),
        Operand::ShiftOp(sh, n) => {
            let _ = write!(out, "{} #{n}", sh.as_str());
        }
        Operand::Name(n) => out.push_str(n),
        Operand::FpImm(b) => {
            let _ = write!(out, "#{}", fp_text(*b));
        }
        Operand::Vector(n, lanes) => {
            let _ = write!(out, "v{n}.{}", lanes.as_str());
        }
        Operand::VectorLane(n, width, index) => {
            let letter = match width {
                Width::W8 => 'b',
                Width::W16 => 'h',
                Width::W32 => 's',
                _ => 'd',
            };
            let _ = write!(out, "v{n}.{letter}[{index}]");
        }
        Operand::VectorList(first, count, lanes) => {
            out.push('{');
            for i in 0..*count {
                if i > 0 {
                    out.push_str(", ");
                }
                let _ = write!(out, "v{}.{}", (first + i) % 32, lanes.as_str());
            }
            out.push('}');
        }
        Operand::Addr(a) => {
            if style.objdump {
                let _ = write!(out, "{:x}", a.get());
            } else {
                let _ = write!(out, "{:#x}", a.get());
            }
        }
        Operand::Mem(m) => mem(out, *m, style),
        Operand::Cond(c) => out.push_str(cond_name(*c)),
        Operand::Sys(v) => out.push_str(&super::sysreg_name(*v)),
    }
}

/// A floating point literal in objdump's `%.18e` spelling.
fn fp_text(bits: u64) -> String {
    let v = f64::from_bits(bits);
    let s = format!("{v:.18e}");
    match s.split_once('e') {
        Some((m, e)) => {
            let exp: i32 = e.parse().unwrap_or(0);
            format!("{m}e{}{:02}", if exp < 0 { '-' } else { '+' }, exp.abs())
        }
        None => s,
    }
}

/// Render a whole instruction as `mnemonic\toperands`.
pub fn format(i: &Insn, style: Style) -> String {
    let mut out = String::with_capacity(32);
    out.push_str(i.mnemonic);
    for (n, op) in i.operands().iter().enumerate() {
        out.push_str(if n == 0 { "\t" } else { ", " });
        operand(&mut out, op, style);
    }
    out
}

/// A shift whose amount is zero and kind is `lsl` prints as a bare register,
/// which the decoder already arranges; this is here so the invariant is tested.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::insn::Flow;
    use e5r_core::Addr;

    #[test]
    fn registers_print_by_width() {
        let mut s = String::new();
        reg(&mut s, Reg::gpr(3, Width::W32));
        reg(&mut s, Reg::gpr(3, Width::W64));
        assert_eq!(s, "w3x3");
    }

    #[test]
    fn immediates_are_hex_and_counts_are_decimal() {
        let mut s = String::new();
        imm(&mut s, -16);
        assert_eq!(s, "#-0x10");
        let mut d = String::new();
        count(&mut d, -16);
        assert_eq!(d, "#-16");
    }

    #[test]
    fn post_index_moves_the_bracket() {
        let mut s = String::new();
        mem(
            &mut s,
            Mem {
                seg: None,
                base: Some(Reg {
                    class: RegClass::Sp,
                    num: 31,
                    width: Width::W64,
                }),
                index: None,
                disp: 16,
                mode: AddrMode::PostIndex,
                size: 8,
            },
            Style::default(),
        );
        assert_eq!(s, "[sp], #16");
    }

    #[test]
    fn fp_literals_match_objdumps_spelling() {
        assert_eq!(fp_text(1.0f64.to_bits()), "1.000000000000000000e+00");
        assert_eq!(fp_text(10.0f64.to_bits()), "1.000000000000000000e+01");
        assert_eq!(fp_text(0.125f64.to_bits()), "1.250000000000000000e-01");
        assert_eq!(fp_text((-2.0f64).to_bits()), "-2.000000000000000000e+00");
    }

    #[test]
    fn objdump_style_drops_the_hex_prefix_on_targets() {
        let mut i = Insn::new(Addr(0x1000), 4, "b", Flow::Branch(Addr(0x2000)));
        i.push(Operand::Addr(Addr(0x2000)));
        assert_eq!(format(&i, Style { objdump: true }), "b\t2000");
        assert_eq!(format(&i, Style::default()), "b\t0x2000");
    }
}
