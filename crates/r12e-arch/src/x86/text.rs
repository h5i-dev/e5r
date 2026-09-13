//! x86 text output in Intel syntax, matching llvm-objdump.
//!
//! Intel rather than AT&T because llvm-objdump's Intel mode is unambiguous
//! about operand order and needs no size suffixes, which makes the G3 parity
//! gate a string comparison.

use std::fmt::Write;

use crate::insn::{Insn, Mem, Operand, Reg, RegClass, Width};

/// Formatting options.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Style {
    /// Reserved for a future AT&T mode. Intel is the only syntax today.
    pub att: bool,
}

const GPR64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const GPR32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];
const GPR16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];
const GPR8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];
const GPR8H: [&str; 4] = ["ah", "ch", "dh", "bh"];
const SEG: [&str; 6] = ["es", "cs", "ss", "ds", "fs", "gs"];

/// Render a register.
fn reg(out: &mut String, r: Reg) {
    let n = (r.num & 15) as usize;
    match r.class {
        RegClass::Gpr => out.push_str(match r.width {
            Width::W8 => GPR8[n],
            Width::W16 => GPR16[n],
            Width::W32 => GPR32[n],
            _ => GPR64[n],
        }),
        RegClass::GprHigh => out.push_str(GPR8H[(r.num & 3) as usize]),
        RegClass::Vec => {
            let _ = write!(out, "xmm{n}");
        }
        RegClass::Seg => out.push_str(SEG[(r.num as usize).min(5)]),
        RegClass::Pc => out.push_str("rip"),
        RegClass::Sys => {
            let _ = write!(out, "cr{n}");
        }
        RegClass::Sp => out.push_str("rsp"),
        RegClass::Zr => out.push('0'),
        RegClass::Flags => out.push_str("eflags"),
    }
}

/// The `dword ptr` style prefix llvm prints when the size is not implied by a
/// register operand.
fn size_hint(size: u64) -> &'static str {
    match size {
        1 => "byte ptr ",
        2 => "word ptr ",
        4 => "dword ptr ",
        8 => "qword ptr ",
        16 => "xmmword ptr ",
        _ => "",
    }
}

fn mem(out: &mut String, m: Mem, _needs_size: bool) {
    // llvm prints the size on every real memory access. A size of zero means
    // the operand is an address, not an access, which is `lea`.
    out.push_str(size_hint(m.size));
    if let Some(s) = m.seg {
        reg(out, s);
        out.push(':');
    }
    out.push('[');
    let mut wrote = false;
    // RIP-relative displacements are resolved at decode time, so the number
    // shown is the address, not an offset.
    if let Some(b) = m.base {
        reg(out, b);
        wrote = true;
    }
    if let Some((ix, _, scale)) = m.index {
        if wrote {
            out.push_str(" + ");
        }
        if scale > 0 {
            let _ = write!(out, "{}*", 1u32 << scale);
        }
        reg(out, ix);
        wrote = true;
    }
    if m.disp != 0 || !wrote {
        if !wrote {
            let _ = write!(out, "{:#x}", m.disp);
        } else if m.disp > 0 {
            let _ = write!(out, " + {:#x}", m.disp);
        } else {
            let _ = write!(out, " - {:#x}", m.disp.unsigned_abs());
        }
    }
    out.push(']');
}

/// Render one operand. `needs_size` is set when no register operand implies it.
fn operand(out: &mut String, op: &Operand, needs_size: bool) {
    match op {
        Operand::Reg(r) => reg(out, *r),
        Operand::Imm(v) => {
            if *v < 0 {
                let _ = write!(out, "-{:#x}", v.unsigned_abs());
            } else {
                let _ = write!(out, "{v:#x}");
            }
        }
        Operand::UImm(v) => {
            let _ = write!(out, "{v:#x}");
        }
        Operand::Count(v) => {
            let _ = write!(out, "{v:#x}");
        }
        Operand::Addr(a) => {
            let _ = write!(out, "{:#x}", a.get());
        }
        Operand::Mem(m) => mem(out, *m, needs_size),
        Operand::Name(n) => out.push_str(n),
        Operand::Cond(_) | Operand::Shifted(..) | Operand::Extended(..) | Operand::ShiftOp(..) => {}
        Operand::Sys(v) => {
            let _ = write!(out, "{v:#x}");
        }
        Operand::FpImm(b) => {
            let _ = write!(out, "{}", f64::from_bits(*b));
        }
    }
}

/// Render a whole instruction as `mnemonic\toperands`.
pub fn format(i: &Insn, _style: Style) -> String {
    format_with_prefix(i, i.prefix)
}

/// Render with a repeat prefix, which llvm prints as its own token followed by
/// two tabs.
pub fn format_with_prefix(i: &Insn, prefix: Option<&str>) -> String {
    let mut out = String::with_capacity(32);
    if let Some(p) = prefix {
        out.push_str(p);
        out.push_str("\t\t");
    }
    out.push_str(i.mnemonic);
    // A memory operand needs an explicit size only when no register operand
    // gives it away.
    let has_reg = i.operands().iter().any(|o| matches!(o, Operand::Reg(_)));
    for (n, op) in i.operands().iter().enumerate() {
        out.push_str(if n == 0 { "\t" } else { ", " });
        operand(&mut out, op, !has_reg);
    }
    out
}
