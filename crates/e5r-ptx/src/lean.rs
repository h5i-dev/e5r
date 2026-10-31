//! `Ptx.Module` values as Lean source. The mapping is one constructor per
//! AST variant, with names and integers copied through.

use crate::ast::*;
use std::fmt::Write;

fn string(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn int(v: i128) -> String {
    if v < 0 {
        format!("({v})")
    } else {
        v.to_string()
    }
}

fn ty(t: Ty) -> String {
    format!(".{}", t.name())
}

fn dim(d: Dim) -> &'static str {
    match d {
        Dim::X => ".x",
        Dim::Y => ".y",
        Dim::Z => ".z",
    }
}

fn operand(o: &Operand) -> String {
    match o {
        Operand::Reg(r) => format!("(.reg {})", string(r)),
        Operand::Imm(v) => format!("(.imm {})", int(*v)),
        Operand::Sreg(s) => {
            let (c, d) = match s {
                Sreg::Tid(d) => ("tid", d),
                Sreg::Ntid(d) => ("ntid", d),
                Sreg::Ctaid(d) => ("ctaid", d),
                Sreg::Nctaid(d) => ("nctaid", d),
            };
            format!("(.sreg (.{c} {}))", dim(*d))
        }
    }
}

fn address(a: &Address) -> String {
    match a {
        Address::Reg(r, off) => format!("(.reg {} {})", string(r), int(off.unwrap_or(0))),
        Address::Param(n, off) => format!("(.param {} {})", string(n), int(off.unwrap_or(0))),
    }
}

fn cmp(c: CmpOp) -> String {
    format!(".{}", c.name())
}

fn instr(i: &Instr) -> String {
    let o = operand;
    let s = string;
    match i {
        Instr::Bin(b, t, d, x, y) => format!(".{} {} {} {} {}", b.lean(), ty(*t), s(d), o(x), o(y)),
        Instr::MadLo(t, d, a, b, c) => {
            format!(".madLo {} {} {} {} {}", ty(*t), s(d), o(a), o(b), o(c))
        }
        Instr::Not(t, d, a) => format!(".not {} {} {}", ty(*t), s(d), o(a)),
        Instr::Mov(t, d, a) => format!(".mov {} {} {}", ty(*t), s(d), o(a)),
        Instr::Setp(c, t, d, a, b) => {
            format!(".setp {} {} {} {} {}", cmp(*c), ty(*t), s(d), o(a), o(b))
        }
        Instr::Selp(t, d, a, b, p) => {
            format!(".selp {} {} {} {} {}", ty(*t), s(d), o(a), o(b), s(p))
        }
        Instr::Cvt(dt, st, d, a) => format!(".cvt {} {} {} {}", ty(*dt), ty(*st), s(d), o(a)),
        Instr::CvtaGlobal(d, a) => format!(".cvtaGlobal {} {}", s(d), o(a)),
        Instr::Ld(sp, t, d, a) => format!(".ld .{} {} {} {}", sp.name(), ty(*t), s(d), address(a)),
        Instr::St(sp, t, a, v) => format!(".st .{} {} {} {}", sp.name(), ty(*t), address(a), o(v)),
        Instr::Bra(u, l) => format!(".bra {u} {}", s(l)),
        Instr::Ret => ".ret".into(),
        Instr::Exit => ".exit".into(),
    }
}

/// A Lean module defining one `Kernel` per entry (named after it, in
/// guillemets) and `module : Module`, in namespace `ns`. `header` is put in
/// the leading comment verbatim.
pub fn module(m: &Module, ns: &str, header: &str) -> String {
    let mut s = String::new();
    writeln!(
        s,
        "/-\n{}\n-/\nimport Ptx.Syntax\n\nnamespace {ns}\nopen Ptx\n",
        header.trim_end()
    )
    .unwrap();
    for k in &m.kernels {
        writeln!(s, "def «{}» : Kernel where", k.name).unwrap();
        writeln!(s, "  name := {}", string(&k.name)).unwrap();
        let params: Vec<String> = k
            .params
            .iter()
            .map(|(n, t)| format!("({}, {})", string(n), ty(*t)))
            .collect();
        writeln!(s, "  params := [{}]", params.join(", ")).unwrap();
        let regs: Vec<String> = k
            .regs
            .iter()
            .map(|r| {
                let c = match r.count {
                    Some(n) => format!("(some {n})"),
                    None => "none".into(),
                };
                format!("⟨{}, {}, {c}⟩", ty(r.ty), string(&r.name))
            })
            .collect();
        writeln!(s, "  regs := [{}]", regs.join(", ")).unwrap();
        s.push_str("  body := [");
        for (i, st) in k.body.iter().enumerate() {
            let g = match &st.guard {
                None => "none".into(),
                Some(g) => format!("(some ⟨{}, {}⟩)", string(&g.pred), g.neg),
            };
            let sep = if i + 1 < k.body.len() { "," } else { "]" };
            write!(s, "\n    /- {i} -/ ⟨{g}, {}⟩{sep}", instr(&st.instr)).unwrap();
        }
        if k.body.is_empty() {
            s.push(']');
        }
        let labels: Vec<String> = k
            .labels
            .iter()
            .map(|(l, at)| format!("({}, {at})", string(l)))
            .collect();
        writeln!(s, "\n  labels := [{}]\n", labels.join(", ")).unwrap();
    }
    let names: Vec<String> = m.kernels.iter().map(|k| format!("«{}»", k.name)).collect();
    writeln!(
        s,
        "def module : Module where\n  version := {}\n  target := {}\n  addressSize := {}\n  kernels := [{}]\n\nend {ns}",
        string(&m.version),
        string(&m.target),
        m.address_size,
        names.join(", ")
    )
    .unwrap();
    s
}
