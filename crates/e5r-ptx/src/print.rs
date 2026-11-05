//! Canonical PTX text for a parsed module. `ptxas` accepts it, and its tokens
//! equal the tokens of the source it was parsed from (`roundtrip`).

use crate::ast::*;
use std::fmt::Write;

fn dim(d: Dim) -> &'static str {
    match d {
        Dim::X => "x",
        Dim::Y => "y",
        Dim::Z => "z",
    }
}

/// `%tid.x` etc.
pub fn sreg(s: Sreg) -> String {
    let (b, d) = match s {
        Sreg::Tid(d) => ("%tid", d),
        Sreg::Ntid(d) => ("%ntid", d),
        Sreg::Ctaid(d) => ("%ctaid", d),
        Sreg::Nctaid(d) => ("%nctaid", d),
    };
    format!("{b}.{}", dim(d))
}

fn operand(o: &Operand) -> String {
    match o {
        Operand::Reg(r) => r.clone(),
        Operand::Imm(v) => v.to_string(),
        Operand::Sreg(s) => sreg(*s),
        Operand::Sym(n) => n.clone(),
        Operand::FImm(v, 32) => format!("0f{v:08X}"),
        Operand::FImm(v, _) => format!("0d{v:016X}"),
    }
}

fn mods(ftz: bool, sat: bool) -> String {
    format!(
        "{}{}",
        if ftz { ".ftz" } else { "" },
        if sat { ".sat" } else { "" }
    )
}

/// The rounding of a `cvt`, with its dot.
pub fn cvt_rnd(r: CvtRnd) -> String {
    match r {
        CvtRnd::None => String::new(),
        CvtRnd::F(m) => format!(".{}", m.name()),
        CvtRnd::I(m) => format!(".{}i", m.name()),
    }
}

fn address(a: &Address) -> String {
    let (n, off) = match a {
        Address::Reg(n, off) | Address::Param(n, off) => (n, off),
    };
    match off {
        None => format!("[{n}]"),
        Some(v) => format!("[{n}+{v}]"),
    }
}

/// One instruction, without guard or `;`.
pub fn instr(i: &Instr) -> String {
    let o = operand;
    match i {
        Instr::Bin(b, t, d, x, y) => {
            format!("{}.{} \t{d}, {}, {}", b.opcode(), t.name(), o(x), o(y))
        }
        Instr::MadLo(t, d, a, b, c) => {
            format!("mad.lo.{} \t{d}, {}, {}, {}", t.name(), o(a), o(b), o(c))
        }
        Instr::Bfi32(d, a, b, pos, len) => {
            format!("bfi.b32 \t{d}, {}, {}, {pos}, {len}", o(a), o(b))
        }
        Instr::Not(t, d, a) => format!("not.{} \t{d}, {}", t.name(), o(a)),
        Instr::Mov(t, d, a) => format!("mov.{} \t{d}, {}", t.name(), o(a)),
        Instr::Setp(c, t, d, a, b) => {
            format!("setp.{}.{} \t{d}, {}, {}", c.name(), t.name(), o(a), o(b))
        }
        Instr::Selp(t, d, a, b, p) => format!("selp.{} \t{d}, {}, {}, {p}", t.name(), o(a), o(b)),
        Instr::Cvt(dt, st, d, a) => format!("cvt.{}.{} \t{d}, {}", dt.name(), st.name(), o(a)),
        Instr::CvtaGlobal(d, a) => format!("cvta.to.global.u64 \t{d}, {}", o(a)),
        Instr::Ld(sp, t, d, a) => format!("ld.{}.{} \t{d}, {}", sp.name(), t.name(), address(a)),
        Instr::St(sp, t, a, v) => {
            format!("st.{}.{} \t{}, {}", sp.name(), t.name(), address(a), o(v))
        }
        Instr::Bra(false, l) => format!("bra \t{l}"),
        Instr::Bra(true, l) => format!("bra.uni \t{l}"),
        Instr::Ret => "ret".into(),
        Instr::Exit => "exit".into(),
        Instr::Atom(sp, op, t, d, a, b) => format!(
            "atom.{}.{}.{} \t{d}, {}, {}",
            sp.name(),
            op.name(),
            t.name(),
            address(a),
            o(b)
        ),
        Instr::Cas(sp, t, d, a, b, c) => format!(
            "atom.{}.cas.{} \t{d}, {}, {}, {}",
            sp.name(),
            t.name(),
            address(a),
            o(b),
            o(c)
        ),
        Instr::Red(sp, op, t, a, b) => format!(
            "red.{}.{}.{} \t{}, {}",
            sp.name(),
            op.name(),
            t.name(),
            address(a),
            o(b)
        ),
        Instr::Bar => "bar.sync \t0".into(),
        Instr::FBin(op, m, ftz, sat, t, d, a, b) => format!(
            "{}.{}{}.{} \t{d}, {}, {}",
            op.name(),
            m.name(),
            mods(*ftz, *sat),
            t.name(),
            o(a),
            o(b)
        ),
        Instr::Ffma(m, ftz, sat, t, d, a, b, c) => format!(
            "fma.{}{}.{} \t{d}, {}, {}, {}",
            m.name(),
            mods(*ftz, *sat),
            t.name(),
            o(a),
            o(b),
            o(c)
        ),
        Instr::Fsqrt(m, ftz, t, d, a) => {
            format!(
                "sqrt.{}{}.{} \t{d}, {}",
                m.name(),
                mods(*ftz, false),
                t.name(),
                o(a)
            )
        }
        Instr::Frcp(m, ftz, t, d, a) => {
            format!(
                "rcp.{}{}.{} \t{d}, {}",
                m.name(),
                mods(*ftz, false),
                t.name(),
                o(a)
            )
        }
        Instr::Fneg(ftz, t, d, a) => {
            format!("neg{}.{} \t{d}, {}", mods(*ftz, false), t.name(), o(a))
        }
        Instr::Fabs(ftz, t, d, a) => {
            format!("abs{}.{} \t{d}, {}", mods(*ftz, false), t.name(), o(a))
        }
        Instr::Fminmax(mx, ftz, nan, t, d, a, b) => format!(
            "{}{}{}.{} \t{d}, {}, {}",
            if *mx { "max" } else { "min" },
            mods(*ftz, false),
            if *nan { ".NaN" } else { "" },
            t.name(),
            o(a),
            o(b)
        ),
        Instr::Fsetp(c, ftz, t, p, a, b) => format!(
            "setp.{}{}.{} \t{p}, {}, {}",
            c.name(),
            mods(*ftz, false),
            t.name(),
            o(a),
            o(b)
        ),
        Instr::CvtF(dt, st, r, ftz, sat, d, a) => format!(
            "cvt{}{}.{}.{} \t{d}, {}",
            cvt_rnd(*r),
            mods(*ftz, *sat),
            dt.name(),
            st.name(),
            o(a)
        ),
    }
}

/// `.shared {.align a} .t name{[n]};`
pub fn shared_decl(d: &SharedDecl) -> String {
    let al = d.align.map_or(String::new(), |a| format!(".align {a} "));
    let n = d.count.map_or(String::new(), |n| format!("[{n}]"));
    format!(".shared {al}.{} {}{n};", d.elem, d.name)
}

/// The whole module.
pub fn module(m: &Module) -> String {
    let mut s = String::new();
    writeln!(s, ".version {}", m.version).unwrap();
    writeln!(s, ".target {}", m.target).unwrap();
    writeln!(s, ".address_size {}", m.address_size).unwrap();
    for k in &m.kernels {
        s.push('\n');
        let vis = if k.visible { ".visible " } else { "" };
        writeln!(s, "{vis}.entry {}(", k.name).unwrap();
        for (i, (n, t)) in k.params.iter().enumerate() {
            let sep = if i + 1 < k.params.len() { "," } else { "" };
            writeln!(s, "\t.param .{} {n}{sep}", t.name()).unwrap();
        }
        s.push_str(")\n{\n");
        for d in &k.decls {
            match *d {
                Decl::Reg(i) => {
                    let r = &k.regs[i];
                    match r.count {
                        Some(n) => {
                            writeln!(s, "\t.reg .{} \t{}<{n}>;", r.ty.name(), r.name).unwrap()
                        }
                        None => writeln!(s, "\t.reg .{} \t{};", r.ty.name(), r.name).unwrap(),
                    }
                }
                Decl::Shared(i) => writeln!(s, "\t{}", shared_decl(&k.shared[i])).unwrap(),
            }
        }
        s.push('\n');
        for (i, st) in k.body.iter().enumerate() {
            for (l, _) in k.labels.iter().filter(|(_, at)| *at == i) {
                writeln!(s, "{l}:").unwrap();
            }
            let g = match &st.guard {
                None => String::new(),
                Some(Guard { pred, neg: false }) => format!("@{pred} "),
                Some(Guard { pred, neg: true }) => format!("@!{pred} "),
            };
            writeln!(s, "\t{g}{};", instr(&st.instr)).unwrap();
        }
        for (l, _) in k.labels.iter().filter(|(_, at)| *at == k.body.len()) {
            writeln!(s, "{l}:").unwrap();
        }
        s.push_str("}\n");
    }
    s
}
