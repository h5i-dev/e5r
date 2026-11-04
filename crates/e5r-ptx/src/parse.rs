//! Parser and type checker for the subset. Anything outside it is an error
//! naming the line, never a best-effort reading.

use crate::ast::*;
use crate::lex::{Tok, Token, lex};
use crate::print;
use std::collections::HashMap;

struct P {
    toks: Vec<Token>,
    pos: usize,
}

type R<T> = Result<T, String>;

impl P {
    fn line(&self) -> usize {
        self.toks
            .get(self.pos)
            .or(self.toks.last())
            .map_or(0, |t| t.line)
    }

    fn err<T>(&self, msg: impl std::fmt::Display) -> R<T> {
        Err(format!("line {}: {msg}", self.line()))
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.tok)
    }

    fn next(&mut self) -> R<Tok> {
        match self.toks.get(self.pos) {
            Some(t) => {
                self.pos += 1;
                Ok(t.tok.clone())
            }
            None => self.err("unexpected end of input"),
        }
    }

    fn is_punct(&self, c: char) -> bool {
        self.peek() == Some(&Tok::Punct(c))
    }

    fn punct(&mut self, c: char) -> R<()> {
        match self.next()? {
            Tok::Punct(d) if d == c => Ok(()),
            t => {
                self.pos -= 1;
                self.err(format!("expected '{c}', found {t:?}"))
            }
        }
    }

    fn word(&mut self) -> R<String> {
        match self.next()? {
            Tok::Word(w) => Ok(w),
            t => {
                self.pos -= 1;
                self.err(format!("expected a name, found {t:?}"))
            }
        }
    }

    fn keyword(&mut self, k: &str) -> R<()> {
        let w = self.word()?;
        if w == k {
            Ok(())
        } else {
            self.pos -= 1;
            self.err(format!("expected {k}, found {w}"))
        }
    }

    fn int(&mut self) -> R<i128> {
        let neg = if self.is_punct('-') {
            self.pos += 1;
            true
        } else {
            false
        };
        match self.next()? {
            // `-0` would print as `0` and fail the token round trip.
            Tok::Int(0) if neg => {
                self.pos -= 1;
                self.err("negative zero")
            }
            Tok::Int(v) => Ok(if neg { -v } else { v }),
            t => {
                self.pos -= 1;
                self.err(format!("expected an integer, found {t:?}"))
            }
        }
    }

    fn ty_directive(&mut self) -> R<Ty> {
        let w = self.word()?;
        match w.strip_prefix('.').and_then(Ty::from_name) {
            Some(t) => Ok(t),
            None => {
                self.pos -= 1;
                self.err(format!("unsupported type {w}"))
            }
        }
    }
}

fn sreg(w: &str) -> Option<Sreg> {
    let (base, d) = w.rsplit_once('.')?;
    let d = match d {
        "x" => Dim::X,
        "y" => Dim::Y,
        "z" => Dim::Z,
        _ => return None,
    };
    Some(match base {
        "%tid" => Sreg::Tid(d),
        "%ntid" => Sreg::Ntid(d),
        "%ctaid" => Sreg::Ctaid(d),
        "%nctaid" => Sreg::Nctaid(d),
        _ => return None,
    })
}

/// Parse and type-check a module.
pub fn parse_module(src: &str) -> R<Module> {
    let mut p = P {
        toks: lex(src)?,
        pos: 0,
    };
    p.keyword(".version")?;
    let version = match p.next()? {
        Tok::Num(v) => v,
        t => return p.err(format!("expected a version, found {t:?}")),
    };
    p.keyword(".target")?;
    let target = p.word()?;
    if p.is_punct(',') {
        return p.err("only a single .target is supported");
    }
    p.keyword(".address_size")?;
    let address_size = p.int()?;
    if address_size != 64 {
        return p.err("only .address_size 64 is supported");
    }
    let mut kernels = Vec::new();
    while p.peek().is_some() {
        kernels.push(kernel(&mut p)?);
    }
    if kernels.is_empty() {
        return p.err("no .entry");
    }
    Ok(Module {
        version,
        target,
        address_size: 64,
        kernels,
    })
}

fn kernel(p: &mut P) -> R<Kernel> {
    let visible = p.peek() == Some(&Tok::Word(".visible".into()));
    if visible {
        p.pos += 1;
    }
    p.keyword(".entry")?;
    let name = p.word()?;
    p.punct('(')?;
    let mut params = Vec::new();
    if !p.is_punct(')') {
        loop {
            p.keyword(".param")?;
            let ty = p.ty_directive()?;
            if ty == Ty::Pred {
                return p.err(".pred parameter");
            }
            let n = p.word()?;
            if n.starts_with('.') {
                p.pos -= 1;
                return p.err(format!("unsupported parameter attribute {n}"));
            }
            params.push((n, ty));
            if p.is_punct(',') {
                p.pos += 1;
            } else {
                break;
            }
        }
    }
    p.punct(')')?;
    p.punct('{')?;
    let mut regs = Vec::new();
    let mut shared = Vec::new();
    let mut decls = Vec::new();
    loop {
        if p.peek() == Some(&Tok::Word(".reg".into())) {
            p.pos += 1;
            let ty = p.ty_directive()?;
            let name = p.word()?;
            let count = if p.is_punct('<') {
                p.pos += 1;
                let n = p.int()?;
                p.punct('>')?;
                Some(
                    u32::try_from(n)
                        .map_err(|_| format!("line {}: bad register count", p.line()))?,
                )
            } else {
                None
            };
            if p.is_punct(',') {
                return p.err("one register declaration per .reg");
            }
            p.punct(';')?;
            decls.push(Decl::Reg(regs.len()));
            regs.push(RegDecl { ty, name, count });
        } else if p.peek() == Some(&Tok::Word(".shared".into())) {
            p.pos += 1;
            decls.push(Decl::Shared(shared.len()));
            shared.push(shared_decl(p)?);
        } else {
            break;
        }
    }
    let mut body = Vec::new();
    let mut labels = Vec::new();
    let mut lines = Vec::new();
    loop {
        if p.is_punct('}') {
            p.pos += 1;
            break;
        }
        // A label is a name followed by ':'.
        if let (Some(Tok::Word(w)), Some(Tok::Punct(':'))) =
            (p.peek().cloned(), p.toks.get(p.pos + 1).map(|t| &t.tok))
        {
            labels.push((w, body.len()));
            p.pos += 2;
            continue;
        }
        lines.push(p.line());
        body.push(stmt(p)?);
    }
    let k = Kernel {
        visible,
        name,
        params,
        regs,
        shared,
        decls,
        body,
        labels,
    };
    check(&k, &lines)?;
    Ok(k)
}

/// After `.shared`: `{.align a} .t name{[n]};`. Shared memory has no
/// initialiser; `.extern` (dynamic) shared memory is not in the subset.
fn shared_decl(p: &mut P) -> R<SharedDecl> {
    let mut align = None;
    if p.peek() == Some(&Tok::Word(".align".into())) {
        p.pos += 1;
        let a = p.int()?;
        if !matches!(a, 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256) {
            return p.err(format!("bad .align {a}"));
        }
        align = Some(a as u32);
    }
    let w = p.word()?;
    let elem = match w.strip_prefix('.') {
        Some(e) if SharedDecl::elem_bytes(e).is_some() => e.to_string(),
        _ => {
            p.pos -= 1;
            return p.err(format!("unsupported .shared element type {w}"));
        }
    };
    let name = p.word()?;
    if name.starts_with('%') || name.starts_with('.') {
        p.pos -= 1;
        return p.err(format!("bad .shared name {name}"));
    }
    let count = if p.is_punct('[') {
        p.pos += 1;
        if p.is_punct(']') {
            return p.err(".shared array without a size");
        }
        let n = p.int()?;
        p.punct(']')?;
        match u32::try_from(n) {
            Ok(n) if n > 0 => Some(n),
            _ => return p.err(format!("bad .shared array size {n}")),
        }
    } else {
        None
    };
    if p.is_punct('=') || p.is_punct(',') {
        return p.err("one .shared variable per declaration, without initialiser");
    }
    p.punct(';')?;
    let d = SharedDecl {
        align,
        elem,
        name,
        count,
    };
    if d.size() > 48 * 1024 {
        return p.err(format!(
            "static .shared {} of {} bytes exceeds 48 KB",
            d.name,
            d.size()
        ));
    }
    Ok(d)
}

fn operand(p: &mut P) -> R<Operand> {
    if let Some(Tok::Float(v, w)) = p.peek().cloned() {
        p.pos += 1;
        return Ok(Operand::FImm(v, w));
    }
    if p.is_punct('-') || matches!(p.peek(), Some(Tok::Int(_))) {
        return Ok(Operand::Imm(p.int()?));
    }
    let w = p.word()?;
    if let Some(s) = sreg(&w) {
        return Ok(Operand::Sreg(s));
    }
    if w.starts_with('%') {
        // Any other %name with a dot is a special register outside the subset.
        if w.contains('.') {
            p.pos -= 1;
            return p.err(format!("unsupported special register {w}"));
        }
        return Ok(Operand::Reg(w));
    }
    if w.starts_with('.') || w.contains('.') {
        p.pos -= 1;
        return p.err(format!("unsupported operand {w}"));
    }
    // a variable name; check() requires a `.shared` variable, in `mov`
    Ok(Operand::Sym(w))
}

fn reg(p: &mut P) -> R<String> {
    match operand(p)? {
        Operand::Reg(r) => Ok(r),
        o => {
            p.pos -= 1;
            p.err(format!("expected a register, found {o:?}"))
        }
    }
}

fn address(p: &mut P) -> R<Address> {
    p.punct('[')?;
    let w = p.word()?;
    let off = if p.is_punct('+') {
        p.pos += 1;
        Some(p.int()?)
    } else {
        None
    };
    p.punct(']')?;
    if w.starts_with('%') {
        if sreg(&w).is_some() || w.contains('.') {
            return p.err("special register as an address");
        }
        Ok(Address::Reg(w, off))
    } else {
        Ok(Address::Param(w, off))
    }
}

fn comma(p: &mut P) -> R<()> {
    p.punct(',')
}

/// The modifiers between the opcode and the type of a float instruction,
/// in the order the ISA writes them: rounding, `.ftz`, `.sat` (and `.NaN`
/// for min/max). Returns (rounding, ftz, sat, NaN) or what is wrong.
fn float_mods(
    mods: &[&str],
    round: &str,
    allow: &[&str],
) -> Result<(Option<String>, bool, bool, bool), String> {
    let order = ["rnd", "ftz", "sat", "NaN"];
    let mut at = 0;
    let (mut r, mut ftz, mut sat, mut nan) = (None, false, false, false);
    for m in mods {
        let kind = match *m {
            "rn" | "rz" | "rm" | "rp" if round == "f" => "rnd",
            "rni" | "rzi" | "rmi" | "rpi" if round == "i" => "rnd",
            "rn" | "rz" | "rm" | "rp" | "rni" | "rzi" | "rmi" | "rpi" if round == "fi" => "rnd",
            "ftz" => "ftz",
            "sat" => "sat",
            "NaN" => "NaN",
            _ => return Err(format!("modifier .{m}")),
        };
        if !allow.contains(&kind) {
            return Err(format!("modifier .{m}"));
        }
        let pos = order.iter().position(|k| *k == kind).unwrap();
        if pos < at {
            return Err(format!("modifiers out of order or repeated at .{m}"));
        }
        at = pos + 1;
        match kind {
            "rnd" => r = Some(m.to_string()),
            "ftz" => ftz = true,
            "sat" => sat = true,
            _ => nan = true,
        }
    }
    Ok((r, ftz, sat, nan))
}

fn rmode(s: &str) -> RMode {
    RMode::from_name(s.trim_end_matches('i')).unwrap()
}

/// A float instruction (`.f32`/`.f64` arithmetic, `setp`, `cvt` with a
/// float side), or `None` if `parts` is not one.
fn float_instr(p: &mut P, op: &str, parts: &[&str]) -> Option<R<Instr>> {
    let (&opc, rest) = parts.split_first()?;
    let float = |s: &str| matches!(s, "f32" | "f64");
    let t = |s: &str| if s == "f32" { Ty::F32 } else { Ty::F64 };
    let unsup = |m: String| -> R<Instr> { Err(format!("line {}: {op}: {m}", p.line())) };
    let last = *rest.last()?;
    match opc {
        "add" | "sub" | "mul" | "div" | "fma" | "sqrt" | "rcp" | "neg" | "abs" | "min" | "max"
            if float(last) =>
        {
            let ty = t(last);
            let mods = &rest[..rest.len() - 1];
            if mods.iter().any(|m| matches!(*m, "approx" | "full")) {
                return Some(unsup(
                    "approximate instructions are not modelled (no exact specification)".into(),
                ));
            }
            let allow: &[&str] = match opc {
                "add" | "sub" | "mul" | "fma" if ty == Ty::F32 => &["rnd", "ftz", "sat"],
                "div" | "sqrt" | "rcp" if ty == Ty::F32 => &["rnd", "ftz"],
                "add" | "sub" | "mul" | "fma" | "div" | "sqrt" | "rcp" => &["rnd"],
                "neg" | "abs" if ty == Ty::F32 => &["ftz"],
                "min" | "max" if ty == Ty::F32 => &["ftz", "NaN"],
                _ => &[],
            };
            let (r, ftz, sat, nan) = match float_mods(mods, "f", allow) {
                Ok(v) => v,
                Err(e) => return Some(unsup(e)),
            };
            let rounded = matches!(opc, "add" | "sub" | "mul" | "fma" | "div" | "sqrt" | "rcp");
            if rounded && r.is_none() {
                return Some(unsup(if matches!(opc, "add" | "sub" | "mul") {
                    "no rounding modifier: ptxas may fuse it with a mul into an fma (PTX ISA), so its result is not determined; write .rn".into()
                } else {
                    "a rounding modifier is required".into()
                }));
            }
            let m = r.map(|r| rmode(&r)).unwrap_or(RMode::Rn);
            Some((|| {
                let d = reg(p)?;
                comma(p)?;
                let a = operand(p)?;
                Ok(match opc {
                    "sqrt" => Instr::Fsqrt(m, ftz, ty, d, a),
                    "rcp" => Instr::Frcp(m, ftz, ty, d, a),
                    "neg" => Instr::Fneg(ftz, ty, d, a),
                    "abs" => Instr::Fabs(ftz, ty, d, a),
                    _ => {
                        comma(p)?;
                        let b = operand(p)?;
                        match opc {
                            "fma" => {
                                comma(p)?;
                                Instr::Ffma(m, ftz, sat, ty, d, a, b, operand(p)?)
                            }
                            "min" | "max" => Instr::Fminmax(opc == "max", ftz, nan, ty, d, a, b),
                            _ => {
                                let f = match opc {
                                    "add" => FBin::Add,
                                    "sub" => FBin::Sub,
                                    "mul" => FBin::Mul,
                                    _ => FBin::Div,
                                };
                                Instr::FBin(f, m, ftz, sat, ty, d, a, b)
                            }
                        }
                    }
                })
            })())
        }
        "setp" if float(last) && rest.len() >= 2 => {
            let ty = t(last);
            let Some(c) = FCmp::from_name(rest[0]) else {
                return Some(unsup(format!("comparison .{}", rest[0])));
            };
            let allow: &[&str] = if ty == Ty::F32 { &["ftz"] } else { &[] };
            let ftz = match float_mods(&rest[1..rest.len() - 1], "f", allow) {
                Ok((_, ftz, ..)) => ftz,
                Err(e) => return Some(unsup(e)),
            };
            Some((|| {
                let d = reg(p)?;
                comma(p)?;
                let a = operand(p)?;
                comma(p)?;
                Ok(Instr::Fsetp(c, ftz, ty, d, a, operand(p)?))
            })())
        }
        "cvt" if rest.len() >= 2 => {
            let (dt, st) = (rest[rest.len() - 2], rest[rest.len() - 1]);
            let (Some(dt), Some(st)) = (Ty::from_name(dt), Ty::from_name(st)) else {
                return None;
            };
            if !dt.is_float() && !st.is_float() {
                return None;
            }
            let mods = &rest[..rest.len() - 2];
            let (r, ftz, sat, _) = match float_mods(mods, "fi", &["rnd", "ftz", "sat"]) {
                Ok(v) => v,
                Err(e) => return Some(unsup(e)),
            };
            let rnd = match &r {
                None => CvtRnd::None,
                Some(s) if s.ends_with('i') => CvtRnd::I(rmode(s)),
                Some(s) => CvtRnd::F(rmode(s)),
            };
            // PTX ISA, cvt: which rounding each combination takes.
            let ok = match (dt.is_float(), st.is_float(), rnd) {
                (false, true, CvtRnd::I(_)) => dt.is_int(),
                (true, false, CvtRnd::F(_)) => st.is_int(),
                (true, true, CvtRnd::I(_)) => dt == st,
                (true, true, CvtRnd::F(_)) => dt == Ty::F32 && st == Ty::F64,
                (true, true, CvtRnd::None) => dt == Ty::F64 && st == Ty::F32,
                _ => false,
            };
            if !ok {
                return Some(unsup(
                    "rounding modifier or types outside the subset".into(),
                ));
            }
            if ftz && dt != Ty::F32 && st != Ty::F32 {
                return Some(unsup(".ftz needs an .f32 side".into()));
            }
            Some((|| {
                let d = reg(p)?;
                comma(p)?;
                Ok(Instr::CvtF(dt, st, rnd, ftz, sat, d, operand(p)?))
            })())
        }
        _ => None,
    }
}

fn stmt(p: &mut P) -> R<Stmt> {
    let guard = if p.is_punct('@') {
        p.pos += 1;
        let neg = p.is_punct('!');
        if neg {
            p.pos += 1;
        }
        Some(Guard { pred: reg(p)?, neg })
    } else {
        None
    };
    let op = p.word()?;
    let parts: Vec<&str> = op.split('.').collect();
    if let Some(r) = float_instr(p, &op, &parts) {
        let instr = r?;
        p.punct(';')?;
        return Ok(Stmt { guard, instr });
    }
    let ty = |s: &str, p: &P| -> R<Ty> {
        match Ty::from_name(s) {
            Some(t) if t != Ty::Pred => Ok(t),
            _ => p.err(format!("unsupported type .{s} in {op}")),
        }
    };
    let bin = |b: BinOp, t: &str, p: &mut P| -> R<Instr> {
        let t = ty(t, p)?;
        let d = reg(p)?;
        comma(p)?;
        let a = operand(p)?;
        comma(p)?;
        Ok(Instr::Bin(b, t, d, a, operand(p)?))
    };
    let instr = match parts.as_slice() {
        ["add", t] => bin(BinOp::Add, t, p)?,
        ["sub", t] => bin(BinOp::Sub, t, p)?,
        ["mul", "lo", t] => bin(BinOp::MulLo, t, p)?,
        ["mul", "wide", t] => bin(BinOp::MulWide, t, p)?,
        ["and", t] => bin(BinOp::And, t, p)?,
        ["or", t] => bin(BinOp::Or, t, p)?,
        ["xor", t] => bin(BinOp::Xor, t, p)?,
        ["shl", t] => bin(BinOp::Shl, t, p)?,
        ["shr", t] => bin(BinOp::Shr, t, p)?,
        ["mad", "lo", t] => {
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            let a = operand(p)?;
            comma(p)?;
            let b = operand(p)?;
            comma(p)?;
            Instr::MadLo(t, d, a, b, operand(p)?)
        }
        ["not", t] => {
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            Instr::Not(t, d, operand(p)?)
        }
        ["mov", t] => {
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            Instr::Mov(t, d, operand(p)?)
        }
        ["setp", c, t] => {
            let c = CmpOp::from_name(c).ok_or(format!("line {}: unsupported {op}", p.line()))?;
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            let a = operand(p)?;
            comma(p)?;
            Instr::Setp(c, t, d, a, operand(p)?)
        }
        ["selp", t] => {
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            let a = operand(p)?;
            comma(p)?;
            let b = operand(p)?;
            comma(p)?;
            Instr::Selp(t, d, a, b, reg(p)?)
        }
        ["cvt", dt, st] => {
            let (dt, st) = (ty(dt, p)?, ty(st, p)?);
            let d = reg(p)?;
            comma(p)?;
            Instr::Cvt(dt, st, d, operand(p)?)
        }
        ["cvta", "to", "global", "u64"] => {
            let d = reg(p)?;
            comma(p)?;
            Instr::CvtaGlobal(d, operand(p)?)
        }
        ["ld", sp, t] => {
            let sp = match *sp {
                "global" => Space::Global,
                "param" => Space::Param,
                "shared" => Space::Shared,
                _ => return p.err(format!("unsupported {op}")),
            };
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            Instr::Ld(sp, t, d, address(p)?)
        }
        ["st", sp @ ("global" | "shared"), t] => {
            let sp = if *sp == "global" {
                Space::Global
            } else {
                Space::Shared
            };
            let t = ty(t, p)?;
            let a = address(p)?;
            comma(p)?;
            Instr::St(sp, t, a, operand(p)?)
        }
        ["atom", sp @ ("global" | "shared"), o, t] => {
            let sp = if *sp == "global" {
                Space::Global
            } else {
                Space::Shared
            };
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            let a = address(p)?;
            comma(p)?;
            let b = operand(p)?;
            if *o == "cas" {
                comma(p)?;
                Instr::Cas(sp, t, d, a, b, operand(p)?)
            } else {
                let o = AtomOp::from_name(o)
                    .ok_or(format!("line {}: unsupported instruction {op}", p.line()))?;
                Instr::Atom(sp, o, t, d, a, b)
            }
        }
        ["red", sp @ ("global" | "shared"), o, t] => {
            let sp = if *sp == "global" {
                Space::Global
            } else {
                Space::Shared
            };
            let o = match AtomOp::from_name(o) {
                Some(AtomOp::Exch) | None => {
                    return p.err(format!("unsupported instruction {op}"));
                }
                Some(o) => o,
            };
            let t = ty(t, p)?;
            let a = address(p)?;
            comma(p)?;
            Instr::Red(sp, o, t, a, operand(p)?)
        }
        ["bar", "sync"] => {
            // `bar.sync 0` only: other barrier numbers and thread counts are
            // not in the subset.
            match operand(p)? {
                Operand::Imm(0) => {}
                _ => return p.err("only bar.sync 0 is supported"),
            }
            if p.is_punct(',') {
                return p.err("bar.sync with a thread count is not supported");
            }
            Instr::Bar
        }
        ["bra"] => Instr::Bra(false, p.word()?),
        ["bra", "uni"] => Instr::Bra(true, p.word()?),
        ["ret"] => Instr::Ret,
        ["exit"] => Instr::Exit,
        _ => {
            p.pos -= 1;
            return p.err(format!("unsupported instruction {op}"));
        }
    };
    p.punct(';')?;
    Ok(Stmt { guard, instr })
}

/// The instruction types PTX defines for each opcode of the subset (PTX ISA
/// §9.7; checked against ptxas in `tests/ptxas_agreement.rs`). The model
/// gives a meaning to more combinations than PTX does; those are refused so
/// that nothing is proved about text no assembler accepts.
fn types_ok(i: &Instr) -> Result<(), String> {
    use Ty::*;
    let arith = |t: &Ty| matches!(t, U32 | S32 | U64 | S64);
    let bits = |t: &Ty| matches!(t, B32 | B64);
    let ok = match i {
        Instr::Bin(BinOp::Add | BinOp::Sub | BinOp::MulLo, t, ..) | Instr::MadLo(t, ..) => arith(t),
        Instr::Bin(BinOp::MulWide, t, ..) => matches!(t, U32 | S32),
        Instr::Bin(BinOp::And | BinOp::Or | BinOp::Xor | BinOp::Shl, t, ..) | Instr::Not(t, ..) => {
            bits(t)
        }
        Instr::Bin(BinOp::Shr, t, ..) => arith(t) || bits(t),
        Instr::Mov(t, ..) | Instr::Selp(t, ..) => *t != Pred,
        Instr::Setp(_, F32 | F64, ..) => false,
        Instr::Setp(c, t, ..) => match c {
            CmpOp::Eq | CmpOp::Ne => true,
            CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => arith(t),
            CmpOp::Lo | CmpOp::Ls | CmpOp::Hi | CmpOp::Hs => matches!(t, U32 | U64),
        },
        Instr::Cvt(dt, st, ..) => arith(dt) && arith(st),
        Instr::CvtaGlobal(..) | Instr::Ld(..) | Instr::St(..) => true,
        Instr::Bra(..) | Instr::Ret | Instr::Exit | Instr::Bar => true,
        // PTX ISA, `atom` and `red`
        Instr::Atom(_, o, t, ..) | Instr::Red(_, o, t, ..) => match o {
            AtomOp::Add => matches!(t, U32 | S32 | U64),
            AtomOp::Min | AtomOp::Max => arith(t),
            AtomOp::Exch | AtomOp::And | AtomOp::Or | AtomOp::Xor => bits(t),
        },
        Instr::Cas(_, t, ..) => bits(t),
        // float forms: modifiers and types were checked by `float_instr`
        Instr::FBin(..)
        | Instr::Ffma(..)
        | Instr::Fsqrt(..)
        | Instr::Frcp(..)
        | Instr::Fneg(..)
        | Instr::Fabs(..)
        | Instr::Fminmax(..)
        | Instr::Fsetp(..)
        | Instr::CvtF(..) => true,
    };
    if ok {
        Ok(())
    } else {
        Err(format!("{} is not a PTX instruction type", print::instr(i)))
    }
}

/// Immediates and address offsets inside the ranges whose meaning is not in
/// doubt, and special registers only where ptxas allows them (`mov`, the
/// source of `cvt`). ptxas accepts wider immediates (`add.u32 d, a,
/// 0x1FFFFFFFF`); what it does with the excess bits is not specified, so the
/// subset refuses them.
fn operands_ok(i: &Instr) -> Result<(), String> {
    let imm = |o: &Operand, w: u32| -> Result<(), String> {
        if let Operand::Imm(v) = o {
            let (lo, hi) = (-(1i128 << (w - 1)), (1i128 << w) - 1);
            if *v < lo || *v > hi {
                return Err(format!("immediate {v} does not fit {w} bits"));
            }
        }
        if let Operand::FImm(..) = o {
            return Err("floating-point literal in an integer instruction".into());
        }
        Ok(())
    };
    // a source of a float-typed operand: a register or a float literal of
    // the type's width (integer literals are refused)
    let fsrc = |o: &Operand, t: Ty| -> Result<(), String> {
        match o {
            Operand::Reg(_) => Ok(()),
            Operand::FImm(_, w) if Some(*w) == t.width() => Ok(()),
            Operand::FImm(..) => Err(format!("literal of the wrong width for .{}", t.name())),
            Operand::Imm(_) => Err(format!("integer literal for .{}: write 0f/0d", t.name())),
            Operand::Sreg(_) | Operand::Sym(_) => {
                Err("special register or variable in a float instruction".into())
            }
        }
    };
    let src_at = |o: &Operand, t: Ty| -> Result<(), String> {
        if t.is_float() {
            fsrc(o, t)
        } else {
            imm(o, t.width().unwrap_or(32))
        }
    };
    let nosreg = |o: &Operand| -> Result<(), String> {
        match o {
            Operand::Sreg(s) => Err(format!(
                "special register {} outside mov/cvt",
                print::sreg(*s)
            )),
            Operand::Sym(n) => Err(format!("variable {n} outside mov")),
            _ => Ok(()),
        }
    };
    let off = |a: &Address| -> Result<(), String> {
        match a {
            Address::Reg(_, Some(v)) | Address::Param(_, Some(v))
                if *v < -(1i128 << 31) || *v >= (1i128 << 31) =>
            {
                Err(format!("address offset {v} does not fit 32 signed bits"))
            }
            _ => Ok(()),
        }
    };
    let w = |t: &Ty| t.width().unwrap_or(32);
    match i {
        Instr::Bin(b, t, _, x, y) => {
            let (wx, wy) = match b {
                BinOp::MulWide => (32, 32),
                BinOp::Shl | BinOp::Shr => (w(t), 32),
                _ => (w(t), w(t)),
            };
            nosreg(x)?;
            nosreg(y)?;
            imm(x, wx)?;
            imm(y, wy)
        }
        Instr::MadLo(t, _, a, b, c) => {
            for o in [a, b, c] {
                nosreg(o)?;
                imm(o, w(t))?;
            }
            Ok(())
        }
        Instr::Not(t, _, a) => {
            nosreg(a)?;
            imm(a, w(t))
        }
        Instr::Mov(t, _, a) => {
            if let Operand::Sym(n) = a {
                if !matches!(t, Ty::U32 | Ty::B32 | Ty::U64 | Ty::B64) {
                    return Err(format!("mov.{} of the address of {n}", t.name()));
                }
            }
            if let Operand::Sreg(_) = a {
                if t.is_float() {
                    return Err("mov of a special register to a float".into());
                }
            }
            if matches!(a, Operand::Sreg(_) | Operand::Sym(_)) {
                Ok(())
            } else {
                src_at(a, *t)
            }
        }
        Instr::Setp(_, t, _, a, b) | Instr::Selp(t, _, a, b, _) => {
            nosreg(a)?;
            nosreg(b)?;
            src_at(a, *t)?;
            src_at(b, *t)
        }
        Instr::Cvt(_, st, _, a) => {
            if let Operand::Sym(n) = a {
                return Err(format!("variable {n} outside mov"));
            }
            imm(a, w(st))
        }
        Instr::CvtaGlobal(_, a) => {
            nosreg(a)?;
            imm(a, 64)
        }
        Instr::Ld(_, _, _, a) => off(a),
        Instr::St(_, t, a, v) => {
            nosreg(v)?;
            src_at(v, *t)?;
            off(a)
        }
        Instr::Atom(_, _, t, _, a, b) | Instr::Red(_, _, t, a, b) => {
            nosreg(b)?;
            imm(b, w(t))?;
            off(a)
        }
        Instr::Cas(_, t, _, a, b, c) => {
            for o in [b, c] {
                nosreg(o)?;
                imm(o, w(t))?;
            }
            off(a)
        }
        Instr::Bra(..) | Instr::Ret | Instr::Exit | Instr::Bar => Ok(()),
        Instr::FBin(.., t, _, a, b)
        | Instr::Fminmax(.., t, _, a, b)
        | Instr::Fsetp(_, _, t, _, a, b) => {
            fsrc(a, *t)?;
            fsrc(b, *t)
        }
        Instr::Ffma(.., t, _, a, b, c) => {
            fsrc(a, *t)?;
            fsrc(b, *t)?;
            fsrc(c, *t)
        }
        Instr::Fsqrt(.., t, _, a)
        | Instr::Frcp(.., t, _, a)
        | Instr::Fneg(_, t, _, a)
        | Instr::Fabs(_, t, _, a) => fsrc(a, *t),
        Instr::CvtF(_, st, .., a) => {
            nosreg(a)?;
            src_at(a, *st)
        }
    }
}

/// Each register an instruction reads or writes, with the type it is used
/// at. A register declared `.f32`/`.f64` may be used only at its own type
/// or a `.b` type of its width; another register never at a float type.
fn typed_uses(i: &Instr) -> Vec<(&str, Ty)> {
    fn o<'a>(x: &'a Operand, t: Ty, v: &mut Vec<(&'a str, Ty)>) {
        if let Operand::Reg(r) = x {
            v.push((r.as_str(), t));
        }
    }
    fn addr<'a>(a: &'a Address, v: &mut Vec<(&'a str, Ty)>) {
        if let Address::Reg(r, _) = a {
            v.push((r.as_str(), Ty::B64));
        }
    }
    let mut v: Vec<(&str, Ty)> = Vec::new();
    match i {
        Instr::Bin(BinOp::MulWide, t, d, a, b) => {
            v.push((d.as_str(), Ty::U64));
            o(a, *t, &mut v);
            o(b, *t, &mut v);
        }
        Instr::Bin(BinOp::Shl | BinOp::Shr, t, d, a, b) => {
            v.push((d.as_str(), *t));
            o(a, *t, &mut v);
            o(b, Ty::U32, &mut v);
        }
        Instr::Bin(_, t, d, a, b) => {
            v.push((d.as_str(), *t));
            o(a, *t, &mut v);
            o(b, *t, &mut v);
        }
        Instr::MadLo(t, d, a, b, c) => {
            v.push((d.as_str(), *t));
            for x in [a, b, c] {
                o(x, *t, &mut v);
            }
        }
        Instr::Not(t, d, a) | Instr::Mov(t, d, a) => {
            v.push((d.as_str(), *t));
            o(a, *t, &mut v);
        }
        Instr::Setp(_, t, _, a, b) => {
            o(a, *t, &mut v);
            o(b, *t, &mut v);
        }
        Instr::Selp(t, d, a, b, _) => {
            v.push((d.as_str(), *t));
            o(a, *t, &mut v);
            o(b, *t, &mut v);
        }
        Instr::Cvt(dt, st, d, a) | Instr::CvtF(dt, st, _, _, _, d, a) => {
            v.push((d.as_str(), *dt));
            o(a, *st, &mut v);
        }
        Instr::CvtaGlobal(d, a) => {
            v.push((d.as_str(), Ty::U64));
            o(a, Ty::U64, &mut v);
        }
        Instr::Ld(sp, t, d, a) => {
            v.push((d.as_str(), *t));
            if *sp != Space::Shared {
                addr(a, &mut v);
            }
        }
        Instr::St(sp, t, a, x) => {
            o(x, *t, &mut v);
            if *sp != Space::Shared {
                addr(a, &mut v);
            }
        }
        Instr::Atom(sp, _, t, d, a, b) => {
            v.push((d.as_str(), *t));
            o(b, *t, &mut v);
            if *sp != Space::Shared {
                addr(a, &mut v);
            }
        }
        Instr::Cas(sp, t, d, a, b, c) => {
            v.push((d.as_str(), *t));
            o(b, *t, &mut v);
            o(c, *t, &mut v);
            if *sp != Space::Shared {
                addr(a, &mut v);
            }
        }
        Instr::Red(sp, _, t, a, b) => {
            o(b, *t, &mut v);
            if *sp != Space::Shared {
                addr(a, &mut v);
            }
        }
        Instr::FBin(.., t, d, a, b) | Instr::Fminmax(.., t, d, a, b) => {
            v.push((d.as_str(), *t));
            o(a, *t, &mut v);
            o(b, *t, &mut v);
        }
        Instr::Ffma(.., t, d, a, b, c) => {
            v.push((d.as_str(), *t));
            for x in [a, b, c] {
                o(x, *t, &mut v);
            }
        }
        Instr::Fsqrt(.., t, d, a)
        | Instr::Frcp(.., t, d, a)
        | Instr::Fneg(_, t, d, a)
        | Instr::Fabs(_, t, d, a) => {
            v.push((d.as_str(), *t));
            o(a, *t, &mut v);
        }
        Instr::Fsetp(_, _, t, _, a, b) => {
            o(a, *t, &mut v);
            o(b, *t, &mut v);
        }
        Instr::Bra(..) | Instr::Ret | Instr::Exit | Instr::Bar => {}
    }
    v
}

/// The type rule of [`typed_uses`].
fn compatible(declared: Ty, used: Ty) -> bool {
    if declared.is_float() {
        used == declared || (used.is_bits() && used.width() == declared.width())
    } else {
        !used.is_float()
    }
}

/// Declared registers, params and labels used at the right types.
fn check(k: &Kernel, lines: &[usize]) -> R<()> {
    let mut regs: HashMap<String, Ty> = HashMap::new();
    for d in &k.regs {
        let names: Vec<String> = match d.count {
            Some(n) => (0..n).map(|i| format!("{}{i}", d.name)).collect(),
            None => vec![d.name.clone()],
        };
        for n in names {
            if regs.insert(n.clone(), d.ty).is_some() {
                return Err(format!("{}: register {n} declared twice", k.name));
            }
        }
    }
    let params: HashMap<&str, Ty> = k.params.iter().map(|(n, t)| (n.as_str(), *t)).collect();
    let mut shared = std::collections::HashSet::new();
    for d in &k.shared {
        if !shared.insert(d.name.as_str()) || params.contains_key(d.name.as_str()) {
            return Err(format!("{}: name {} declared twice", k.name, d.name));
        }
        if regs.contains_key(&d.name) {
            return Err(format!(
                "{}: {} is both a register and a variable",
                k.name, d.name
            ));
        }
        if d.size() % d.alignment() as u64 != 0 && d.count.is_none() {
            return Err(format!(
                "{}: .shared {} smaller than its alignment",
                k.name, d.name
            ));
        }
    }
    let mut seen = std::collections::HashSet::new();
    for (l, _) in &k.labels {
        if !seen.insert(l) {
            return Err(format!("{}: label {l} defined twice", k.name));
        }
    }
    for (s, line) in k.body.iter().zip(lines) {
        let e = |m: String| format!("line {line}: {m}");
        let width_of = |r: &str| -> R<Ty> {
            regs.get(r)
                .copied()
                .ok_or(e(format!("undeclared register {r}")))
        };
        let pred = |r: &str| -> R<()> {
            match width_of(r)? {
                Ty::Pred => Ok(()),
                _ => Err(e(format!("{r} is not a .pred register"))),
            }
        };
        let data = |r: &str, w: u32| -> R<()> {
            match width_of(r)?.width() {
                Some(x) if x == w => Ok(()),
                _ => Err(e(format!("{r} is not a {w}-bit register"))),
            }
        };
        let src = |o: &Operand, w: u32| -> R<()> {
            match o {
                Operand::Reg(r) => data(r, w),
                Operand::Imm(_) => Ok(()),
                Operand::Sreg(_) if w == 32 => Ok(()),
                Operand::Sreg(_) => Err(e("special registers are 32-bit".into())),
                Operand::Sym(n) if shared.contains(n.as_str()) => Ok(()),
                Operand::Sym(n) => Err(e(format!("{n} is not a .shared variable"))),
                Operand::FImm(_, fw) if *fw == w => Ok(()),
                Operand::FImm(..) => Err(e("float literal of the wrong width".into())),
            }
        };
        // a data address in `sp`: global needs a 64-bit register; shared takes
        // a 32- or 64-bit register or a `.shared` variable
        let addr = |sp: Space, a: &Address| -> R<()> {
            match (sp, a) {
                (Space::Global, Address::Reg(r, _)) => data(r, 64),
                (Space::Shared, Address::Reg(r, _)) => match width_of(r)?.width() {
                    Some(32 | 64) => Ok(()),
                    _ => Err(e(format!("{r} is not a 32- or 64-bit register"))),
                },
                (Space::Shared, Address::Param(n, _)) if shared.contains(n.as_str()) => Ok(()),
                (Space::Shared, Address::Param(n, _)) => {
                    Err(e(format!("{n} is not a .shared variable")))
                }
                (_, Address::Param(..)) => Err(e(format!(
                    "{} needs a register address",
                    print::instr(&s.instr)
                ))),
                (Space::Param, _) => Err(e("not a data space".into())),
            }
        };
        let w = |t: Ty| t.width().unwrap();
        if let Some(g) = &s.guard {
            pred(&g.pred)?;
        }
        types_ok(&s.instr).map_err(e)?;
        operands_ok(&s.instr).map_err(e)?;
        for (r, t) in typed_uses(&s.instr) {
            if let Some(dt) = regs.get(r) {
                if !compatible(*dt, t) {
                    return Err(e(format!(
                        "register {r} (.{}) used at .{}",
                        dt.name(),
                        t.name()
                    )));
                }
            }
        }
        if s.guard.is_some() && matches!(s.instr, Instr::Bar) {
            // bar.sync is .aligned: every thread of the CTA must execute it
            return Err(e("predicated bar.sync".into()));
        }
        if s.guard.is_some() && matches!(s.instr, Instr::Bra(true, _)) {
            // `bra.uni` promises the branch is non-divergent; a guarded one
            // can diverge, which PTX leaves undefined.
            return Err(e("predicated bra.uni".into()));
        }
        match &s.instr {
            Instr::Bin(BinOp::MulWide, t, d, a, b) => {
                if !matches!(t, Ty::U32 | Ty::S32) {
                    return Err(e("mul.wide is supported for .u32 and .s32".into()));
                }
                data(d, 64)?;
                src(a, 32)?;
                src(b, 32)?;
            }
            Instr::Bin(BinOp::Shl | BinOp::Shr, t, d, a, b) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
                src(b, 32)?;
            }
            Instr::Bin(_, t, d, a, b) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
                src(b, w(*t))?;
            }
            Instr::MadLo(t, d, a, b, c) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
                src(b, w(*t))?;
                src(c, w(*t))?;
            }
            Instr::Not(t, d, a) | Instr::Mov(t, d, a) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
            }
            Instr::Setp(c, t, d, a, b) => {
                if c.is_ordered() && t.is_bits() {
                    return Err(e("ordered comparison on a .b type".into()));
                }
                pred(d)?;
                src(a, w(*t))?;
                src(b, w(*t))?;
            }
            Instr::Selp(t, d, a, b, q) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
                src(b, w(*t))?;
                pred(q)?;
            }
            Instr::Cvt(dt, st, d, a) => {
                data(d, w(*dt))?;
                src(a, w(*st))?;
            }
            Instr::CvtaGlobal(d, a) => {
                data(d, 64)?;
                src(a, 64)?;
            }
            Instr::Ld(Space::Param, t, d, a) => {
                data(d, w(*t))?;
                match a {
                    Address::Param(n, off) if off.unwrap_or(0) == 0 => {
                        if params.get(n.as_str()) != Some(t) {
                            return Err(e(format!("ld.param.{} of parameter {n}", t.name())));
                        }
                    }
                    _ => return Err(e("ld.param needs [parameter] without offset".into())),
                }
            }
            Instr::Ld(sp, t, d, a) => {
                data(d, w(*t))?;
                addr(*sp, a)?;
            }
            Instr::St(Space::Param, ..) => return Err(e("st.param".into())),
            Instr::St(sp, t, a, v) => {
                src(v, w(*t))?;
                addr(*sp, a)?;
            }
            Instr::Atom(sp, _, t, d, a, b) => {
                data(d, w(*t))?;
                src(b, w(*t))?;
                addr(*sp, a)?;
            }
            Instr::Cas(sp, t, d, a, b, c) => {
                data(d, w(*t))?;
                src(b, w(*t))?;
                src(c, w(*t))?;
                addr(*sp, a)?;
            }
            Instr::Red(sp, _, t, a, b) => {
                src(b, w(*t))?;
                addr(*sp, a)?;
            }
            Instr::Bar => {}
            Instr::Bra(_, l) => {
                if !k.labels.iter().any(|(m, _)| m == l) {
                    return Err(e(format!("undefined label {l}")));
                }
            }
            Instr::Ret | Instr::Exit => {}
            Instr::FBin(.., t, d, a, b) | Instr::Fminmax(.., t, d, a, b) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
                src(b, w(*t))?;
            }
            Instr::Ffma(.., t, d, a, b, c) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
                src(b, w(*t))?;
                src(c, w(*t))?;
            }
            Instr::Fsqrt(.., t, d, a)
            | Instr::Frcp(.., t, d, a)
            | Instr::Fneg(_, t, d, a)
            | Instr::Fabs(_, t, d, a) => {
                data(d, w(*t))?;
                src(a, w(*t))?;
            }
            Instr::Fsetp(_, _, t, d, a, b) => {
                pred(d)?;
                src(a, w(*t))?;
                src(b, w(*t))?;
            }
            Instr::CvtF(dt, st, _, _, _, d, a) => {
                data(d, w(*dt))?;
                src(a, w(*st))?;
            }
        }
    }
    Ok(())
}
