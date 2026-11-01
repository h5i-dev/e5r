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
    while p.peek() == Some(&Tok::Word(".reg".into())) {
        p.pos += 1;
        let ty = p.ty_directive()?;
        let name = p.word()?;
        let count = if p.is_punct('<') {
            p.pos += 1;
            let n = p.int()?;
            p.punct('>')?;
            Some(u32::try_from(n).map_err(|_| format!("line {}: bad register count", p.line()))?)
        } else {
            None
        };
        if p.is_punct(',') {
            return p.err("one register declaration per .reg");
        }
        p.punct(';')?;
        regs.push(RegDecl { ty, name, count });
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
        body,
        labels,
    };
    check(&k, &lines)?;
    Ok(k)
}

fn operand(p: &mut P) -> R<Operand> {
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
    p.pos -= 1;
    p.err(format!("unsupported operand {w}"))
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
                _ => return p.err(format!("unsupported {op}")),
            };
            let t = ty(t, p)?;
            let d = reg(p)?;
            comma(p)?;
            Instr::Ld(sp, t, d, address(p)?)
        }
        ["st", "global", t] => {
            let t = ty(t, p)?;
            let a = address(p)?;
            comma(p)?;
            Instr::St(Space::Global, t, a, operand(p)?)
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
        Instr::Bin(BinOp::Shr, ..) | Instr::Mov(..) | Instr::Selp(..) => true,
        Instr::Setp(c, t, ..) => match c {
            CmpOp::Eq | CmpOp::Ne => true,
            CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => arith(t),
            CmpOp::Lo | CmpOp::Ls | CmpOp::Hi | CmpOp::Hs => matches!(t, U32 | U64),
        },
        Instr::Cvt(dt, st, ..) => arith(dt) && arith(st),
        Instr::CvtaGlobal(..) | Instr::Ld(..) | Instr::St(..) => true,
        Instr::Bra(..) | Instr::Ret | Instr::Exit => true,
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
        Ok(())
    };
    let nosreg = |o: &Operand| -> Result<(), String> {
        match o {
            Operand::Sreg(s) => Err(format!(
                "special register {} outside mov/cvt",
                print::sreg(*s)
            )),
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
        Instr::Mov(t, _, a) => imm(a, w(t)),
        Instr::Setp(_, t, _, a, b) | Instr::Selp(t, _, a, b, _) => {
            nosreg(a)?;
            nosreg(b)?;
            imm(a, w(t))?;
            imm(b, w(t))
        }
        Instr::Cvt(_, st, _, a) => imm(a, w(st)),
        Instr::CvtaGlobal(_, a) => {
            nosreg(a)?;
            imm(a, 64)
        }
        Instr::Ld(_, _, _, a) => off(a),
        Instr::St(_, t, a, v) => {
            nosreg(v)?;
            imm(v, w(t))?;
            off(a)
        }
        Instr::Bra(..) | Instr::Ret | Instr::Exit => Ok(()),
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
            }
        };
        let w = |t: Ty| t.width().unwrap();
        if let Some(g) = &s.guard {
            pred(&g.pred)?;
        }
        types_ok(&s.instr).map_err(e)?;
        operands_ok(&s.instr).map_err(e)?;
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
            Instr::Ld(Space::Global, t, d, a) => {
                data(d, w(*t))?;
                match a {
                    Address::Reg(r, _) => data(r, 64)?,
                    Address::Param(..) => {
                        return Err(e("ld.global needs a register address".into()));
                    }
                }
            }
            Instr::St(Space::Global, t, a, v) => {
                src(v, w(*t))?;
                match a {
                    Address::Reg(r, _) => data(r, 64)?,
                    Address::Param(..) => {
                        return Err(e("st.global needs a register address".into()));
                    }
                }
            }
            Instr::St(Space::Param, ..) => return Err(e("st.param".into())),
            Instr::Bra(_, l) => {
                if !k.labels.iter().any(|(m, _)| m == l) {
                    return Err(e(format!("undefined label {l}")));
                }
            }
            Instr::Ret | Instr::Exit => {}
        }
    }
    Ok(())
}
