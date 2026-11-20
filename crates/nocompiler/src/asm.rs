//! Structured assembly (docs/isa/asm.md): the listing `nocompiler disasm`
//! prints, read back. `listing` writes it; `assemble` turns it into an ELF
//! with `.nocompiler.struct`, checked against the profile before it is
//! written; `skeleton` writes a Lean proof skeleton from its annotations.
//!
//! The format is the exact inverse of the listing: `disasm`, then `asm`,
//! gives the same `.text`, function symbols, data sections and structure
//! (tests/asm.rs, on every committed example). For writing by hand (or by a
//! model) the address and word columns are optional, branch targets may be
//! the label of an enclosing `block` (its end) or `loop` (its head), so that
//! rule R3 holds by construction, and a few pseudo-instructions are accepted.
//!
//! Nothing here is trusted: the output is re-read and checked with
//! `profile::check`, and a proof about it is checked by the Lean kernel
//! against its bytes.

use crate::isa::{self, BrOp, IOp, Imm, Instr, LdOp, ROp, RWOp, Reg, ShOp, ShWOp, StOp, UOp};
use crate::profile::{self, Func, FuncMeta, Kind, Node};
use crate::{Binary, meta};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// Where a function goes when its header gives no address.
pub const DEFAULT_TEXT: u64 = 0x11000;

// ---------------------------------------------------------------- listing

/// The structured listing of a binary: every function nested by its
/// block/loop tree, then every allocated data section.
pub fn listing(bin: &Binary) -> String {
    let mut out = String::new();
    for (f, r) in bin.funcs.iter().zip(bin.check()) {
        let _ = writeln!(out, "\n{} {:#x}:", f.name, f.entry);
        let nodes = match &r.result {
            Ok(m) => m.nodes.clone(),
            Err(vs) => {
                for v in vs {
                    let _ = writeln!(out, "  ; {v}");
                }
                vec![]
            }
        };
        let mut marks: Vec<(u64, bool, usize, &'static str)> = Vec::new();
        fn walk(ns: &[Node], d: usize, m: &mut Vec<(u64, bool, usize, &'static str)>) {
            for n in ns {
                let k = match n.kind {
                    Kind::Block => "block",
                    Kind::Loop => "loop",
                };
                m.push((n.start, true, d, k));
                walk(&n.children, d + 1, m);
                m.push((n.end, false, d, k));
            }
        }
        walk(&nodes, 0, &mut marks);
        for (i, &w) in f.words.iter().enumerate() {
            let pc = f.entry + 4 * i as u64;
            for &(_, _, d, k) in marks.iter().filter(|m| m.0 == pc && !m.1) {
                let _ = writeln!(out, "  {:ind$}end {k}", "", ind = 2 * d);
            }
            for &(_, _, d, k) in marks.iter().filter(|m| m.0 == pc && m.1) {
                let _ = writeln!(out, "  {:ind$}{k} {{", "", ind = 2 * d);
            }
            let depth = marks.iter().filter(|m| m.1 && m.0 <= pc).count()
                - marks.iter().filter(|m| !m.1 && m.0 <= pc).count();
            let text = isa::decode(w)
                .map(|i| i.asm(pc))
                .unwrap_or_else(|| format!(".word {w:#010x}"));
            let _ = writeln!(
                out,
                "  {:ind$}{pc:8x}: {w:08x}  {text}",
                "",
                ind = 2 * depth
            );
        }
        for &(_, _, d, k) in marks.iter().filter(|m| m.0 == f.end() && !m.1) {
            let _ = writeln!(out, "  {:ind$}end {k}", "", ind = 2 * d);
        }
    }
    for g in &bin.segments {
        let fl = if g.writable { "rw" } else { "r" };
        if g.zero {
            let _ = writeln!(out, "\nbss {} {:#x} {} {fl}", g.name, g.addr, g.bytes.len());
            continue;
        }
        let _ = writeln!(out, "\ndata {} {:#x} {fl}:", g.name, g.addr);
        for c in g.bytes.chunks(16) {
            let hex: Vec<String> = c.iter().map(|b| format!("{b:02x}")).collect();
            let _ = writeln!(out, "  {}", hex.join(" "));
        }
    }
    out
}

// ---------------------------------------------------------------- parsing

#[derive(Clone, Debug)]
enum Item {
    Ins {
        line: usize,
        addr: Option<u64>,
        word: Option<u32>,
        text: String,
    },
    Open {
        line: usize,
        kind: Kind,
        label: Option<String>,
        inv: Option<String>,
        measure: Option<String>,
    },
    Close {
        line: usize,
        kind: Kind,
    },
}

#[derive(Clone, Debug, Default)]
struct AFunc {
    name: String,
    line: usize,
    addr: Option<u64>,
    items: Vec<Item>,
    spec: Option<String>,
    intro: Option<String>,
}

#[derive(Clone, Debug)]
struct AData {
    name: String,
    line: usize,
    addr: Option<u64>,
    writable: bool,
    zero: bool,
    bytes: Vec<u8>,
    /// Labels, by offset into `bytes`.
    labels: Vec<(String, usize)>,
}

#[derive(Clone, Debug, Default)]
struct Source {
    funcs: Vec<AFunc>,
    data: Vec<AData>,
    imports: Vec<String>,
    opens: Vec<String>,
    namespace: Option<String>,
}

/// Which annotation a `#` continuation line extends.
#[derive(Clone, Copy, PartialEq)]
enum Ann {
    None,
    Inv,
    Measure,
    Spec,
    Intro,
}

fn err(line: usize, msg: impl std::fmt::Display) -> String {
    format!("line {line}: {msg}")
}

fn parse_u64(s: &str) -> Option<u64> {
    if let Some(h) = s.strip_prefix("0x") {
        u64::from_str_radix(h, 16).ok()
    } else {
        s.parse().ok()
    }
}

fn is_name(s: &str) -> bool {
    let mut c = s.chars();
    matches!(c.next(), Some(ch) if ch.is_ascii_alphabetic() || ch == '_' || ch == '.' || ch == '$')
        && s.chars()
            .all(|ch| ch.is_ascii_alphanumeric() || "_.$".contains(ch))
}

fn parse_source(text: &str) -> Result<Source, String> {
    let mut src = Source::default();
    let mut cur: Option<AFunc> = None;
    let mut data: Option<AData> = None;
    let mut ann = Ann::None;
    let finish = |src: &mut Source, cur: &mut Option<AFunc>, data: &mut Option<AData>| {
        if let Some(f) = cur.take() {
            src.funcs.push(f);
        }
        if let Some(d) = data.take() {
            src.data.push(d);
        }
    };
    for (i, raw) in text.lines().enumerate() {
        let line = i + 1;
        let t = raw.trim();
        // Annotations: Lean text, passed through verbatim.
        if let Some(rest) = t.strip_prefix('#') {
            let (key, body) = match rest.split_once(char::is_whitespace) {
                Some((k, b)) => (k, b.trim()),
                None => (rest, ""),
            };
            let f = cur.as_mut();
            let append = |slot: &mut Option<String>, b: &str| match slot {
                Some(s) => {
                    s.push('\n');
                    s.push_str(b);
                }
                None => *slot = Some(b.to_string()),
            };
            match key {
                "import" => src.imports.push(body.to_string()),
                "open" => src.opens.push(body.to_string()),
                "namespace" => src.namespace = Some(body.to_string()),
                "spec" | "intro" => {
                    let f = f.ok_or_else(|| err(line, format!("#{key} outside a function")))?;
                    if key == "spec" {
                        append(&mut f.spec, body);
                        ann = Ann::Spec;
                    } else {
                        append(&mut f.intro, body);
                        ann = Ann::Intro;
                    }
                }
                "inv" | "measure" => {
                    let f = f.ok_or_else(|| err(line, format!("#{key} outside a function")))?;
                    let Some(Item::Open {
                        kind: Kind::Loop,
                        inv,
                        measure,
                        ..
                    }) = f.items.last_mut()
                    else {
                        return Err(err(line, format!("#{key} must follow `loop {{` directly")));
                    };
                    if key == "inv" {
                        append(inv, body);
                        ann = Ann::Inv;
                    } else {
                        append(measure, body);
                        ann = Ann::Measure;
                    }
                }
                "" => {
                    // `#` followed by a space: a continuation line (keeps its text).
                    let body = raw.trim_start().strip_prefix('#').unwrap_or("").trim();
                    let f = f.ok_or_else(|| err(line, "continuation outside a function"))?;
                    match ann {
                        Ann::Spec => append(&mut f.spec, body),
                        Ann::Intro => append(&mut f.intro, body),
                        Ann::Inv | Ann::Measure => match f.items.last_mut() {
                            Some(Item::Open { inv, measure, .. }) => {
                                append(if ann == Ann::Inv { inv } else { measure }, body)
                            }
                            _ => return Err(err(line, "continuation not after #inv/#measure")),
                        },
                        Ann::None => return Err(err(line, "continuation without an annotation")),
                    }
                }
                _ => return Err(err(line, format!("unknown annotation #{key}"))),
            }
            continue;
        }
        ann = Ann::None;
        let t = match t.find(';') {
            Some(k) => t[..k].trim(),
            None => t,
        };
        if t.is_empty() {
            continue;
        }
        // Data.
        if let Some(rest) = t.strip_prefix("data ") {
            finish(&mut src, &mut cur, &mut data);
            let rest = rest
                .strip_suffix(':')
                .ok_or_else(|| err(line, "`data` header ends with `:`"))?;
            let ws: Vec<&str> = rest.split_whitespace().collect();
            let (name, mut addr, mut writable) = (ws.first().copied().unwrap_or(""), None, false);
            for w in &ws[1..] {
                match *w {
                    "r" => writable = false,
                    "rw" => writable = true,
                    a => addr = Some(parse_u64(a).ok_or_else(|| err(line, format!("bad `{a}`")))?),
                }
            }
            data = Some(AData {
                name: name.into(),
                line,
                addr,
                writable,
                zero: false,
                bytes: vec![],
                labels: vec![],
            });
            continue;
        }
        if let Some(rest) = t.strip_prefix("bss ") {
            finish(&mut src, &mut cur, &mut data);
            let ws: Vec<&str> = rest.split_whitespace().collect();
            let [name, addr, size, fl] = ws[..] else {
                return Err(err(line, "`bss NAME ADDR SIZE r|rw`"));
            };
            src.data.push(AData {
                name: name.into(),
                line,
                addr: Some(parse_u64(addr).ok_or_else(|| err(line, "bad address"))?),
                writable: fl == "rw",
                zero: true,
                bytes: vec![0; parse_u64(size).ok_or_else(|| err(line, "bad size"))? as usize],
                labels: vec![],
            });
            continue;
        }
        if let Some(d) = data.as_mut() {
            if let Some(l) = t.strip_prefix('@').and_then(|l| l.strip_suffix(':')) {
                d.labels.push((l.to_string(), d.bytes.len()));
                continue;
            }
            if let Some(s) = t.strip_prefix(".ascii ") {
                let s = s.trim();
                let s = s
                    .strip_prefix('"')
                    .and_then(|s| s.strip_suffix('"'))
                    .ok_or_else(|| err(line, "`.ascii \"...\"`"))?;
                let mut chars = s.chars();
                while let Some(c) = chars.next() {
                    if c == '\\' {
                        match chars.next() {
                            Some('n') => d.bytes.push(b'\n'),
                            Some('t') => d.bytes.push(b'\t'),
                            Some('0') => d.bytes.push(0),
                            Some('\\') => d.bytes.push(b'\\'),
                            Some('"') => d.bytes.push(b'"'),
                            _ => return Err(err(line, "unknown escape")),
                        }
                    } else {
                        let mut b = [0; 4];
                        d.bytes.extend_from_slice(c.encode_utf8(&mut b).as_bytes());
                    }
                }
                continue;
            }
            for h in t.split_whitespace() {
                let h = h.strip_prefix(".byte").unwrap_or(h);
                if h.is_empty() {
                    continue;
                }
                if h.len() % 2 != 0 {
                    return Err(err(line, format!("`{h}`: hex bytes come in pairs")));
                }
                for k in (0..h.len()).step_by(2) {
                    d.bytes.push(
                        u8::from_str_radix(&h[k..k + 2], 16)
                            .map_err(|_| err(line, format!("`{h}` is not hex")))?,
                    );
                }
            }
            continue;
        }
        // A function header: `name ADDR:` or `name:`, nothing after the colon.
        if let Some(head) = t.strip_suffix(':') {
            let ws: Vec<&str> = head.split_whitespace().collect();
            let header = match ws[..] {
                [n] if is_name(n) => Some((n, None)),
                [n, a] if is_name(n) => Some((
                    n,
                    Some(parse_u64(a).ok_or_else(|| err(line, "bad address"))?),
                )),
                _ => None,
            };
            if let Some((n, a)) = header {
                finish(&mut src, &mut cur, &mut data);
                cur = Some(AFunc {
                    name: n.into(),
                    line,
                    addr: a,
                    ..Default::default()
                });
                continue;
            }
        }
        let f = cur
            .as_mut()
            .ok_or_else(|| err(line, "instruction outside a function"))?;
        let open = |kw: &str| -> Option<Option<String>> {
            let r = t.strip_prefix(kw)?.trim();
            let r = r.strip_suffix('{')?.trim();
            if r.is_empty() {
                Some(None)
            } else {
                r.strip_prefix('@')
                    .filter(|l| is_name(l))
                    .map(|l| Some(l.to_string()))
            }
        };
        if let Some(label) = open("block") {
            f.items.push(Item::Open {
                line,
                kind: Kind::Block,
                label,
                inv: None,
                measure: None,
            });
            continue;
        }
        if let Some(label) = open("loop") {
            f.items.push(Item::Open {
                line,
                kind: Kind::Loop,
                label,
                inv: None,
                measure: None,
            });
            continue;
        }
        if t == "end block" || t == "end loop" {
            let kind = if t == "end block" {
                Kind::Block
            } else {
                Kind::Loop
            };
            f.items.push(Item::Close { line, kind });
            continue;
        }
        // `ADDR: WORD  text`, or just `text`.
        let (addr, word, text) = match t.split_once(':') {
            Some((a, rest)) if a.chars().all(|c| c.is_ascii_hexdigit()) && !a.is_empty() => {
                let rest = rest.trim();
                let (w, text) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
                let addr = u64::from_str_radix(a, 16).map_err(|_| err(line, "bad address"))?;
                let word =
                    u32::from_str_radix(w, 16).map_err(|_| err(line, format!("bad word `{w}`")))?;
                (Some(addr), Some(word), text.trim().to_string())
            }
            _ => (None, None, t.to_string()),
        };
        f.items.push(Item::Ins {
            line,
            addr,
            word,
            text,
        });
    }
    finish(&mut src, &mut cur, &mut data);
    Ok(src)
}

// ---------------------------------------------------------------- instructions

fn reg(s: &str, line: usize) -> Result<Reg, String> {
    let s = s.trim();
    let abi = [
        "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
        "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
        "t5", "t6",
    ];
    if let Some(k) = abi.iter().position(|r| *r == s) {
        return Ok(Reg(k as u8));
    }
    if s == "fp" {
        return Ok(Reg(8));
    }
    if let Some(n) = s.strip_prefix('x').and_then(|n| n.parse::<u8>().ok()) {
        if n < 32 {
            return Ok(Reg(n));
        }
    }
    Err(err(line, format!("`{s}` is not a register")))
}

fn int(s: &str, line: usize) -> Result<i64, String> {
    let s = s.trim();
    let (neg, m) = match s.strip_prefix('-') {
        Some(m) => (true, m),
        None => (false, s),
    };
    let v = if let Some(h) = m.strip_prefix("0x") {
        i64::from_str_radix(h, 16)
    } else {
        m.parse::<i64>()
    }
    .map_err(|_| err(line, format!("`{s}` is not a number")))?;
    Ok(if neg { -v } else { v })
}

/// A signed immediate of `bits` bits (`scale`: the low bits that must be 0).
fn simm(v: i64, bits: u8, line: usize) -> Result<Imm, String> {
    let lo = -(1i64 << (bits - 1));
    let hi = (1i64 << (bits - 1)) - 1;
    if v < lo || v > hi {
        return Err(err(line, format!("{v} does not fit in {bits} signed bits")));
    }
    Ok(Imm {
        value: (v as u64 & ((1u64 << bits) - 1)) as u32,
        bits,
    })
}

fn uimm(v: i64, bits: u8, line: usize) -> Result<Imm, String> {
    if v < 0 || v >= 1i64 << bits {
        return Err(err(
            line,
            format!("{v} does not fit in {bits} unsigned bits"),
        ));
    }
    Ok(Imm {
        value: v as u32,
        bits,
    })
}

/// `off(reg)`.
fn mem_operand(s: &str, line: usize) -> Result<(i64, Reg), String> {
    let s = s.trim();
    let (o, r) = s
        .split_once('(')
        .ok_or_else(|| err(line, format!("`{s}`: want off(reg)")))?;
    let r = r
        .strip_suffix(')')
        .ok_or_else(|| err(line, format!("`{s}`: want off(reg)")))?;
    let o = if o.trim().is_empty() {
        0
    } else {
        int(o, line)?
    };
    Ok((o, reg(r, line)?))
}

macro_rules! by_mnemonic {
    ($ty:ident, [$($v:ident),*]) => {
        |m: &str| -> Option<$ty> { [$($ty::$v),*].into_iter().find(|o| o.mnemonic() == m) }
    };
}

/// What a branch or jump goes to, before addresses are known.
#[derive(Clone, Debug)]
enum Target {
    Abs(u64),
    Label(String),
}

/// An instruction whose target, if any, is still symbolic.
#[derive(Clone, Debug)]
enum Pre {
    Done(Instr),
    Jal(Reg, Target),
    Branch(BrOp, Reg, Reg, Target),
    /// `la rd, @label`: auipc rd + addi rd, rd (two words).
    La(Reg, String),
}

impl Pre {
    fn words(&self) -> u64 {
        match self {
            Pre::La(..) => 2,
            _ => 1,
        }
    }
}

fn target(s: &str, line: usize) -> Result<Target, String> {
    let s = s.trim();
    if let Some(h) = s.strip_prefix("0x") {
        return u64::from_str_radix(h, 16)
            .map(Target::Abs)
            .map_err(|_| err(line, format!("bad target `{s}`")));
    }
    let l = s.strip_prefix('@').unwrap_or(s);
    if is_name(l) {
        Ok(Target::Label(l.to_string()))
    } else {
        Err(err(line, format!("bad target `{s}`")))
    }
}

fn parse_instr(text: &str, line: usize) -> Result<Pre, String> {
    let (m, rest) = text.split_once(char::is_whitespace).unwrap_or((text, ""));
    let ops: Vec<&str> = if rest.trim().is_empty() {
        vec![]
    } else {
        rest.split(',').map(|o| o.trim()).collect()
    };
    let n = |k: usize| -> Result<(), String> {
        if ops.len() == k {
            Ok(())
        } else {
            Err(err(
                line,
                format!("`{m}` takes {k} operands, has {}", ops.len()),
            ))
        }
    };
    let br = by_mnemonic!(BrOp, [Beq, Bne, Blt, Bge, Bltu, Bgeu]);
    let ld = by_mnemonic!(LdOp, [Lb, Lh, Lw, Ld, Lbu, Lhu, Lwu]);
    let st = by_mnemonic!(StOp, [Sb, Sh, Sw, Sd]);
    let io = by_mnemonic!(IOp, [Addi, Slti, Sltiu, Xori, Ori, Andi]);
    let sh = by_mnemonic!(ShOp, [Slli, Srli, Srai, Rori, Slliuw]);
    let shw = by_mnemonic!(ShWOp, [Slliw, Srliw, Sraiw, Roriw]);
    let rop = by_mnemonic!(
        ROp,
        [
            Add, Sub, Sll, Slt, Sltu, Xor, Srl, Sra, Or, And, Mul, Mulh, Mulhsu, Mulhu, Div, Divu,
            Rem, Remu, Sh1add, Sh2add, Sh3add, Andn, Orn, Xnor, Max, Maxu, Min, Minu, Rol, Ror
        ]
    );
    let rwop = by_mnemonic!(
        RWOp,
        [
            Addw, Subw, Sllw, Srlw, Sraw, Mulw, Divw, Divuw, Remw, Remuw, Adduw, Sh1adduw,
            Sh2adduw, Sh3adduw, Rolw, Rorw
        ]
    );
    let uop = by_mnemonic!(
        UOp,
        [
            Clz, Ctz, Cpop, Clzw, Ctzw, Cpopw, Sextb, Sexth, Zexth, Rev8, Orcb
        ]
    );
    let done = Pre::Done;
    Ok(match m {
        "lui" | "auipc" => {
            n(2)?;
            let rd = reg(ops[0], line)?;
            let i = uimm(int(ops[1], line)?, 20, line)?;
            done(if m == "lui" {
                Instr::Lui(rd, i)
            } else {
                Instr::Auipc(rd, i)
            })
        }
        "jal" => {
            n(2)?;
            Pre::Jal(reg(ops[0], line)?, target(ops[1], line)?)
        }
        "jalr" => {
            n(2)?;
            let (o, rs1) = mem_operand(ops[1], line)?;
            done(Instr::Jalr(reg(ops[0], line)?, rs1, simm(o, 12, line)?))
        }
        "ecall" => {
            n(0)?;
            done(Instr::Ecall)
        }
        ".word" => {
            return Err(err(
                line,
                "`.word`: a word outside the profile cannot be assembled",
            ));
        }
        // Pseudo-instructions (never printed by `disasm`).
        "nop" => {
            n(0)?;
            done(Instr::IOp(IOp::Addi, Reg(0), Reg(0), simm(0, 12, line)?))
        }
        "li" => {
            n(2)?;
            done(Instr::IOp(
                IOp::Addi,
                reg(ops[0], line)?,
                Reg(0),
                simm(int(ops[1], line)?, 12, line)?,
            ))
        }
        "mv" => {
            n(2)?;
            done(Instr::IOp(
                IOp::Addi,
                reg(ops[0], line)?,
                reg(ops[1], line)?,
                simm(0, 12, line)?,
            ))
        }
        "ret" => {
            n(0)?;
            done(Instr::Jalr(Reg(0), Reg(1), simm(0, 12, line)?))
        }
        "j" | "br" => {
            n(1)?;
            Pre::Jal(Reg(0), target(ops[0], line)?)
        }
        "call" => {
            n(1)?;
            Pre::Jal(Reg(1), target(ops[0], line)?)
        }
        "tail" => {
            n(1)?;
            Pre::Jal(Reg(0), target(ops[0], line)?)
        }
        "beqz" | "bnez" => {
            n(2)?;
            let op = if m == "beqz" { BrOp::Beq } else { BrOp::Bne };
            Pre::Branch(op, reg(ops[0], line)?, Reg(0), target(ops[1], line)?)
        }
        "la" => {
            n(2)?;
            let l = ops[1].strip_prefix('@').unwrap_or(ops[1]);
            Pre::La(reg(ops[0], line)?, l.to_string())
        }
        _ => {
            if let Some(op) = br(m) {
                n(3)?;
                Pre::Branch(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    target(ops[2], line)?,
                )
            } else if let Some(op) = ld(m) {
                n(2)?;
                let (o, rs1) = mem_operand(ops[1], line)?;
                done(Instr::Load(op, reg(ops[0], line)?, rs1, simm(o, 12, line)?))
            } else if let Some(op) = st(m) {
                n(2)?;
                let (o, rs1) = mem_operand(ops[1], line)?;
                done(Instr::Store(
                    op,
                    rs1,
                    reg(ops[0], line)?,
                    simm(o, 12, line)?,
                ))
            } else if let Some(op) = io(m) {
                n(3)?;
                done(Instr::IOp(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    simm(int(ops[2], line)?, 12, line)?,
                ))
            } else if m == "addiw" {
                n(3)?;
                done(Instr::Addiw(
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    simm(int(ops[2], line)?, 12, line)?,
                ))
            } else if let Some(op) = sh(m) {
                n(3)?;
                done(Instr::Shift(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    uimm(int(ops[2], line)?, 6, line)?,
                ))
            } else if let Some(op) = shw(m) {
                n(3)?;
                done(Instr::ShiftW(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    uimm(int(ops[2], line)?, 5, line)?,
                ))
            } else if let Some(op) = rop(m) {
                n(3)?;
                done(Instr::ROp(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    reg(ops[2], line)?,
                ))
            } else if let Some(op) = rwop(m) {
                n(3)?;
                done(Instr::RWOp(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    reg(ops[2], line)?,
                ))
            } else if let Some(op) = uop(m) {
                n(2)?;
                done(Instr::UOp(op, reg(ops[0], line)?, reg(ops[1], line)?))
            } else {
                return Err(err(line, format!("unknown instruction `{m}`")));
            }
        }
    })
}

// ---------------------------------------------------------------- encoding

fn r_type(opc: u32, rd: Reg, f3: u32, rs1: Reg, rs2: Reg, f7: u32) -> u32 {
    opc | (rd.0 as u32) << 7 | f3 << 12 | (rs1.0 as u32) << 15 | (rs2.0 as u32) << 20 | f7 << 25
}

fn i_type(opc: u32, rd: Reg, f3: u32, rs1: Reg, imm12: u32) -> u32 {
    opc | (rd.0 as u32) << 7 | f3 << 12 | (rs1.0 as u32) << 15 | (imm12 & 0xfff) << 20
}

/// The word for an instruction: the inverse of `isa::decode` (tests/asm.rs).
pub fn encode(i: &Instr) -> u32 {
    use Instr::*;
    match *i {
        Lui(rd, im) => 0x37 | (rd.0 as u32) << 7 | im.value << 12,
        Auipc(rd, im) => 0x17 | (rd.0 as u32) << 7 | im.value << 12,
        Jal(rd, im) => {
            let v = im.value;
            0x6f | (rd.0 as u32) << 7
                | ((v >> 12) & 0xff) << 12
                | ((v >> 11) & 1) << 20
                | ((v >> 1) & 0x3ff) << 21
                | ((v >> 20) & 1) << 31
        }
        Jalr(rd, rs1, im) => i_type(0x67, rd, 0, rs1, im.value),
        Branch(op, a, b, im) => {
            let f3 = match op {
                BrOp::Beq => 0,
                BrOp::Bne => 1,
                BrOp::Blt => 4,
                BrOp::Bge => 5,
                BrOp::Bltu => 6,
                BrOp::Bgeu => 7,
            };
            let v = im.value;
            0x63 | ((v >> 11) & 1) << 7
                | ((v >> 1) & 0xf) << 8
                | f3 << 12
                | (a.0 as u32) << 15
                | (b.0 as u32) << 20
                | ((v >> 5) & 0x3f) << 25
                | ((v >> 12) & 1) << 31
        }
        Load(op, rd, rs1, im) => {
            let f3 = match op {
                LdOp::Lb => 0,
                LdOp::Lh => 1,
                LdOp::Lw => 2,
                LdOp::Ld => 3,
                LdOp::Lbu => 4,
                LdOp::Lhu => 5,
                LdOp::Lwu => 6,
            };
            i_type(0x03, rd, f3, rs1, im.value)
        }
        Store(op, rs1, rs2, im) => {
            let f3 = match op {
                StOp::Sb => 0,
                StOp::Sh => 1,
                StOp::Sw => 2,
                StOp::Sd => 3,
            };
            let v = im.value;
            0x23 | (v & 0x1f) << 7
                | f3 << 12
                | (rs1.0 as u32) << 15
                | (rs2.0 as u32) << 20
                | ((v >> 5) & 0x7f) << 25
        }
        IOp(op, rd, rs1, im) => {
            let f3 = match op {
                isa::IOp::Addi => 0,
                isa::IOp::Slti => 2,
                isa::IOp::Sltiu => 3,
                isa::IOp::Xori => 4,
                isa::IOp::Ori => 6,
                isa::IOp::Andi => 7,
            };
            i_type(0x13, rd, f3, rs1, im.value)
        }
        Addiw(rd, rs1, im) => i_type(0x1b, rd, 0, rs1, im.value),
        Shift(op, rd, rs1, sh) => match op {
            ShOp::Slli => i_type(0x13, rd, 1, rs1, sh.value),
            ShOp::Srli => i_type(0x13, rd, 5, rs1, sh.value),
            ShOp::Srai => i_type(0x13, rd, 5, rs1, 0x400 | sh.value),
            ShOp::Rori => i_type(0x13, rd, 5, rs1, 0x600 | sh.value),
            ShOp::Slliuw => i_type(0x1b, rd, 1, rs1, 0x080 | sh.value),
        },
        ShiftW(op, rd, rs1, sh) => match op {
            ShWOp::Slliw => i_type(0x1b, rd, 1, rs1, sh.value),
            ShWOp::Srliw => i_type(0x1b, rd, 5, rs1, sh.value),
            ShWOp::Sraiw => i_type(0x1b, rd, 5, rs1, 0x400 | sh.value),
            ShWOp::Roriw => i_type(0x1b, rd, 5, rs1, 0x600 | sh.value),
        },
        ROp(op, rd, a, b) => {
            use crate::isa::ROp::*;
            let (f7, f3) = match op {
                Add => (0x00, 0),
                Sub => (0x20, 0),
                Sll => (0x00, 1),
                Slt => (0x00, 2),
                Sltu => (0x00, 3),
                Xor => (0x00, 4),
                Srl => (0x00, 5),
                Sra => (0x20, 5),
                Or => (0x00, 6),
                And => (0x00, 7),
                Mul => (0x01, 0),
                Mulh => (0x01, 1),
                Mulhsu => (0x01, 2),
                Mulhu => (0x01, 3),
                Div => (0x01, 4),
                Divu => (0x01, 5),
                Rem => (0x01, 6),
                Remu => (0x01, 7),
                Sh1add => (0x10, 2),
                Sh2add => (0x10, 4),
                Sh3add => (0x10, 6),
                Andn => (0x20, 7),
                Orn => (0x20, 6),
                Xnor => (0x20, 4),
                Max => (0x05, 6),
                Maxu => (0x05, 7),
                Min => (0x05, 4),
                Minu => (0x05, 5),
                Rol => (0x30, 1),
                Ror => (0x30, 5),
            };
            r_type(0x33, rd, f3, a, b, f7)
        }
        RWOp(op, rd, a, b) => {
            use crate::isa::RWOp::*;
            let (f7, f3) = match op {
                Addw => (0x00, 0),
                Subw => (0x20, 0),
                Sllw => (0x00, 1),
                Srlw => (0x00, 5),
                Sraw => (0x20, 5),
                Mulw => (0x01, 0),
                Divw => (0x01, 4),
                Divuw => (0x01, 5),
                Remw => (0x01, 6),
                Remuw => (0x01, 7),
                Adduw => (0x04, 0),
                Sh1adduw => (0x10, 2),
                Sh2adduw => (0x10, 4),
                Sh3adduw => (0x10, 6),
                Rolw => (0x30, 1),
                Rorw => (0x30, 5),
            };
            r_type(0x3b, rd, f3, a, b, f7)
        }
        UOp(op, rd, rs1) => {
            use crate::isa::UOp::*;
            match op {
                Clz => i_type(0x13, rd, 1, rs1, 0x600),
                Ctz => i_type(0x13, rd, 1, rs1, 0x601),
                Cpop => i_type(0x13, rd, 1, rs1, 0x602),
                Sextb => i_type(0x13, rd, 1, rs1, 0x604),
                Sexth => i_type(0x13, rd, 1, rs1, 0x605),
                Rev8 => i_type(0x13, rd, 5, rs1, 0x6b8),
                Orcb => i_type(0x13, rd, 5, rs1, 0x287),
                Clzw => i_type(0x1b, rd, 1, rs1, 0x600),
                Ctzw => i_type(0x1b, rd, 1, rs1, 0x601),
                Cpopw => i_type(0x1b, rd, 1, rs1, 0x602),
                Zexth => r_type(0x3b, rd, 4, rs1, Reg(0), 0x04),
            }
        }
        Ecall => 0x73,
    }
}

// ---------------------------------------------------------------- assembling

/// One assembled function.
#[derive(Clone, Debug)]
pub struct AsmFunc {
    pub name: String,
    pub entry: u64,
    pub words: Vec<u32>,
    pub nodes: Vec<Node>,
    /// Loop heads with their annotations (pc, invariant, measure).
    pub loops: Vec<(u64, Option<String>, Option<String>)>,
    pub spec: Option<String>,
    pub intro: Option<String>,
}

/// An assembled data section.
#[derive(Clone, Debug)]
pub struct AsmData {
    pub name: String,
    pub addr: u64,
    pub bytes: Vec<u8>,
    pub zero: bool,
    pub writable: bool,
}

/// The result of `assemble`: everything `write_elf` needs.
#[derive(Clone, Debug)]
pub struct Assembled {
    pub funcs: Vec<AsmFunc>,
    pub data: Vec<AsmData>,
    pub metas: Vec<FuncMeta>,
    pub imports: Vec<String>,
    pub opens: Vec<String>,
    /// The namespace the skeleton's theorems go in (`#namespace`).
    pub namespace: Option<String>,
}

impl Assembled {
    pub fn text_addr(&self) -> u64 {
        self.funcs
            .iter()
            .map(|f| f.entry)
            .min()
            .unwrap_or(DEFAULT_TEXT)
    }
    /// `.text`: every function at its address, gaps zero.
    pub fn text(&self) -> Vec<u32> {
        let lo = self.text_addr();
        let hi = self
            .funcs
            .iter()
            .map(|f| f.entry + 4 * f.words.len() as u64)
            .max()
            .unwrap_or(lo);
        let mut t = vec![0u32; ((hi - lo) / 4) as usize];
        for f in &self.funcs {
            let k = ((f.entry - lo) / 4) as usize;
            t[k..k + f.words.len()].copy_from_slice(&f.words);
        }
        t
    }
}

/// Assemble structured assembly. Errors are positioned (`line N: ...`); a
/// function that does not conform to the profile is an error too, with the
/// checker's violations.
pub fn assemble(text: &str) -> Result<Assembled, String> {
    let src = parse_source(text)?;
    if src.funcs.is_empty() {
        return Err("no functions".into());
    }
    // Pass 1: parse instructions, lay out functions.
    let mut pres: Vec<Vec<Option<Pre>>> = Vec::new();
    let mut entries: BTreeMap<String, u64> = BTreeMap::new();
    let mut starts = Vec::new();
    let mut next = DEFAULT_TEXT;
    for f in &src.funcs {
        let entry = f.addr.unwrap_or(next);
        if entry % 4 != 0 {
            return Err(err(
                f.line,
                format!("{} at {entry:#x} is not 4-aligned", f.name),
            ));
        }
        if entries.insert(f.name.clone(), entry).is_some() {
            return Err(err(f.line, format!("function {} defined twice", f.name)));
        }
        let mut ps = Vec::new();
        let mut words = 0u64;
        for it in &f.items {
            match it {
                Item::Ins { line, text, .. } => {
                    let p = parse_instr(text, *line)?;
                    words += p.words();
                    ps.push(Some(p));
                }
                _ => ps.push(None),
            }
        }
        starts.push(entry);
        next = entry + 4 * words;
        pres.push(ps);
    }
    // Data: explicit addresses, or after the text, each 8-aligned.
    let text_end = src
        .funcs
        .iter()
        .zip(&pres)
        .zip(&starts)
        .map(|((_, ps), &e)| e + 4 * ps.iter().flatten().map(|p| p.words()).sum::<u64>())
        .max()
        .unwrap_or(DEFAULT_TEXT);
    let mut dnext = (text_end + 0xfff) & !0xfff;
    let mut labels: BTreeMap<String, u64> = BTreeMap::new();
    let mut data = Vec::new();
    for d in &src.data {
        let addr = d.addr.unwrap_or(dnext);
        dnext = (addr + d.bytes.len() as u64 + 7) & !7;
        for (l, off) in &d.labels {
            if labels.insert(l.clone(), addr + *off as u64).is_some() {
                return Err(err(d.line, format!("data label @{l} defined twice")));
            }
        }
        data.push(AsmData {
            name: d.name.clone(),
            addr,
            bytes: d.bytes.clone(),
            zero: d.zero,
            writable: d.writable,
        });
    }
    // Pass 2: addresses, the tree, targets.
    let mut out = Vec::new();
    for ((f, ps), &entry) in src.funcs.iter().zip(&pres).zip(&starts) {
        struct Open {
            kind: Kind,
            start: u64,
            line: usize,
            children: Vec<Node>,
        }
        // Label resolution needs each block's end, so first compute every
        // node's interval, then encode.
        let mut pc = entry;
        let mut stack: Vec<Open> = Vec::new();
        let mut top: Vec<Node> = Vec::new();
        let mut spans: BTreeMap<usize, (Kind, u64, u64)> = BTreeMap::new(); // item index of Open -> span
        let mut open_idx: Vec<usize> = Vec::new();
        for (k, (it, p)) in f.items.iter().zip(ps).enumerate() {
            match it {
                Item::Open { kind, line, .. } => {
                    stack.push(Open {
                        kind: *kind,
                        start: pc,
                        line: *line,
                        children: vec![],
                    });
                    open_idx.push(k);
                }
                Item::Close { kind, line } => {
                    let o = stack
                        .pop()
                        .ok_or_else(|| err(*line, "`end` without an open block or loop"))?;
                    let oi = open_idx.pop().unwrap();
                    if o.kind != *kind {
                        return Err(err(
                            *line,
                            format!("`end` closes the {:?} opened at line {}", o.kind, o.line),
                        ));
                    }
                    if o.start == pc {
                        return Err(err(*line, "an empty block or loop"));
                    }
                    spans.insert(oi, (o.kind, o.start, pc));
                    let n = Node {
                        kind: o.kind,
                        start: o.start,
                        end: pc,
                        children: o.children,
                    };
                    match stack.last_mut() {
                        Some(parent) => parent.children.push(n),
                        None => top.push(n),
                    }
                }
                Item::Ins { line, addr, .. } => {
                    if let Some(a) = addr {
                        if *a != pc {
                            return Err(err(
                                *line,
                                format!("the listing says {a:#x}, the instruction is at {pc:#x}"),
                            ));
                        }
                    }
                    pc += 4 * p.as_ref().unwrap().words();
                }
            }
        }
        if let Some(o) = stack.last() {
            return Err(err(o.line, format!("{:?} not closed", o.kind)));
        }
        // Encode, resolving labels against the enclosing nodes.
        let mut words = Vec::new();
        let mut pc = entry;
        let mut enclosing: Vec<(Option<String>, Kind, u64, u64)> = Vec::new();
        let mut loops = Vec::new();
        for (k, (it, p)) in f.items.iter().zip(ps).enumerate() {
            match it {
                Item::Open {
                    label,
                    kind,
                    inv,
                    measure,
                    ..
                } => {
                    let (_, s, e) = spans[&k];
                    enclosing.push((label.clone(), *kind, s, e));
                    if *kind == Kind::Loop {
                        loops.push((s, inv.clone(), measure.clone()));
                    }
                }
                Item::Close { .. } => {
                    enclosing.pop();
                }
                Item::Ins { line, word, .. } => {
                    let resolve = |t: &Target| -> Result<u64, String> {
                        match t {
                            Target::Abs(a) => Ok(*a),
                            Target::Label(l) => {
                                if let Some((_, kind, s, e)) =
                                    enclosing.iter().rev().find(|x| x.0.as_deref() == Some(l))
                                {
                                    return Ok(if *kind == Kind::Loop { *s } else { *e });
                                }
                                if let Some(&e) = entries.get(l) {
                                    return Ok(e);
                                }
                                Err(err(
                                    *line,
                                    format!(
                                        "@{l} is neither an enclosing block or loop nor a function"
                                    ),
                                ))
                            }
                        }
                    };
                    let off = |a: u64| a.wrapping_sub(pc) as i64;
                    let ins: Vec<Instr> = match p.as_ref().unwrap() {
                        Pre::Done(i) => vec![*i],
                        Pre::Jal(rd, t) => {
                            vec![Instr::Jal(*rd, simm(off(resolve(t)?), 21, *line)?)]
                        }
                        Pre::Branch(op, a, b, t) => {
                            vec![Instr::Branch(
                                *op,
                                *a,
                                *b,
                                simm(off(resolve(t)?), 13, *line)?,
                            )]
                        }
                        Pre::La(rd, l) => {
                            let a = *labels
                                .get(l)
                                .ok_or_else(|| err(*line, format!("no data label @{l}")))?;
                            let o = off(a);
                            let hi = (o + 0x800) >> 12;
                            let lo = o - (hi << 12);
                            vec![
                                Instr::Auipc(
                                    *rd,
                                    Imm {
                                        value: (hi as u64 & 0xfffff) as u32,
                                        bits: 20,
                                    },
                                ),
                                Instr::IOp(IOp::Addi, *rd, *rd, simm(lo, 12, *line)?),
                            ]
                        }
                    };
                    for i in ins {
                        let w = encode(&i);
                        words.push(w);
                        pc += 4;
                    }
                    if let Some(w) = word {
                        if matches!(p, Some(Pre::La(..))) {
                            return Err(err(*line, "`la` is two words; a listing line has one"));
                        }
                        if *w != *words.last().unwrap() {
                            return Err(err(
                                *line,
                                format!(
                                    "the listing says {w:08x}, the instruction encodes as {:08x}",
                                    words.last().unwrap()
                                ),
                            ));
                        }
                    }
                }
            }
        }
        out.push(AsmFunc {
            name: f.name.clone(),
            entry,
            words,
            nodes: top,
            loops,
            spec: f.spec.clone(),
            intro: f.intro.clone(),
        });
    }
    // Overlaps.
    let mut spans: Vec<(u64, u64, &str)> = out
        .iter()
        .map(|f| (f.entry, f.entry + 4 * f.words.len() as u64, f.name.as_str()))
        .collect();
    spans.sort();
    for w in spans.windows(2) {
        if w[0].1 > w[1].0 {
            return Err(format!("{} and {} overlap", w[0].2, w[1].2));
        }
    }
    // Check every function against the profile, with the tree as written.
    let entry_set: BTreeSet<u64> = out.iter().map(|f| f.entry).collect();
    let mut metas = Vec::new();
    let mut bad = Vec::new();
    for f in &out {
        let func = Func {
            name: f.name.clone(),
            entry: f.entry,
            words: f.words.clone(),
        };
        match profile::check(&func, &f.nodes, &entry_set) {
            Ok(m) => metas.push(m),
            Err(vs) => bad.extend(vs.into_iter().map(|v| format!("{} {v}", f.name))),
        }
    }
    if !bad.is_empty() {
        return Err(format!(
            "does not conform to the profile:\n  {}",
            bad.join("\n  ")
        ));
    }
    Ok(Assembled {
        funcs: out,
        data,
        metas,
        imports: src.imports,
        opens: src.opens,
        namespace: src.namespace,
    })
}

// ---------------------------------------------------------------- ELF

/// A static RV64 executable: `.text`, the data sections, `.nocompiler.struct`,
/// symbols. Entry `_start` if there is one, else the first function.
pub fn write_elf(a: &Assembled) -> Result<Vec<u8>, String> {
    struct Sec {
        name: String,
        kind: u32,
        flags: u64,
        addr: u64,
        data: Vec<u8>,
        size: u64,
        link: u32,
        info: u32,
        align: u64,
        entsize: u64,
        offset: u64,
    }
    let text: Vec<u8> = a.text().iter().flat_map(|w| w.to_le_bytes()).collect();
    let mut secs = vec![Sec {
        name: ".text".into(),
        kind: 1,
        flags: 2 | 4,
        addr: a.text_addr(),
        size: text.len() as u64,
        data: text,
        link: 0,
        info: 0,
        align: 4,
        entsize: 0,
        offset: 0,
    }];
    for d in &a.data {
        secs.push(Sec {
            name: d.name.clone(),
            kind: if d.zero { 8 } else { 1 },
            flags: 2 | if d.writable { 1 } else { 0 },
            addr: d.addr,
            size: d.bytes.len() as u64,
            data: if d.zero { vec![] } else { d.bytes.clone() },
            link: 0,
            info: 0,
            align: 1,
            entsize: 0,
            offset: 0,
        });
    }
    let nalloc = secs.len();
    // Overlapping allocated sections.
    let mut iv: Vec<(u64, u64, &str)> = secs
        .iter()
        .map(|s| (s.addr, s.addr + s.size, s.name.as_str()))
        .collect();
    iv.sort();
    for w in iv.windows(2) {
        if w[0].1 > w[1].0 {
            return Err(format!("sections {} and {} overlap", w[0].2, w[1].2));
        }
    }
    secs.push(Sec {
        name: meta::SECTION.into(),
        kind: 1,
        flags: 0,
        addr: 0,
        data: meta::encode(&a.metas),
        size: 0,
        link: 0,
        info: 0,
        align: 1,
        entsize: 0,
        offset: 0,
    });
    // Symbols: null, then the functions (global FUNC, in `.text`).
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 24];
    for f in &a.funcs {
        let name = strtab.len() as u32;
        strtab.extend_from_slice(f.name.as_bytes());
        strtab.push(0);
        symtab.extend_from_slice(&name.to_le_bytes());
        symtab.push(0x12); // STB_GLOBAL, STT_FUNC
        symtab.push(0);
        symtab.extend_from_slice(&1u16.to_le_bytes()); // .text
        symtab.extend_from_slice(&f.entry.to_le_bytes());
        symtab.extend_from_slice(&(4 * f.words.len() as u64).to_le_bytes());
    }
    let nsec = secs.len();
    secs.push(Sec {
        name: ".symtab".into(),
        kind: 2,
        flags: 0,
        addr: 0,
        data: symtab,
        size: 0,
        link: (nsec + 2) as u32, // .strtab
        info: 1,                 // first global
        align: 8,
        entsize: 24,
        offset: 0,
    });
    secs.push(Sec {
        name: ".shstrtab".into(),
        kind: 3,
        flags: 0,
        addr: 0,
        data: vec![],
        size: 0,
        link: 0,
        info: 0,
        align: 1,
        entsize: 0,
        offset: 0,
    });
    secs.push(Sec {
        name: ".strtab".into(),
        kind: 3,
        flags: 0,
        addr: 0,
        data: strtab,
        size: 0,
        link: 0,
        info: 0,
        align: 1,
        entsize: 0,
        offset: 0,
    });
    let mut shstr = vec![0u8];
    let mut name_off = Vec::new();
    for s in &secs {
        name_off.push(shstr.len() as u32);
        shstr.extend_from_slice(s.name.as_bytes());
        shstr.push(0);
    }
    let shi = secs.iter().position(|s| s.name == ".shstrtab").unwrap();
    secs[shi].data = shstr;
    for s in secs.iter_mut() {
        if s.kind != 8 {
            s.size = s.data.len() as u64;
        }
    }
    // File layout: allocated sections at `vaddr - base` (so that offset and
    // address agree modulo the page size), the rest after them.
    let phnum = nalloc as u64;
    let hdr = 64 + 56 * phnum;
    let lo = secs[..nalloc].iter().map(|s| s.addr).min().unwrap();
    let mut base = lo & !0xfff;
    while lo - base < hdr {
        base = base
            .checked_sub(0x1000)
            .ok_or("sections too low in memory")?;
    }
    let mut end = hdr;
    for s in secs[..nalloc].iter_mut() {
        s.offset = s.addr - base;
        if s.kind != 8 {
            end = end.max(s.offset + s.size);
        }
    }
    if end > 64 << 20 {
        return Err("the sections span more than 64 MiB".into());
    }
    for s in secs[nalloc..].iter_mut() {
        end = end.div_ceil(s.align) * s.align;
        s.offset = end;
        end += s.size;
    }
    let shoff = (end + 7) & !7;
    let total = shoff + 64 * (secs.len() as u64 + 1);
    let mut b = vec![0u8; total as usize];
    // ELF header.
    b[..4].copy_from_slice(b"\x7fELF");
    b[4] = 2; // ELFCLASS64
    b[5] = 1; // little-endian
    b[6] = 1; // EV_CURRENT
    let entry = a
        .funcs
        .iter()
        .find(|f| f.name == "_start")
        .or(a.funcs.first())
        .map(|f| f.entry)
        .unwrap_or(0);
    let mut put = |o: usize, v: &[u8]| b[o..o + v.len()].copy_from_slice(v);
    put(16, &2u16.to_le_bytes()); // ET_EXEC
    put(18, &243u16.to_le_bytes()); // EM_RISCV
    put(20, &1u32.to_le_bytes());
    put(24, &entry.to_le_bytes());
    put(32, &64u64.to_le_bytes()); // phoff
    put(40, &shoff.to_le_bytes());
    put(48, &0u32.to_le_bytes()); // flags: no RVC, soft-float ABI (lp64)
    put(52, &64u16.to_le_bytes());
    put(54, &56u16.to_le_bytes());
    put(56, &(phnum as u16).to_le_bytes());
    put(58, &64u16.to_le_bytes());
    put(60, &((secs.len() + 1) as u16).to_le_bytes());
    put(62, &((shi + 1) as u16).to_le_bytes());
    // Program headers: one PT_LOAD per allocated section.
    let mut order: Vec<usize> = (0..nalloc).collect();
    order.sort_by_key(|&k| secs[k].addr); // PT_LOAD in ascending address order
    for (k, s) in order.iter().map(|&i| &secs[i]).enumerate() {
        let o = 64 + 56 * k;
        let flags: u32 =
            4 | if s.flags & 1 != 0 { 2 } else { 0 } | if s.flags & 4 != 0 { 1 } else { 0 };
        // Each segment starts at its page, as loaders expect (lld does the same).
        let pad = s.addr & 0xfff;
        put(o, &1u32.to_le_bytes());
        put(o + 4, &flags.to_le_bytes());
        put(o + 8, &(s.offset - pad).to_le_bytes());
        put(o + 16, &(s.addr - pad).to_le_bytes());
        put(o + 24, &(s.addr - pad).to_le_bytes());
        put(
            o + 32,
            &(pad + if s.kind == 8 { 0 } else { s.size }).to_le_bytes(),
        );
        put(o + 40, &(pad + s.size).to_le_bytes());
        put(o + 48, &0x1000u64.to_le_bytes());
    }
    for s in &secs {
        if s.kind != 8 {
            put(s.offset as usize, &s.data);
        }
    }
    // Section headers (index 0 is null).
    for (k, s) in secs.iter().enumerate() {
        let o = shoff as usize + 64 * (k + 1);
        put(o, &name_off[k].to_le_bytes());
        put(o + 4, &s.kind.to_le_bytes());
        put(o + 8, &s.flags.to_le_bytes());
        put(o + 16, &s.addr.to_le_bytes());
        put(o + 24, &s.offset.to_le_bytes());
        put(o + 32, &s.size.to_le_bytes());
        // .symtab links .strtab by its header index (+1 for the null header).
        let link = if s.kind == 2 { s.link + 1 } else { s.link };
        put(o + 40, &link.to_le_bytes());
        put(o + 44, &s.info.to_le_bytes());
        put(o + 48, &s.align.to_le_bytes());
        put(o + 56, &s.entsize.to_le_bytes());
    }
    Ok(b)
}

// ---------------------------------------------------------------- Lean

/// A proof skeleton for every function with a `#spec`: the theorem, its
/// `rintro`, and one `nocompiler_auto` call with the loop annotations as its
/// invariants and measures (in tree order). What is left after it are the
/// verification conditions, as named goals. `image` is the namespace the
/// image was exported under (`nocompiler export --namespace`).
pub fn skeleton(a: &Assembled, image: &str, source: &str) -> String {
    let mut o = String::new();
    let _ = writeln!(o, "import {image}");
    for i in &a.imports {
        let _ = writeln!(o, "import {i}");
    }
    let _ = writeln!(
        o,
        "\n/- Generated by `nocompiler asm` from {source}: the theorem, the call to\n   nocompiler_auto with the source's loop annotations, and nothing else. The\n   verification conditions are what is left; prove them below the marker. -/"
    );
    let mut opens = vec![
        "NoCompiler".to_string(),
        "NoCompiler.Vocab".into(),
        image.to_string(),
    ];
    opens.extend(a.opens.iter().cloned());
    if let Some(ns) = &a.namespace {
        let _ = writeln!(o, "namespace {ns}");
    }
    let _ = writeln!(o, "open {}", opens.join(" "));
    for f in &a.funcs {
        let Some(spec) = &f.spec else { continue };
        let id = crate::lean::ident(&f.name);
        let _ = writeln!(o, "\nset_option maxHeartbeats 20000000 in");
        let _ = writeln!(
            o,
            "theorem {id}_verified : Verified code {id}_dom {id}_entry ({}) := by",
            spec.replace('\n', "\n    ")
        );
        let intro = f.intro.clone().unwrap_or_else(|| "a s he hpre".into());
        let _ = writeln!(o, "  rintro {}", intro.replace('\n', "\n    "));
        let _ = writeln!(o, "  nocompiler_auto {id}_func s he");
        for (pc, inv, measure) in &f.loops {
            let inv = inv
                .clone()
                .unwrap_or_else(|| "fun _ => True  -- no #inv in the source".into());
            let measure = measure
                .clone()
                .unwrap_or_else(|| "fun _ => 0  -- no #measure in the source".into());
            let _ = writeln!(
                o,
                "    loop_inv 0x{pc:x} ({})",
                inv.replace('\n', "\n        ")
            );
            let _ = writeln!(o, "      measure ({})", measure.replace('\n', "\n        "));
        }
        let _ = writeln!(o, "  -- verification conditions ({id})");
    }
    o
}

/// One instruction in listing syntax, at `pc` (absolute targets only): for
/// tests of the parser and encoder against `isa::decode` and `Instr::asm`.
pub fn assemble_one(text: &str, pc: u64) -> Result<u32, String> {
    let i = match parse_instr(text, 0)? {
        Pre::Done(i) => i,
        Pre::Jal(rd, Target::Abs(a)) => Instr::Jal(rd, simm(a.wrapping_sub(pc) as i64, 21, 0)?),
        Pre::Branch(op, a, b, Target::Abs(t)) => {
            Instr::Branch(op, a, b, simm(t.wrapping_sub(pc) as i64, 13, 0)?)
        }
        _ => return Err("a symbolic target or a pseudo-instruction of two words".into()),
    };
    Ok(encode(&i))
}
