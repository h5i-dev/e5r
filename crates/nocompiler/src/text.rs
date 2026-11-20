//! The structured text form (docs/isa/v1.md, "The structured form";
//! docs/isa/asm.md): what `nocompiler disasm` prints for a profile binary and
//! `nocompiler asm` reads back.
//!
//! A function is its block/loop tree with the profile's instructions as
//! leaves. Branches name an enclosing block (its end) or loop (its head) by
//! label, so R3 holds by construction; calls name their callee (`call f`,
//! `tail f`: two words each, `R_RISCV_CALL_PLT`); data addresses name a
//! symbol (`auipc rd, %pcrel_hi(sym)` and `%pcrel_lo(sym)` in the immediate of
//! the instructions that use it). Every statement is a fixed number of words
//! and no address appears, so the text is relocatable: `asm` writes an ELF
//! relocatable object (one `.text.NAME` section per function, `.rela`
//! sections, the data sections, and a `.nocompiler.struct` v2 table), which
//! ld.lld links like any other.
//!
//! Neither direction is trusted. `asm` checks every function it writes
//! against the profile (R1 to R6, with the frame partition the text declares)
//! and refuses one that does not conform; a proof is checked by the Lean
//! kernel against the bytes of whatever binary the object ends up in.

use crate::Binary;
use crate::frame::Partition;
use crate::isa::{self, BrOp, IOp, Imm, Instr, LdOp, ROp, RWOp, Reg, ShOp, ShWOp, StOp, UOp};
use crate::module::{self, Kind as RKind, Reloc};
use crate::profile::{self, Func, Kind, Level, Node, Range, RangeSource, Slot, SlotKind};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

fn err(line: usize, msg: impl std::fmt::Display) -> String {
    format!("line {line}: {msg}")
}

fn is_name(s: &str) -> bool {
    let mut c = s.chars();
    matches!(c.next(), Some(ch) if ch.is_ascii_alphabetic() || ch == '_' || ch == '.' || ch == '$')
        && s.chars()
            .all(|ch| ch.is_ascii_alphanumeric() || "_.$".contains(ch))
}

const ABI: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

// ---------------------------------------------------------------- printing

fn sym_ref(sym: &str, addend: i64) -> String {
    match addend {
        0 => sym.to_string(),
        a if a > 0 => format!("{sym}+{a}"),
        a => format!("{sym}{a}"),
    }
}

/// The text of a binary: every function (in address order), then the data
/// sections. A function that does not reach L1 is listed as a comment.
pub fn print(bin: &Binary, only: Option<&str>) -> Result<String, String> {
    let m = module::of_binary(bin)?;
    let reports = bin.check();
    let mut out = String::new();
    let mut funcs: Vec<_> = bin.funcs.iter().zip(&reports).collect();
    funcs.sort_by_key(|(f, _)| f.entry);
    for (f, r) in funcs {
        if only.is_some_and(|o| o != f.name) {
            continue;
        }
        let rf = m
            .funcs
            .iter()
            .find(|g| g.name == f.name)
            .ok_or("function not in its module")?;
        let meta = match &r.result {
            Ok(meta) => meta,
            Err(vs) => {
                let _ = writeln!(
                    out,
                    "\n; func {} at {:#x}: below L1, not listed",
                    f.name, f.entry
                );
                for v in vs {
                    let _ = writeln!(out, ";   {v}");
                }
                continue;
            }
        };
        let _ = writeln!(
            out,
            "\nfunc {}                ; {:#x}, {:?}",
            f.name, f.entry, meta.level
        );
        if meta.frame > 0 {
            let _ = writeln!(out, "  frame {}", meta.frame);
            let mut parts: Vec<(u64, String)> = Vec::new();
            for s in &meta.slots {
                let what = match s.kind {
                    SlotKind::Save(r) => format!("save {}", ABI[r.0 as usize]),
                    SlotKind::Spill => "spill".into(),
                };
                parts.push((s.off, format!("slot {} {what}", s.off)));
            }
            for g in &meta.ranges {
                parts.push((g.off, format!("mem {} {}", g.off, g.len)));
            }
            parts.sort();
            for (_, p) in parts {
                let _ = writeln!(out, "    {p}");
            }
        }
        // Labels: the recorded ones, else $b<k>/$l<k> in pre-order.
        let mut flat: Vec<(Kind, u64, u64, String, usize)> = Vec::new();
        fn walk(
            ns: &[Node],
            d: usize,
            k: &mut usize,
            out: &mut Vec<(Kind, u64, u64, String, usize)>,
        ) {
            for n in ns {
                let l = n
                    .label
                    .clone()
                    .map(|l| l.trim_start_matches('$').to_string())
                    .unwrap_or_else(|| {
                        format!("{}{}", if n.kind == Kind::Loop { "l" } else { "b" }, *k)
                    });
                *k += 1;
                out.push((n.kind, n.start, n.end, l, d));
                walk(&n.children, d + 1, k, out);
            }
        }
        walk(&meta.nodes, 0, &mut 0, &mut flat);
        let target = |pc: u64, t: u64| -> Option<String> {
            flat.iter()
                .filter(|n| n.1 <= pc && pc < n.2)
                .filter(|n| (n.0 == Kind::Block && n.2 == t) || (n.0 == Kind::Loop && n.1 == t))
                .max_by_key(|n| n.4)
                .map(|n| format!("${}", n.3))
        };
        let reloc_at = |off: u64| rf.relocs.iter().find(|r| r.off == off);
        let mut k = 0;
        while k < f.words.len() {
            let pc = f.entry + 4 * k as u64;
            for n in flat.iter().filter(|n| n.2 == pc).rev() {
                let _ = writeln!(out, "  {:ind$}end", "", ind = 2 * n.4);
            }
            for n in flat.iter().filter(|n| n.1 == pc) {
                let kw = if n.0 == Kind::Loop { "loop" } else { "block" };
                let note = if n.0 == Kind::Loop {
                    format!("        ; head {pc:#x}")
                } else {
                    String::new()
                };
                let _ = writeln!(out, "  {:ind$}{kw} ${}{note}", "", n.3, ind = 2 * n.4);
            }
            let depth = flat.iter().filter(|n| n.1 <= pc && pc < n.2).count();
            let ind = 2 + 2 * depth;
            let i = isa::decode(f.words[k])
                .ok_or_else(|| format!("{}: {pc:#x} does not decode", f.name))?;
            let text = match (reloc_at(4 * k as u64), i) {
                (Some(r), _) if r.kind == RKind::Call => {
                    let tail = matches!(isa::decode(f.words[k + 1]), Some(Instr::Jalr(Reg(0), ..)));
                    k += 1;
                    format!("{} {}", if tail { "tail" } else { "call" }, r.sym)
                }
                (Some(r), Instr::Auipc(rd, _)) => {
                    format!("auipc {rd}, %pcrel_hi({})", sym_ref(&r.sym, r.addend))
                }
                (Some(r), Instr::IOp(op, rd, rs1, _)) => {
                    format!(
                        "{} {rd}, {rs1}, %pcrel_lo({})",
                        op.mnemonic(),
                        sym_ref(&r.sym, r.addend)
                    )
                }
                (Some(r), Instr::Load(op, rd, rs1, _)) => {
                    format!(
                        "{} {rd}, %pcrel_lo({})({rs1})",
                        op.mnemonic(),
                        sym_ref(&r.sym, r.addend)
                    )
                }
                (Some(r), Instr::Store(op, rs1, rs2, _)) => {
                    format!(
                        "{} {rs2}, %pcrel_lo({})({rs1})",
                        op.mnemonic(),
                        sym_ref(&r.sym, r.addend)
                    )
                }
                (Some(_), _) => {
                    return Err(format!("{}: unexpected relocation at {pc:#x}", f.name));
                }
                (None, Instr::Jalr(Reg(0), Reg(1), imm)) if imm.signed() == 0 => "ret".into(),
                (None, Instr::Jal(Reg(0), imm)) => {
                    let t = pc.wrapping_add(imm.signed() as u64);
                    format!(
                        "j {}",
                        target(pc, t)
                            .ok_or_else(|| format!("{}: jump at {pc:#x} has no label", f.name))?
                    )
                }
                (None, Instr::Branch(op, a, b, imm)) => {
                    let t = pc.wrapping_add(imm.signed() as u64);
                    let l = target(pc, t)
                        .ok_or_else(|| format!("{}: branch at {pc:#x} has no label", f.name))?;
                    format!("{} {a}, {b}, {l}", op.mnemonic())
                }
                (None, Instr::Jal(..)) => {
                    return Err(format!(
                        "{}: a jal call at {pc:#x} (only auipc/jalr calls)",
                        f.name
                    ));
                }
                (None, i) => i.asm(pc),
            };
            let _ = writeln!(out, "{:ind$}{text}", "");
            k += 1;
        }
        for n in flat.iter().filter(|n| n.2 == f.end()).rev() {
            let _ = writeln!(out, "  {:ind$}end", "", ind = 2 * n.4);
        }
    }
    if only.is_none() {
        for g in &bin.segments {
            let fl = if g.writable { "rw" } else { "r" };
            let al = if g.align > 1 {
                format!(" align {}", g.align)
            } else {
                String::new()
            };
            if g.zero {
                let _ = writeln!(out, "\nbss {} {} {fl}{al}", g.name, g.bytes.len());
                continue;
            }
            let _ = writeln!(out, "\ndata {} {fl}{al}", g.name);
            for c in g.bytes.chunks(16) {
                let hex: Vec<String> = c.iter().map(|b| format!("{b:02x}")).collect();
                let _ = writeln!(out, "  {}", hex.join(" "));
            }
        }
    }
    Ok(out)
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

// ---------------------------------------------------------------- parsing

/// A symbol plus an addend: `sym`, `sym+8`, `sym-4`.
fn sym_operand(s: &str, line: usize) -> Result<(String, i64), String> {
    let s = s.trim();
    let (name, add) = match s[1..].find(['+', '-']) {
        Some(k) => (
            &s[..k + 1],
            int(&s[k + 1..], line)? * if &s[k + 1..k + 2] == "-" { -1 } else { 1 },
        ),
        None => (s, 0),
    };
    if !is_name(name) {
        return Err(err(line, format!("`{name}` is not a symbol")));
    }
    Ok((name.to_string(), add))
}

/// `%pcrel_hi(x)` / `%pcrel_lo(x)`, if `s` is one.
fn pcrel(s: &str, which: &str, line: usize) -> Result<Option<(String, i64)>, String> {
    let s = s.trim();
    let Some(rest) = s.strip_prefix(which) else {
        return Ok(None);
    };
    let inner = rest
        .strip_prefix('(')
        .and_then(|r| r.strip_suffix(')'))
        .ok_or_else(|| err(line, format!("`{s}`: want {which}(sym)")))?;
    sym_operand(inner, line).map(Some)
}

/// One statement of a function body.
#[derive(Clone, Debug)]
enum Stmt {
    /// One instruction, encoded.
    Ins(Instr),
    Branch(BrOp, Reg, Reg, String),
    Jump(String),
    /// `call f` (`ra`) or `tail f` (`t1`, `jalr zero`): two words.
    Call(String, bool),
    /// `auipc rd, %pcrel_hi(sym)`.
    Hi(Reg, String, i64),
    /// An instruction whose 12-bit immediate is `%pcrel_lo(sym)`; S-type or not.
    Lo(Instr, String, i64, bool),
}

impl Stmt {
    fn words(&self) -> u64 {
        if matches!(self, Stmt::Call(..)) { 2 } else { 1 }
    }
}

fn label(s: &str, line: usize) -> Result<String, String> {
    let l = s
        .trim()
        .strip_prefix('$')
        .ok_or_else(|| err(line, format!("`{s}`: a target is a $label")))?;
    if is_name(l) {
        Ok(l.to_string())
    } else {
        Err(err(line, format!("`{s}` is not a label")))
    }
}

fn parse_stmt(text: &str, line: usize) -> Result<Stmt, String> {
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
    let z12 = Imm { value: 0, bits: 12 };
    Ok(match m {
        "call" | "tail" => {
            n(1)?;
            let f = ops[0];
            if !is_name(f) || f.starts_with('$') {
                return Err(err(line, format!("`{f}` is not a function")));
            }
            Stmt::Call(f.to_string(), m == "tail")
        }
        "ret" => {
            n(0)?;
            Stmt::Ins(Instr::Jalr(Reg(0), Reg(1), z12))
        }
        "j" => {
            n(1)?;
            Stmt::Jump(label(ops[0], line)?)
        }
        "jal" | "jalr" if ops.len() == 2 && m == "jal" => {
            return Err(err(line, "`jal`: write `j $label` or `call f`"));
        }
        "jalr" => {
            n(2)?;
            let (o, rs1) = mem_operand(ops[1], line)?;
            Stmt::Ins(Instr::Jalr(reg(ops[0], line)?, rs1, simm(o, 12, line)?))
        }
        "lui" | "auipc" => {
            n(2)?;
            let rd = reg(ops[0], line)?;
            if m == "auipc" {
                if let Some((s, a)) = pcrel(ops[1], "%pcrel_hi", line)? {
                    return Ok(Stmt::Hi(rd, s, a));
                }
                return Err(err(line, "`auipc`: its operand is %pcrel_hi(sym)"));
            }
            Stmt::Ins(Instr::Lui(rd, uimm(int(ops[1], line)?, 20, line)?))
        }
        "ecall" => {
            n(0)?;
            Stmt::Ins(Instr::Ecall)
        }
        _ => {
            if let Some(op) = br(m) {
                n(3)?;
                Stmt::Branch(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    label(ops[2], line)?,
                )
            } else if let Some(op) = ld(m) {
                n(2)?;
                let rd = reg(ops[0], line)?;
                if let Some(p) = ops[1].find("%pcrel_lo") {
                    let close = ops[1][p..]
                        .find(')')
                        .ok_or_else(|| err(line, "unclosed %pcrel_lo"))?
                        + p
                        + 1;
                    let (s, a) = pcrel(&ops[1][p..close], "%pcrel_lo", line)?.unwrap();
                    let (_, rs1) = mem_operand(&format!("0{}", &ops[1][close..]), line)?;
                    return Ok(Stmt::Lo(Instr::Load(op, rd, rs1, z12), s, a, false));
                }
                let (o, rs1) = mem_operand(ops[1], line)?;
                Stmt::Ins(Instr::Load(op, rd, rs1, simm(o, 12, line)?))
            } else if let Some(op) = st(m) {
                n(2)?;
                let rs2 = reg(ops[0], line)?;
                if let Some(p) = ops[1].find("%pcrel_lo") {
                    let close = ops[1][p..]
                        .find(')')
                        .ok_or_else(|| err(line, "unclosed %pcrel_lo"))?
                        + p
                        + 1;
                    let (s, a) = pcrel(&ops[1][p..close], "%pcrel_lo", line)?.unwrap();
                    let (_, rs1) = mem_operand(&format!("0{}", &ops[1][close..]), line)?;
                    return Ok(Stmt::Lo(Instr::Store(op, rs1, rs2, z12), s, a, true));
                }
                let (o, rs1) = mem_operand(ops[1], line)?;
                Stmt::Ins(Instr::Store(op, rs1, rs2, simm(o, 12, line)?))
            } else if let Some(op) = io(m) {
                n(3)?;
                let (rd, rs1) = (reg(ops[0], line)?, reg(ops[1], line)?);
                if let Some((s, a)) = pcrel(ops[2], "%pcrel_lo", line)? {
                    if op != IOp::Addi {
                        return Err(err(line, "%pcrel_lo only in addi, loads and stores"));
                    }
                    return Ok(Stmt::Lo(Instr::IOp(op, rd, rs1, z12), s, a, false));
                }
                Stmt::Ins(Instr::IOp(op, rd, rs1, simm(int(ops[2], line)?, 12, line)?))
            } else if m == "addiw" {
                n(3)?;
                Stmt::Ins(Instr::Addiw(
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    simm(int(ops[2], line)?, 12, line)?,
                ))
            } else if let Some(op) = sh(m) {
                n(3)?;
                Stmt::Ins(Instr::Shift(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    uimm(int(ops[2], line)?, 6, line)?,
                ))
            } else if let Some(op) = shw(m) {
                n(3)?;
                Stmt::Ins(Instr::ShiftW(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    uimm(int(ops[2], line)?, 5, line)?,
                ))
            } else if let Some(op) = rop(m) {
                n(3)?;
                Stmt::Ins(Instr::ROp(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    reg(ops[2], line)?,
                ))
            } else if let Some(op) = rwop(m) {
                n(3)?;
                Stmt::Ins(Instr::RWOp(
                    op,
                    reg(ops[0], line)?,
                    reg(ops[1], line)?,
                    reg(ops[2], line)?,
                ))
            } else if let Some(op) = uop(m) {
                n(2)?;
                Stmt::Ins(Instr::UOp(op, reg(ops[0], line)?, reg(ops[1], line)?))
            } else {
                return Err(err(line, format!("unknown instruction `{m}`")));
            }
        }
    })
}

#[derive(Clone, Debug)]
enum Item {
    Stmt(usize, Stmt),
    Open(usize, Kind, String),
    Close(usize),
}

#[derive(Clone, Debug, Default)]
struct SrcFunc {
    name: String,
    line: usize,
    items: Vec<Item>,
    frame: Option<u64>,
    slots: Vec<Slot>,
    ranges: Vec<Range>,
}

/// A data section of the text.
#[derive(Clone, Debug)]
pub struct Data {
    pub name: String,
    pub bytes: Vec<u8>,
    pub zero: bool,
    pub writable: bool,
    pub align: u64,
}

/// One assembled function: its relocatable form and what the checker found.
#[derive(Clone, Debug)]
pub struct Assembled {
    pub func: module::RFunc,
    /// The tree, with offsets from the function's start.
    pub nodes: Vec<Node>,
    pub meta: profile::FuncMeta,
}

#[derive(Clone, Debug)]
pub struct Object {
    pub funcs: Vec<Assembled>,
    pub data: Vec<Data>,
    /// The trial layout the functions were checked at (symbol to address).
    pub trial: BTreeMap<String, u64>,
}

fn parse(text: &str) -> Result<(Vec<SrcFunc>, Vec<Data>), String> {
    let mut funcs: Vec<SrcFunc> = Vec::new();
    let mut data: Vec<Data> = Vec::new();
    let mut in_data = false;
    let mut in_frame = false;
    for (i, raw) in text.lines().enumerate() {
        let line = i + 1;
        let t = raw.find(';').map(|k| &raw[..k]).unwrap_or(raw).trim();
        if t.is_empty() {
            continue;
        }
        let ws: Vec<&str> = t.split_whitespace().collect();
        match ws[0] {
            "func" => {
                let [_, name] = ws[..] else {
                    return Err(err(line, "`func NAME`"));
                };
                if !is_name(name) {
                    return Err(err(line, format!("`{name}` is not a name")));
                }
                funcs.push(SrcFunc {
                    name: name.into(),
                    line,
                    ..Default::default()
                });
                in_data = false;
                in_frame = false;
                continue;
            }
            "data" | "bss" => {
                let w = |k: usize| ws.get(k).copied().unwrap_or("");
                let (name, size, fl, rest) = if ws[0] == "data" {
                    (w(1), None, w(2), 3)
                } else {
                    (w(1), Some(w(2)), w(3), 4)
                };
                let align = match &ws[rest.min(ws.len())..] {
                    [] => 1,
                    ["align", n] => n
                        .parse::<u64>()
                        .ok()
                        .filter(|a| a.is_power_of_two())
                        .ok_or_else(|| err(line, "`align N`, a power of two"))?,
                    _ => {
                        return Err(err(
                            line,
                            "`data NAME r|rw [align N]` or `bss NAME SIZE r|rw [align N]`",
                        ));
                    }
                };
                if !is_name(name) || !(fl == "r" || fl == "rw") {
                    return Err(err(
                        line,
                        "`data NAME r|rw [align N]` or `bss NAME SIZE r|rw [align N]`",
                    ));
                }
                let bytes = match size {
                    Some(n) => vec![0; n.parse::<usize>().map_err(|_| err(line, "bad size"))?],
                    None => vec![],
                };
                data.push(Data {
                    name: name.into(),
                    bytes,
                    zero: size.is_some(),
                    writable: fl == "rw",
                    align,
                });
                in_data = size.is_none();
                in_frame = false;
                continue;
            }
            _ => {}
        }
        if in_data {
            let d = data.last_mut().unwrap();
            for h in &ws {
                if h.len() != 2 {
                    return Err(err(line, format!("`{h}`: data is hex bytes")));
                }
                d.bytes.push(
                    u8::from_str_radix(h, 16)
                        .map_err(|_| err(line, format!("`{h}` is not hex")))?,
                );
            }
            continue;
        }
        let f = funcs
            .last_mut()
            .ok_or_else(|| err(line, "a statement outside a function"))?;
        match ws[0] {
            "frame" => {
                let [_, n] = ws[..] else {
                    return Err(err(line, "`frame N`"));
                };
                if f.frame.is_some() || !f.items.is_empty() {
                    return Err(err(line, "`frame` comes first, once"));
                }
                f.frame = Some(n.parse().map_err(|_| err(line, "bad frame size"))?);
                in_frame = true;
            }
            "slot" | "mem" if in_frame => {
                let num = |s: &str| {
                    s.parse::<u64>()
                        .map_err(|_| err(line, format!("`{s}` is not a number")))
                };
                if ws[0] == "mem" {
                    let [_, k, n] = ws[..] else {
                        return Err(err(line, "`mem OFF LEN`"));
                    };
                    f.ranges.push(Range {
                        off: num(k)?,
                        len: num(n)?,
                        source: RangeSource::Declared,
                    });
                } else {
                    let kind = match ws[..] {
                        [_, _, "spill"] => SlotKind::Spill,
                        [_, _, "save", r] => SlotKind::Save(reg(r, line)?),
                        _ => return Err(err(line, "`slot OFF save REG` or `slot OFF spill`")),
                    };
                    f.slots.push(Slot {
                        off: num(ws[1])?,
                        kind,
                    });
                }
            }
            "block" | "loop" => {
                in_frame = false;
                let [_, l] = ws[..] else {
                    return Err(err(line, format!("`{} $label`", ws[0])));
                };
                let kind = if ws[0] == "loop" {
                    Kind::Loop
                } else {
                    Kind::Block
                };
                f.items.push(Item::Open(line, kind, label(l, line)?));
            }
            "end" => {
                in_frame = false;
                if ws.len() != 1 {
                    return Err(err(line, "`end` takes nothing"));
                }
                f.items.push(Item::Close(line));
            }
            _ => {
                in_frame = false;
                f.items.push(Item::Stmt(line, parse_stmt(t, line)?));
            }
        }
    }
    Ok((funcs, data))
}

/// Patch a function's words for an address map: what a linker does
/// (the formulas of lean/NoCompiler/Module.lean, `Reloc.apply`).
pub fn patch(
    f: &module::RFunc,
    at: u64,
    addr: &dyn Fn(&str) -> Option<u64>,
) -> Result<Vec<u32>, String> {
    let mut w = f.words.clone();
    for r in &f.relocs {
        let t = addr(&r.sym).ok_or_else(|| format!("{}: no address for {}", f.name, r.sym))?;
        let d = t.wrapping_add(r.addend as u64).wrapping_sub(at + r.hi_off) as i64;
        if !(-(1i64 << 31) - (1 << 11)..(1i64 << 31) - (1 << 11)).contains(&d) {
            return Err(format!("{}: {} out of reach", f.name, r.sym));
        }
        let hi = ((d + 0x800) >> 12) as u32 & 0xfffff;
        let lo = (d & 0xfff) as u32;
        let k = (r.off / 4) as usize;
        match r.kind {
            RKind::Call => {
                w[k] |= hi << 12;
                w[k + 1] |= lo << 20;
            }
            RKind::PcrelHi => w[k] |= hi << 12,
            RKind::PcrelLoI => w[k] |= lo << 20,
            RKind::PcrelLoS => w[k] |= ((lo & 0x1f) << 7) | ((lo >> 5) << 25),
        }
    }
    Ok(w)
}

/// Assemble the text into a relocatable object, checking every function
/// against the profile. Errors carry a line number, or the violations.
pub fn assemble(text: &str) -> Result<Object, String> {
    let (src, data) = parse(text)?;
    if src.is_empty() {
        return Err("no functions".into());
    }
    let mut names = BTreeSet::new();
    for f in &src {
        if !names.insert(f.name.clone()) {
            return Err(err(f.line, format!("function {} twice", f.name)));
        }
    }
    let mut out = Vec::new();
    for f in &src {
        // Offsets, the tree, the labels.
        let mut off = 0u64;
        let mut stack: Vec<(Kind, String, u64, usize, Vec<Node>)> = Vec::new();
        let mut top = Vec::new();
        let mut spans: BTreeMap<usize, (Kind, u64, u64)> = BTreeMap::new();
        let mut opens = Vec::new();
        for (k, it) in f.items.iter().enumerate() {
            match it {
                Item::Open(line, kind, l) => {
                    stack.push((*kind, l.clone(), off, *line, vec![]));
                    opens.push(k);
                }
                Item::Close(line) => {
                    let (kind, l, start, _, children) = stack
                        .pop()
                        .ok_or_else(|| err(*line, "`end` with nothing open"))?;
                    if start == off {
                        return Err(err(*line, "an empty block or loop"));
                    }
                    spans.insert(opens.pop().unwrap(), (kind, start, off));
                    let n = Node {
                        kind,
                        start,
                        end: off,
                        label: Some(format!("${l}")),
                        children,
                    };
                    match stack.last_mut() {
                        Some(p) => p.4.push(n),
                        None => top.push(n),
                    }
                }
                Item::Stmt(_, s) => off += 4 * s.words(),
            }
        }
        if let Some(o) = stack.last() {
            return Err(err(o.3, format!("${} not closed", o.1)));
        }
        // Encode.
        let mut words: Vec<u32> = Vec::new();
        let mut relocs = Vec::new();
        let mut enclosing: Vec<(String, Kind, u64, u64)> = Vec::new();
        let mut his: Vec<(String, i64, u64)> = Vec::new();
        for (k, it) in f.items.iter().enumerate() {
            match it {
                Item::Open(_, kind, l) => {
                    let (_, s, e) = spans[&k];
                    enclosing.push((l.clone(), *kind, s, e));
                }
                Item::Close(_) => {
                    enclosing.pop();
                }
                Item::Stmt(line, s) => {
                    let pc = 4 * words.len() as u64;
                    let resolve = |l: &str| -> Result<u64, String> {
                        enclosing
                            .iter()
                            .rev()
                            .find(|x| x.0 == l)
                            .map(|x| if x.1 == Kind::Loop { x.2 } else { x.3 })
                            .ok_or_else(|| {
                                err(*line, format!("${l} is not an enclosing block or loop"))
                            })
                    };
                    let off = |t: u64| t.wrapping_sub(pc) as i64;
                    match s {
                        Stmt::Ins(i) => words.push(encode(i)),
                        Stmt::Branch(op, a, b, l) => words.push(encode(&Instr::Branch(
                            *op,
                            *a,
                            *b,
                            simm(off(resolve(l)?), 13, *line)?,
                        ))),
                        Stmt::Jump(l) => words.push(encode(&Instr::Jal(
                            Reg(0),
                            simm(off(resolve(l)?), 21, *line)?,
                        ))),
                        Stmt::Call(g, tail) => {
                            let r = if *tail { Reg(6) } else { Reg(1) };
                            relocs.push(Reloc {
                                off: pc,
                                kind: RKind::Call,
                                sym: g.clone(),
                                addend: 0,
                                hi_off: pc,
                            });
                            words.push(encode(&Instr::Auipc(r, Imm { value: 0, bits: 20 })));
                            words.push(encode(&Instr::Jalr(
                                if *tail { Reg(0) } else { Reg(1) },
                                r,
                                Imm { value: 0, bits: 12 },
                            )));
                        }
                        Stmt::Hi(rd, sym, a) => {
                            relocs.push(Reloc {
                                off: pc,
                                kind: RKind::PcrelHi,
                                sym: sym.clone(),
                                addend: *a,
                                hi_off: pc,
                            });
                            his.push((sym.clone(), *a, pc));
                            words.push(encode(&Instr::Auipc(*rd, Imm { value: 0, bits: 20 })));
                        }
                        Stmt::Lo(i, sym, a, s_type) => {
                            let hi = his
                                .iter()
                                .rev()
                                .find(|h| h.0 == *sym && h.1 == *a)
                                .ok_or_else(|| {
                                    err(
                                        *line,
                                        format!(
                                            "%pcrel_lo({sym}) without an earlier %pcrel_hi({sym})"
                                        ),
                                    )
                                })?;
                            relocs.push(Reloc {
                                off: pc,
                                kind: if *s_type {
                                    RKind::PcrelLoS
                                } else {
                                    RKind::PcrelLoI
                                },
                                sym: sym.clone(),
                                addend: *a,
                                hi_off: hi.2,
                            });
                            words.push(encode(i));
                        }
                    }
                }
            }
        }
        out.push((
            f,
            module::RFunc {
                name: f.name.clone(),
                entry: 0,
                words,
                relocs,
            },
            top,
        ));
    }
    // Check every function at a trial layout: functions back to back from
    // 0x10000, data after them. Its bytes are layout-dependent; its tree,
    // level and frame are not.
    let mut at: BTreeMap<String, u64> = BTreeMap::new();
    let mut next = 0x10000u64;
    for (_, rf, _) in &out {
        at.insert(rf.name.clone(), next);
        next += 4 * rf.words.len() as u64;
    }
    next = (next + 0xfff) & !0xfff;
    for d in &data {
        if at.insert(d.name.clone(), next).is_some() {
            return Err(format!(
                "{} is both a function and a data section, or twice",
                d.name
            ));
        }
        next = (next + d.bytes.len() as u64 + 15) & !15;
    }
    // Symbols referenced but not defined here (another object's): addresses
    // of their own, past everything, so calls to them check as calls.
    let mut entries: BTreeSet<u64> = out.iter().map(|(_, rf, _)| at[&rf.name]).collect();
    for (_, rf, _) in &out {
        for r in &rf.relocs {
            if !at.contains_key(&r.sym) {
                next = (next + 0xfff) & !0xfff;
                at.insert(r.sym.clone(), next);
                if r.kind == RKind::Call {
                    entries.insert(next);
                }
            }
        }
    }
    let mut funcs = Vec::new();
    let mut bad = Vec::new();
    for (f, rf, top) in out {
        let a = at[&rf.name];
        let words = patch(&rf, a, &|s| at.get(s).copied())?;
        let func = Func {
            name: rf.name.clone(),
            entry: a,
            words,
        };
        fn shift(ns: &[Node], a: u64) -> Vec<Node> {
            ns.iter()
                .map(|n| Node {
                    kind: n.kind,
                    start: n.start + a,
                    end: n.end + a,
                    label: n.label.clone(),
                    children: shift(&n.children, a),
                })
                .collect()
        }
        let nodes = shift(&top, a);
        let part = f.frame.map(|_| Partition {
            slots: f.slots.clone(),
            ranges: f.ranges.clone(),
        });
        match profile::check_with(&func, &nodes, part.as_ref(), None, &entries) {
            Ok(c) => {
                // At L2 the frame is what the text declares; below L2 (L1:
                // R4 to R6 not met) the function is accepted with its level.
                if c.meta.level == Level::L2 {
                    if let Some(n) = f.frame {
                        if n != c.meta.frame {
                            bad.push(format!(
                                "{}: `frame {n}`, the code uses {}",
                                f.name, c.meta.frame
                            ));
                        }
                    } else if c.meta.frame > 0 {
                        bad.push(format!(
                            "{}: uses a {}-byte frame; declare it (`frame {}`)",
                            f.name, c.meta.frame, c.meta.frame
                        ));
                    }
                }
                funcs.push(Assembled {
                    func: rf,
                    nodes: top,
                    meta: c.meta,
                });
            }
            Err(e) => bad.extend(e.violations.into_iter().map(|v| format!("{} {v}", f.name))),
        }
    }
    if !bad.is_empty() {
        return Err(format!(
            "does not conform to the profile:\n  {}",
            bad.join("\n  ")
        ));
    }
    Ok(Object {
        funcs,
        data,
        trial: at,
    })
}

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
// ---------------------------------------------------------------- the object

const R_RISCV_CALL_PLT: u32 = 19;
const R_RISCV_PCREL_HI20: u32 = 23;
const R_RISCV_PCREL_LO12_I: u32 = 24;
const R_RISCV_PCREL_LO12_S: u32 = 25;

/// A relocation entry before symbol indices: offset, symbol key, type, addend.
type Rela = (u64, String, u32, i64);

struct Sec {
    name: String,
    kind: u32,
    flags: u64,
    data: Vec<u8>,
    size: u64,
    link: u32,
    info: u32,
    align: u64,
    entsize: u64,
}

impl Sec {
    fn new(name: &str, kind: u32, flags: u64, data: Vec<u8>, align: u64) -> Sec {
        Sec {
            name: name.into(),
            kind,
            flags,
            size: data.len() as u64,
            data,
            link: 0,
            info: 0,
            align,
            entsize: 0,
        }
    }
}

/// The object as an ELF64 RISC-V relocatable file: `.text.NAME` and
/// `.rela.text.NAME` per function, the data sections, `.nocompiler.struct`
/// (version 2, position-independent), symbols.
pub fn write_object(o: &Object) -> Result<Vec<u8>, String> {
    let mut secs: Vec<Sec> = vec![Sec::new("", 0, 0, vec![], 0)];
    // Symbols: (name, info, shndx, value, size); locals first.
    let mut locals: Vec<(String, u8, u16, u64, u64)> = Vec::new();
    let mut globals: Vec<(String, u8, u16, u64, u64)> = Vec::new();
    let mut text_idx = BTreeMap::new();
    for a in &o.funcs {
        let bytes: Vec<u8> = a.func.words.iter().flat_map(|w| w.to_le_bytes()).collect();
        text_idx.insert(a.func.name.clone(), secs.len());
        secs.push(Sec::new(
            &format!(".text.{}", a.func.name),
            1,
            2 | 4,
            bytes,
            4,
        ));
    }
    let mut data_idx = BTreeMap::new();
    for d in &o.data {
        data_idx.insert(d.name.clone(), secs.len());
        let mut s = Sec::new(
            &d.name,
            if d.zero { 8 } else { 1 },
            2 | if d.writable { 1 } else { 0 },
            if d.zero { vec![] } else { d.bytes.clone() },
            d.align,
        );
        s.size = d.bytes.len() as u64;
        secs.push(s);
        locals.push((String::new(), 3, (secs.len() - 1) as u16, 0, 0)); // STT_SECTION
    }
    // The metadata, at a trial layout (its encoding is position-independent).
    let names: BTreeMap<u64, String> = o.trial.iter().map(|(n, a)| (*a, n.clone())).collect();
    let metas: Vec<_> = o.funcs.iter().map(|a| a.meta.clone()).collect();
    secs.push(Sec::new(
        crate::meta::SECTION,
        1,
        0,
        crate::meta::encode(&metas, &names)?,
        1,
    ));
    for a in &o.funcs {
        globals.push((
            a.func.name.clone(),
            0x12,
            text_idx[&a.func.name] as u16,
            0,
            4 * a.func.words.len() as u64,
        ));
    }
    // Relocations: their symbols, then the sections.
    let mut relas: Vec<(usize, Vec<Rela>)> = Vec::new();
    for a in &o.funcs {
        let sec = text_idx[&a.func.name];
        let mut rs = Vec::new();
        for r in &a.func.relocs {
            let (ty, sym, add) = match r.kind {
                RKind::Call => (R_RISCV_CALL_PLT, format!("f:{}", r.sym), r.addend),
                RKind::PcrelHi => {
                    let label = format!(".Lpcrel_hi.{}.{}", a.func.name, r.off);
                    locals.push((label, 0, sec as u16, r.off, 0));
                    let target = if data_idx.contains_key(&r.sym) {
                        format!("d:{}", r.sym)
                    } else {
                        format!("f:{}", r.sym)
                    };
                    (R_RISCV_PCREL_HI20, target, r.addend)
                }
                RKind::PcrelLoI | RKind::PcrelLoS => (
                    if r.kind == RKind::PcrelLoI {
                        R_RISCV_PCREL_LO12_I
                    } else {
                        R_RISCV_PCREL_LO12_S
                    },
                    format!("l:.Lpcrel_hi.{}.{}", a.func.name, r.hi_off),
                    0,
                ),
            };
            rs.push((r.off, sym, ty, add));
        }
        if !rs.is_empty() {
            relas.push((sec, rs));
        }
    }
    // Undefined functions (called, not defined here).
    for (_, rs) in &relas {
        for (_, s, _, _) in rs {
            if let Some(f) = s.strip_prefix("f:") {
                if !text_idx.contains_key(f) && !globals.iter().any(|g| g.0 == f) {
                    globals.push((f.to_string(), 0x10, 0, 0, 0));
                }
            }
        }
    }
    let nlocal = 1 + locals.len();
    let syms: Vec<_> = locals.iter().chain(globals.iter()).cloned().collect();
    let index = |s: &str| -> Result<u32, String> {
        let k = if let Some(f) = s.strip_prefix("f:") {
            syms.iter().position(|x| x.0 == f && x.1 >> 4 == 1)
        } else if let Some(d) = s.strip_prefix("d:") {
            syms.iter()
                .position(|x| x.1 == 3 && x.2 as usize == data_idx[d])
        } else {
            syms.iter().position(|x| x.0 == s[2..])
        };
        k.map(|k| k as u32 + 1)
            .ok_or_else(|| format!("no symbol for {s}"))
    };
    let symtab_at = secs.len() + relas.len();
    for (sec, rs) in &relas {
        let mut b = Vec::new();
        for (off, s, ty, add) in rs {
            b.extend_from_slice(&off.to_le_bytes());
            b.extend_from_slice(&(((index(s)? as u64) << 32) | *ty as u64).to_le_bytes());
            b.extend_from_slice(&add.to_le_bytes());
        }
        let mut r = Sec::new(&format!(".rela{}", secs[*sec].name), 4, 0x40, b, 8);
        r.link = symtab_at as u32;
        r.info = *sec as u32;
        r.entsize = 24;
        secs.push(r);
    }
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 24];
    for (name, info, shndx, value, size) in &syms {
        let off = if name.is_empty() {
            0
        } else {
            let o = strtab.len() as u32;
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
            o
        };
        symtab.extend_from_slice(&off.to_le_bytes());
        symtab.push(*info);
        symtab.push(0);
        symtab.extend_from_slice(&shndx.to_le_bytes());
        symtab.extend_from_slice(&value.to_le_bytes());
        symtab.extend_from_slice(&size.to_le_bytes());
    }
    let mut st = Sec::new(".symtab", 2, 0, symtab, 8);
    st.link = (symtab_at + 1) as u32;
    st.info = nlocal as u32;
    st.entsize = 24;
    secs.push(st);
    secs.push(Sec::new(".strtab", 3, 0, strtab, 1));
    secs.push(Sec::new(".shstrtab", 3, 0, vec![], 1));
    let mut shstr = vec![0u8];
    let mut name_off = Vec::new();
    for s in &secs {
        if s.name.is_empty() {
            name_off.push(0u32);
            continue;
        }
        name_off.push(shstr.len() as u32);
        shstr.extend_from_slice(s.name.as_bytes());
        shstr.push(0);
    }
    let shi = secs.len() - 1;
    secs[shi].size = shstr.len() as u64;
    secs[shi].data = shstr;
    // Layout: header, section contents, section headers.
    let mut b = vec![0u8; 64];
    let mut offs = vec![0u64; secs.len()];
    for (k, s) in secs.iter().enumerate().skip(1) {
        let a = s.align.max(1) as usize;
        while b.len() % a != 0 {
            b.push(0);
        }
        offs[k] = b.len() as u64;
        b.extend_from_slice(&s.data);
    }
    while b.len() % 8 != 0 {
        b.push(0);
    }
    let shoff = b.len() as u64;
    for (k, s) in secs.iter().enumerate() {
        let mut h = Vec::with_capacity(64);
        h.extend_from_slice(&name_off[k].to_le_bytes());
        h.extend_from_slice(&s.kind.to_le_bytes());
        h.extend_from_slice(&s.flags.to_le_bytes());
        h.extend_from_slice(&0u64.to_le_bytes());
        h.extend_from_slice(&offs[k].to_le_bytes());
        h.extend_from_slice(&s.size.to_le_bytes());
        h.extend_from_slice(&s.link.to_le_bytes());
        h.extend_from_slice(&s.info.to_le_bytes());
        h.extend_from_slice(&s.align.to_le_bytes());
        h.extend_from_slice(&s.entsize.to_le_bytes());
        b.extend_from_slice(&h);
    }
    b[..4].copy_from_slice(b"\x7fELF");
    b[4] = 2;
    b[5] = 1;
    b[6] = 1;
    b[16..18].copy_from_slice(&1u16.to_le_bytes()); // ET_REL
    b[18..20].copy_from_slice(&243u16.to_le_bytes()); // EM_RISCV
    b[20..24].copy_from_slice(&1u32.to_le_bytes());
    b[40..48].copy_from_slice(&shoff.to_le_bytes());
    b[48..52].copy_from_slice(&0u32.to_le_bytes()); // no RVC, lp64 soft-float
    b[52..54].copy_from_slice(&64u16.to_le_bytes());
    b[58..60].copy_from_slice(&64u16.to_le_bytes());
    b[60..62].copy_from_slice(&(secs.len() as u16).to_le_bytes());
    b[62..64].copy_from_slice(&(shi as u16).to_le_bytes());
    Ok(b)
}
