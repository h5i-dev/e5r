//! `nocompiler module`: the relocatable module a linked binary was made from
//! (docs/isa/v1.md, relocation; `lean/NoCompiler/Module.lean`).
//!
//! Every function's words with the fields a relocation fills set to zero,
//! and the relocations, recovered from the code: an `auipc` followed by a
//! `jalr` through the same register is a call (`R_RISCV_CALL_PLT`) to the
//! function at its target; any other `auipc` is a `R_RISCV_PCREL_HI20` to the
//! data section (or function) holding its target, and each later instruction
//! that uses its register as a base, until the register is written again, is
//! the matching `R_RISCV_PCREL_LO12_I`/`_S`. The data sections are the
//! module's data symbols, by section name. Also the layout of the binary: the
//! address of every symbol, and the extent of `.text`.
//!
//! Nothing here is trusted: `nocompiler-audit` links the module at the layout
//! it reads itself from the ELF's symbol table and compares the result with
//! the ELF's `.text` and data, byte for byte.

use crate::Binary;
use crate::isa::{self, Instr, Reg};
use std::fmt::Write as _;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Call,
    PcrelHi,
    PcrelLoI,
    PcrelLoS,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reloc {
    pub off: u64,
    pub kind: Kind,
    pub sym: String,
    pub addend: i64,
    pub hi_off: u64,
}

#[derive(Clone, Debug)]
pub struct RFunc {
    pub name: String,
    pub entry: u64,
    pub words: Vec<u32>,
    pub relocs: Vec<Reloc>,
}

#[derive(Clone, Debug)]
pub struct RData {
    pub name: String,
    pub addr: u64,
    pub bytes: Vec<u8>,
    pub zero: bool,
    pub writable: bool,
}

#[derive(Clone, Debug)]
pub struct Skipped {
    pub name: String,
    pub entry: u64,
    pub reason: String,
}

#[derive(Clone, Debug)]
pub struct Module {
    pub funcs: Vec<RFunc>,
    pub data: Vec<RData>,
    /// The functions left out, with their entry and why: their code could not
    /// be made relocatable, or did not relink to the binary's words. Calls to
    /// them stay relocations to their symbol.
    pub skipped: Vec<Skipped>,
    pub text_addr: u64,
    pub text_words: usize,
}

fn sext(v: u32, bits: u32) -> i64 {
    let v = v as i64;
    if v & (1 << (bits - 1)) != 0 {
        v - (1 << bits)
    } else {
        v
    }
}

const U_FIELD: u32 = 0xffff_f000;
const I_FIELD: u32 = 0xfff0_0000;
const S_FIELD: u32 = 0xfe00_0f80;

/// The 12-bit immediate an instruction that may carry a LO12 relocation
/// uses with `rs1 = base`, and whether it is S-type.
fn lo_user(i: &Instr, base: Reg) -> Option<(i64, bool)> {
    match *i {
        Instr::IOp(isa::IOp::Addi, _, rs1, imm) if rs1 == base => Some((imm.signed(), false)),
        Instr::Load(_, _, rs1, imm) if rs1 == base => Some((imm.signed(), false)),
        Instr::Store(_, rs1, _, imm) if rs1 == base => Some((imm.signed(), true)),
        _ => None,
    }
}

fn reads_or_writes(i: &Instr, r: Reg) -> (bool, bool) {
    let writes = i.dest() == Some(r);
    let reads = match *i {
        Instr::Jalr(_, a, _)
        | Instr::Load(_, _, a, _)
        | Instr::IOp(_, _, a, _)
        | Instr::Addiw(_, a, _)
        | Instr::Shift(_, _, a, _)
        | Instr::ShiftW(_, _, a, _)
        | Instr::UOp(_, _, a) => a == r,
        Instr::Branch(_, a, b, _)
        | Instr::Store(_, a, b, _)
        | Instr::ROp(_, _, a, b)
        | Instr::RWOp(_, _, a, b) => a == r || b == r,
        _ => false,
    };
    (reads, writes)
}

/// The words of `f` with its relocations applied, at the addresses `addr`
/// gives (Lean `RFunc.patched`, NoCompiler/Module.lean: `Reloc.apply`).
pub fn patched(f: &RFunc, addr: &dyn Fn(&str) -> Option<u64>) -> Option<Vec<u32>> {
    let mut w = f.words.clone();
    for r in &f.relocs {
        let d = addr(&r.sym)?
            .wrapping_add(r.addend as u64)
            .wrapping_sub(f.entry.wrapping_add(r.hi_off));
        let hi20 = ((d.wrapping_add(0x800) >> 12) as u32) << 12;
        let lo12 = (d & 0xfff) as u32;
        let k = (r.off / 4) as usize;
        match r.kind {
            Kind::Call => {
                w[k] |= hi20;
                w[k + 1] |= lo12 << 20;
            }
            Kind::PcrelHi => w[k] |= hi20,
            Kind::PcrelLoI => w[k] |= lo12 << 20,
            Kind::PcrelLoS => w[k] |= ((lo12 & 0x1f) << 7) | ((lo12 >> 5) << 25),
        }
    }
    Some(w)
}

/// The module of a binary, or why its code is not relocatable. The module is
/// checked against the binary: every function, relinked at the binary's own
/// addresses, gives back the binary's words.
pub fn of_binary(bin: &Binary) -> Result<Module, String> {
    let mut m = of_binary_unchecked(bin)?;
    // Symbols resolve to every function of the binary, the skipped included.
    let entries: std::collections::HashMap<String, u64> = m
        .funcs
        .iter()
        .map(|f| (f.name.clone(), f.entry))
        .chain(m.skipped.iter().map(|f| (f.name.clone(), f.entry)))
        .collect();
    let data: Vec<(String, u64)> = m.data.iter().map(|d| (d.name.clone(), d.addr)).collect();
    let addr = |s: &str| -> Option<u64> {
        entries
            .get(s)
            .copied()
            .or_else(|| data.iter().find(|d| d.0 == s).map(|d| d.1))
    };
    let mut kept = Vec::new();
    for f in std::mem::take(&mut m.funcs) {
        let b = bin.funcs.iter().find(|g| g.entry == f.entry).unwrap();
        let bad = match patched(&f, &addr) {
            None => Some("a relocation names no symbol".to_string()),
            Some(w) if w != b.words => {
                let k = w
                    .iter()
                    .zip(&b.words)
                    .position(|(x, y)| x != y)
                    .unwrap_or(0);
                Some(format!(
                    "relinked at its own address, the word at {:#x} differs (a misattributed relocation)",
                    f.entry + 4 * k as u64
                ))
            }
            Some(_) => None,
        };
        match bad {
            None => kept.push(f),
            Some(reason) => m.skipped.push(Skipped {
                name: f.name.clone(),
                entry: f.entry,
                reason: format!("{}: {reason}", f.name),
            }),
        }
    }
    m.funcs = kept;
    m.skipped.sort_by_key(|f| f.entry);
    Ok(m)
}

/// A name per function, unique in the module: the symbol, or, when several
/// local functions share a symbol (a crate linked twice), the symbol with
/// `#k`, `k` its rank by address among them (stable while the linker keeps
/// their order).
fn unique_names(bin: &Binary) -> std::collections::HashMap<u64, String> {
    let mut by_name: std::collections::BTreeMap<&str, Vec<u64>> = Default::default();
    for f in &bin.funcs {
        by_name.entry(&f.name).or_default().push(f.entry);
    }
    let mut out = std::collections::HashMap::new();
    for (n, mut es) in by_name {
        es.sort();
        let dup = es.len() > 1;
        for (k, e) in es.into_iter().enumerate() {
            out.insert(
                e,
                if dup {
                    format!("{n}#{k}")
                } else {
                    n.to_string()
                },
            );
        }
    }
    out
}

const OTHER: u32 = 0;
const MANY: u32 = u32::MAX;

/// Reaching `auipc`s: for each instruction and register, `k + 1` if the
/// register's only reaching definition is the `auipc` at `k` (outside the
/// call pairs `calls`), `OTHER` if no `auipc` reaches it, `MANY` if several
/// definitions do. Successors: the next instruction, branch targets, `jal
/// zero` targets; a call (link register not zero) returns to the next one
/// and keeps only the callee-saved registers (sp, gp, tp, s0-s11); `jalr
/// zero` ends the path.
fn reaching_auipcs(words: &[u32], calls: &std::collections::BTreeSet<usize>) -> Vec<[u32; 32]> {
    let n = words.len();
    let mut ins: Vec<Option<[u32; 32]>> = vec![None; n];
    if n == 0 {
        return vec![];
    }
    ins[0] = Some([OTHER; 32]);
    let mut work = vec![0usize];
    while let Some(k) = work.pop() {
        let Some(st) = ins[k] else { continue };
        let Some(i) = isa::decode(words[k]) else {
            continue;
        };
        let mut out = st;
        match i {
            Instr::Auipc(rd, _) if rd.0 != 0 => {
                out[rd.0 as usize] = if calls.contains(&k) {
                    OTHER
                } else {
                    k as u32 + 1
                }
            }
            _ => {
                for r in 1..32u8 {
                    if reads_or_writes(&i, Reg(r)).1 {
                        out[r as usize] = OTHER;
                    }
                }
                let is_call = matches!(i, Instr::Jal(rd, _) | Instr::Jalr(rd, _, _) if rd.0 != 0);
                if is_call {
                    for (r, v) in out.iter_mut().enumerate().skip(1) {
                        if !matches!(r, 2 | 3 | 4 | 8 | 9 | 18..=27) {
                            *v = OTHER;
                        }
                    }
                }
                if matches!(i, Instr::Ecall) {
                    out[10] = OTHER;
                }
            }
        }
        let at = |off: i64| -> Option<usize> {
            let t = k as i64 + off / 4;
            (0..n as i64).contains(&t).then_some(t as usize)
        };
        let succ: Vec<Option<usize>> = match i {
            Instr::Branch(_, _, _, off) => vec![at(4), at(off.signed())],
            Instr::Jal(Reg(0), off) => vec![at(off.signed())],
            Instr::Jalr(Reg(0), _, _) => vec![],
            _ => vec![at(4)],
        };
        for t in succ.into_iter().flatten() {
            let new = match ins[t] {
                None => out,
                Some(old) => {
                    let mut m = old;
                    for (v, o) in m.iter_mut().zip(out.iter()) {
                        if *v != *o {
                            *v = MANY;
                        }
                    }
                    m
                }
            };
            if ins[t] != Some(new) {
                ins[t] = Some(new);
                work.push(t);
            }
        }
    }
    ins.into_iter().map(|x| x.unwrap_or([OTHER; 32])).collect()
}

fn of_binary_unchecked(bin: &Binary) -> Result<Module, String> {
    let names = unique_names(bin);
    let sym_at = |t: u64| -> Option<(String, i64)> {
        if let Some(n) = names.get(&t) {
            return Some((n.clone(), 0));
        }
        bin.segments
            .iter()
            .find(|g| t >= g.addr && t <= g.addr + g.bytes.len() as u64)
            .map(|g| (g.name.clone(), (t - g.addr) as i64))
    };
    let mut funcs = Vec::new();
    let mut skipped = Vec::new();
    let mut ordered: Vec<_> = bin.funcs.iter().collect();
    ordered.sort_by(|a, b| names[&a.entry].cmp(&names[&b.entry])); // by name: the same module at every layout
    for f in ordered {
        let r = (|| -> Result<RFunc, String> {
            let mut words = f.words.clone();
            let mut relocs = Vec::new();
            let n = words.len();
            // The call pairs: auipc rd / jalr _, lo(rd).
            let calls: std::collections::BTreeSet<usize> = (0..n.saturating_sub(1))
                .filter(|&k| {
                    matches!((isa::decode(f.words[k]), isa::decode(f.words[k + 1])),
                    (Some(Instr::Auipc(rd, _)), Some(Instr::Jalr(_, rs1, _))) if rs1 == rd)
                })
                .collect();
            let reach = reaching_auipcs(&f.words, &calls);
            let mut k = 0;
            while k < n {
                let pc = f.entry + 4 * k as u64;
                let Some(Instr::Auipc(rd, hi)) = isa::decode(f.words[k]) else {
                    k += 1;
                    continue;
                };
                let hi_v = sext(hi.value << 12, 32);
                // A call: auipc ra / jalr ra, or auipc t1 / jalr zero.
                if let Some(Instr::Jalr(_, rs1, lo)) =
                    f.words.get(k + 1).and_then(|w| isa::decode(*w))
                {
                    if rs1 == rd {
                        let t = pc.wrapping_add((hi_v + lo.signed()) as u64);
                        let Some(g) = bin.funcs.iter().find(|g| g.entry == t) else {
                            return Err(format!(
                                "{}: the call at {pc:#x} goes to {t:#x}, no function entry",
                                f.name
                            ));
                        };
                        relocs.push(Reloc {
                            off: 4 * k as u64,
                            kind: Kind::Call,
                            sym: names[&g.entry].clone(),
                            addend: 0,
                            hi_off: 4 * k as u64,
                        });
                        words[k] &= !U_FIELD;
                        words[k + 1] &= !I_FIELD;
                        k += 2;
                        continue;
                    }
                }
                // A data address: the instructions the auipc's value reaches, by
                // dataflow (reaching_auipcs), each a %pcrel_lo user. A read reached
                // by several definitions is left as it is: its word stays in the
                // key, a missed reuse but not a wrong one.
                let mut users = Vec::new();
                for j in 0..n {
                    if reach[j][rd.0 as usize] != k as u32 + 1 {
                        continue;
                    }
                    let Some(i) = isa::decode(f.words[j]) else {
                        continue;
                    };
                    if !reads_or_writes(&i, rd).0 {
                        continue;
                    }
                    if let Some((lo, s_type)) = lo_user(&i, rd) {
                        users.push((j, lo, s_type));
                    } else {
                        return Err(format!(
                            "{}: the auipc at {pc:#x} is used at {:#x} other than as a base",
                            f.name,
                            f.entry + 4 * j as u64
                        ));
                    }
                }
                if users.is_empty() {
                    return Err(format!("{}: the auipc at {pc:#x} has no low part", f.name));
                }
                // Every %pcrel_lo user encodes the low part of the same target.
                if users.iter().any(|u| u.1 != users[0].1) {
                    return Err(format!(
                        "{}: the users of the auipc at {pc:#x} disagree on its low part",
                        f.name
                    ));
                }
                let target = pc.wrapping_add((hi_v + users[0].1) as u64);
                let Some((sym, add0)) = sym_at(target) else {
                    return Err(format!(
                        "{}: the address formed at {pc:#x} ({target:#x}) is in no section",
                        f.name
                    ));
                };
                relocs.push(Reloc {
                    off: 4 * k as u64,
                    kind: Kind::PcrelHi,
                    sym: sym.clone(),
                    addend: add0,
                    hi_off: 4 * k as u64,
                });
                words[k] &= !U_FIELD;
                for &(j, _, s_type) in &users {
                    relocs.push(Reloc {
                        off: 4 * j as u64,
                        kind: if s_type {
                            Kind::PcrelLoS
                        } else {
                            Kind::PcrelLoI
                        },
                        sym: sym.clone(),
                        addend: add0,
                        hi_off: 4 * k as u64,
                    });
                    words[j] &= !if s_type { S_FIELD } else { I_FIELD };
                }
                k += 1;
            }
            Ok(RFunc {
                name: names[&f.entry].clone(),
                entry: f.entry,
                words,
                relocs,
            })
        })();
        match r {
            Ok(rf) => funcs.push(rf),
            Err(reason) => skipped.push(Skipped {
                name: names[&f.entry].clone(),
                entry: f.entry,
                reason,
            }),
        }
    }
    let data = bin
        .segments
        .iter()
        .map(|g| RData {
            name: g.name.clone(),
            addr: g.addr,
            bytes: g.bytes.clone(),
            zero: g.zero,
            writable: g.writable,
        })
        .collect();
    Ok(Module {
        funcs,
        data,
        skipped,
        text_addr: bin.text_addr,
        text_words: bin.text.len(),
    })
}

fn str_lit(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// The module and the binary's layout as Lean definitions.
pub fn lean(m: &Module, namespace: &str, source: &str, sha: &str) -> String {
    let mut o = String::new();
    let _ = writeln!(
        o,
        "/-\nGenerated by `nocompiler module` {}; do not edit.",
        env!("CARGO_PKG_VERSION")
    );
    let _ = writeln!(
        o,
        "Source: {source}\nSHA-256: {sha}\n-/\nimport NoCompiler.Module\n"
    );
    let _ = writeln!(o, "namespace {namespace}\nopen NoCompiler\n");
    let _ = writeln!(o, "/-- The relocatable functions and data of {source}. -/");
    let _ = writeln!(o, "def module : Module where\n  funcs := [");
    for (fi, f) in m.funcs.iter().enumerate() {
        let _ = write!(o, "    {{ name := {}, words := [", str_lit(&f.name));
        for (i, w) in f.words.iter().enumerate() {
            o.push_str(if i == 0 {
                ""
            } else if i % 6 == 0 {
                ",\n        "
            } else {
                ", "
            });
            let _ = write!(o, "0x{w:08x}#32");
        }
        o.push_str("],\n      relocs := [");
        for (i, r) in f.relocs.iter().enumerate() {
            let kind = match r.kind {
                Kind::Call => ".call",
                Kind::PcrelHi => ".pcrelHi",
                Kind::PcrelLoI => ".pcrelLoI",
                Kind::PcrelLoS => ".pcrelLoS",
            };
            if i > 0 {
                o.push_str(",\n        ");
            }
            let _ = write!(
                o,
                "{{ off := {}, kind := {kind}, sym := {}, addend := {}, hiOff := {} }}",
                r.off,
                str_lit(&r.sym),
                r.addend,
                r.hi_off
            );
        }
        o.push_str(if fi + 1 < m.funcs.len() {
            "] },\n"
        } else {
            "] }"
        });
    }
    o.push_str("]\n  data := [");
    for (di, d) in m.data.iter().enumerate() {
        if di > 0 {
            o.push_str(",\n    ");
        }
        let bytes = if d.zero {
            format!("List.replicate {} 0", d.bytes.len())
        } else {
            let b: Vec<String> = d.bytes.iter().map(|b| format!("0x{b:02x}#8")).collect();
            format!("[{}]", b.join(", "))
        };
        let _ = write!(
            o,
            "{{ name := {}, bytes := {bytes}, writable := {} }}",
            str_lit(&d.name),
            d.writable
        );
    }
    o.push_str("]\n\n");
    let _ = writeln!(
        o,
        "/-- Where {source} has every symbol (checked by nocompiler-audit against its symbol table). -/"
    );
    let _ = writeln!(o, "def layout : Layout where\n  addr := fun s =>");
    for f in &m.funcs {
        let _ = writeln!(
            o,
            "    if s = {} then 0x{:x}#64 else",
            str_lit(&f.name),
            f.entry
        );
    }
    for f in &m.skipped {
        let _ = writeln!(
            o,
            "    if s = {} then 0x{:x}#64 else -- not in the module: {}",
            str_lit(&f.name),
            f.entry,
            f.reason.replace('\n', " ")
        );
    }
    for d in &m.data {
        let _ = writeln!(
            o,
            "    if s = {} then 0x{:x}#64 else",
            str_lit(&d.name),
            d.addr
        );
    }
    let _ = writeln!(
        o,
        "    0\n  base := 0x{:x}#64\n  size := {}\n",
        m.text_addr, m.text_words
    );
    let _ = writeln!(o, "end {namespace}");
    o
}

/// The canonical bytes of a relocatable function, which its ledger hash is
/// of: its words (relocated fields zero) and its relocations, in order. Not
/// its name or address, so the same code has the same hash wherever, and
/// under whatever name, it is linked. Relocation targets are by symbol.
pub fn canonical(f: &RFunc) -> Vec<u8> {
    let mut o = String::from("nocompiler-rfunc 1\n");
    for w in &f.words {
        let _ = writeln!(o, "{w:08x}");
    }
    for r in &f.relocs {
        let k = match r.kind {
            Kind::Call => "call",
            Kind::PcrelHi => "pcrel_hi",
            Kind::PcrelLoI => "pcrel_lo_i",
            Kind::PcrelLoS => "pcrel_lo_s",
        };
        let _ = writeln!(o, "reloc {} {k} {} {} {}", r.off, r.sym, r.addend, r.hi_off);
    }
    o.into_bytes()
}

/// One ledger entry (docs/isa/ledger.md).
pub struct Entry {
    pub name: String,
    pub sha256: String,
    /// The reuse key: the hash of the function's and every callee's canonical
    /// form (transitively), by name. Equal in two builds exactly when the
    /// function and everything it calls are unchanged as relocatable code, which
    /// is what `Verified.of_sub` (NoCompiler/Relocate.lean) needs.
    pub closure: String,
    pub level: String,
    pub depth: Option<u64>,
    /// The Lean theorem and specification, when the function has a proof.
    pub theorem: Option<String>,
    pub spec: Option<String>,
}

/// The ledger of a binary's module: one entry per function, with the
/// theorems given (`name -> (theorem, spec)`).
pub fn ledger(
    bin: &Binary,
    m: &Module,
    proofs: &std::collections::BTreeMap<String, (String, String)>,
) -> Vec<Entry> {
    let metas: Vec<_> = bin.check().into_iter().collect();
    // T4's depth: the frame plus the deepest callee's (the checker's, when it
    // records one; else computed here over the acyclic call graph).
    fn depth(e: u64, metas: &[crate::Report], seen: &mut Vec<u64>) -> Option<u64> {
        let m = metas.iter().find(|r| r.entry == e)?.result.as_ref().ok()?;
        if let Some(d) = m.depth {
            return Some(d);
        }
        if seen.contains(&e) {
            return None; // recursion: no static bound
        }
        seen.push(e);
        let mut deepest = 0;
        for &c in &m.callees {
            deepest = deepest.max(depth(c, metas, seen)?);
        }
        seen.pop();
        Some(m.frame + deepest)
    }
    // The call graph by name (call relocations), and each function's closure.
    let by_name: std::collections::HashMap<&str, &RFunc> =
        m.funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    let closure_key = |f: &RFunc| -> String {
        let mut seen = std::collections::BTreeSet::new();
        let mut stack = vec![f.name.as_str()];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            if let Some(g) = by_name.get(n) {
                for r in &g.relocs {
                    if r.kind == Kind::Call {
                        stack.push(r.sym.as_str());
                    }
                }
            }
        }
        let mut bytes = Vec::new();
        for n in &seen {
            bytes.extend_from_slice(n.as_bytes());
            bytes.push(b'\n');
            if let Some(g) = by_name.get(n) {
                bytes.extend_from_slice(&canonical(g));
            }
        }
        crate::sha256::hex(&crate::sha256::digest(&bytes))
    };
    m.funcs
        .iter()
        .map(|f| {
            let meta = metas
                .iter()
                .find(|r| r.entry == f.entry)
                .and_then(|r| r.result.as_ref().ok());
            let p = proofs.get(&f.name);
            Entry {
                name: f.name.clone(),
                sha256: crate::sha256::hex(&crate::sha256::digest(&canonical(f))),
                closure: closure_key(f),
                level: meta
                    .map(|m| format!("{:?}", m.level))
                    .unwrap_or_else(|| "none".into()),
                depth: meta.and_then(|_| depth(f.entry, &metas, &mut Vec::new())),
                theorem: p.map(|p| p.0.clone()),
                spec: p.map(|p| p.1.clone()),
            }
        })
        .collect()
}

pub fn ledger_json(es: &[Entry]) -> String {
    let q = |s: &str| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""));
    let opt = |s: &Option<String>| s.as_deref().map(q).unwrap_or_else(|| "null".into());
    let mut o = String::new();
    for e in es {
        let _ = writeln!(
            o,
            "{{\"name\":{},\"sha256\":{},\"closure\":{},\"level\":{},\"depth\":{},\"theorem\":{},\"spec\":{}}}",
            q(&e.name),
            q(&e.sha256),
            q(&e.closure),
            q(&e.level),
            e.depth
                .map(|d| d.to_string())
                .unwrap_or_else(|| "null".into()),
            opt(&e.theorem),
            opt(&e.spec)
        );
    }
    o
}

/// A symbol as `symOfCode` decodes it (lean/NoCompiler/ModuleChunks.lean):
/// its characters as the 32-bit slots of one number. `None` for a NUL
/// character, which would end the string early.
pub fn sym_code(s: &str) -> Option<String> {
    let cs: Vec<u32> = s.chars().map(u32::from).collect();
    if cs.contains(&0) {
        return None;
    }
    Some(crate::lean::nat_hex(&cs, 8))
}

/// Functions per group in a module in chunks (`RChunk.subSeqG`).
pub const GROUP: usize = 32;

/// Bytes per part of a data section in chunks.
const DPART: usize = 1024;

/// `f`'s relocations packed as `RChunk.reloc` decodes them (128 bits each;
/// lean/NoCompiler/ModuleChunks.lean) and their symbols in first-use order.
/// `None` if a field does not fit its width.
pub fn pack_relocs(f: &RFunc) -> Option<(String, Vec<String>)> {
    let mut syms: Vec<String> = Vec::new();
    let mut ws: Vec<u32> = Vec::new();
    for r in &f.relocs {
        let si = match syms.iter().position(|s| *s == r.sym) {
            Some(i) => i,
            None => {
                syms.push(r.sym.clone());
                syms.len() - 1
            }
        };
        let kind: u128 = match r.kind {
            Kind::Call => 0,
            Kind::PcrelHi => 1,
            Kind::PcrelLoI => 2,
            Kind::PcrelLoS => 3,
        };
        let z: u128 = if r.addend >= 0 {
            2 * r.addend as u128
        } else {
            (-2 * (r.addend as i128) - 1) as u128
        };
        if r.off >= 1 << 24 || r.hi_off >= 1 << 24 || si >= 1 << 20 || z >= 1 << 58 {
            return None;
        }
        let v: u128 =
            r.off as u128 | (r.hi_off as u128) << 24 | kind << 48 | (si as u128) << 50 | z << 70;
        for k in 0..4 {
            ws.push((v >> (32 * k)) as u32);
        }
    }
    Some((crate::lean::nat_hex(&ws, 8), syms))
}

/// The module in chunks (lean/NoCompiler/ModuleChunks.lean): one `RChunk`
/// definition `f_i` per function (its words in one number, its relocations
/// in another), one `DChunk` `d_i` per data section (in parts of `DPART`
/// bytes), then `funcs`, `datas` and `module := Module.ofChunks funcs datas`.
/// No layout: a reuse theorem is about every layout.
pub fn lean_chunks(m: &Module, namespace: &str, source: &str, sha: &str) -> Result<String, String> {
    let mut o = String::new();
    let _ = writeln!(
        o,
        "/-\nGenerated by `nocompiler module --format chunks` {}; do not edit.\nSource: {source}\nSHA-256: {sha}\n-/\nimport NoCompiler.ModuleChunks\n",
        env!("CARGO_PKG_VERSION")
    );
    let _ = writeln!(o, "namespace {namespace}\nopen NoCompiler\n");
    for (i, f) in m.funcs.iter().enumerate() {
        let (rbits, syms) =
            pack_relocs(f).ok_or_else(|| format!("{}: a relocation field is too wide", f.name))?;
        let code = |s: &str| sym_code(s).ok_or_else(|| format!("{s:?}: a NUL in a symbol"));
        let syms = syms
            .iter()
            .map(|s| code(s))
            .collect::<Result<Vec<_>, _>>()?;
        let _ = writeln!(
            o,
            "/-- {} -/\ndef f_{i} : RChunk := ⟨{}, {}, {}, {}, {rbits}, [{}]⟩",
            f.name.replace("-/", "- /"),
            code(&f.name)?,
            f.words.len(),
            crate::lean::nat_hex(&f.words, 8),
            f.relocs.len(),
            syms.join(", ")
        );
    }
    for (i, d) in m.data.iter().enumerate() {
        let parts: Vec<String> = d
            .bytes
            .chunks(DPART)
            .map(|p| {
                let bits = if d.zero {
                    "0".to_string()
                } else {
                    let bs: Vec<u32> = p.iter().map(|&b| b.into()).collect();
                    crate::lean::nat_hex(&bs, 2)
                };
                format!("({}, {bits})", p.len())
            })
            .collect();
        let _ = writeln!(
            o,
            "def d_{i} : DChunk := ⟨{}, [{}], {}⟩",
            sym_code(&d.name).ok_or_else(|| format!("{:?}: a NUL in a symbol", d.name))?,
            parts.join(",\n  "),
            d.writable
        );
    }
    let list = |p: &str, n: usize| -> String {
        let v: Vec<String> = (0..n).map(|i| format!("{p}_{i}")).collect();
        v.join(", ")
    };
    let n = m.funcs.len();
    for g in 0..n.div_ceil(GROUP) {
        let v: Vec<String> = (g * GROUP..n.min((g + 1) * GROUP))
            .map(|i| format!("f_{i}"))
            .collect();
        let _ = writeln!(o, "def g_{g} : List RChunk := [{}]", v.join(", "));
    }
    let _ = writeln!(
        o,
        "\n/-- The relocatable functions of {source}, in groups of {GROUP}. -/\ndef groups : List (List RChunk) := [{}]\n\ndef funcs : List RChunk := groups.flatten\n",
        list("g", n.div_ceil(GROUP))
    );
    let _ = writeln!(
        o,
        "def datas : List DChunk := [{}]\n",
        list("d", m.data.len())
    );
    let _ = writeln!(
        o,
        "/-- The relocatable module of {source}. -/\ndef module : Module := Module.ofChunks funcs datas\n\nend {namespace}"
    );
    Ok(o)
}

/// `f`'s call closure in `m`: `f` and every function it reaches through call
/// relocations, as indices into `m.funcs`, sorted. Calls out of the module
/// are left out (they are not part of any module the theorem is about).
pub fn closure(m: &Module, f: usize) -> Vec<usize> {
    let by_name: std::collections::HashMap<&str, usize> = m
        .funcs
        .iter()
        .enumerate()
        .map(|(i, g)| (g.name.as_str(), i))
        .collect();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![f];
    while let Some(i) = stack.pop() {
        if !seen.insert(i) {
            continue;
        }
        for r in &m.funcs[i].relocs {
            if r.kind == Kind::Call {
                if let Some(&j) = by_name.get(r.sym.as_str()) {
                    stack.push(j);
                }
            }
        }
    }
    seen.into_iter().collect()
}

/// What to state for each function of the old module.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReuseForm {
    /// `Verified.of_chunks`: the theorem carried to the new module.
    Verified,
    /// `Refines.of_chunks`: the new module's image refines the old one's.
    Refines,
}

/// Reuse theorems from module `old` (Lean namespace `old_ns`, written by
/// `lean_chunks`) to `new` (`new_ns`): for each function whose closure is in
/// `new` unchanged (same name, words and relocations), a theorem `r_i` that
/// carries its `Verified` to `new` (or gives `Refines`); for each other
/// function a control `c_i`, the kernel deciding that the check fails.
/// Returns the text and the number of theorems and of controls.
pub fn reuse_lean(
    old: &Module,
    new: &Module,
    old_ns: &str,
    new_ns: &str,
    namespace: &str,
    form: ReuseForm,
) -> (String, usize, usize) {
    let idx: std::collections::HashMap<&str, usize> = new
        .funcs
        .iter()
        .enumerate()
        .map(|(i, g)| (g.name.as_str(), i))
        .collect();
    let mut o = String::new();
    let _ = writeln!(
        o,
        "/-\nGenerated by nocompiler (module::reuse_lean); do not edit.\n-/\nimport {old_ns}\nimport {new_ns}\n\nnamespace {namespace}\nopen NoCompiler\n"
    );
    let (mut thms, mut ctls) = (0, 0);
    // Steps to each index for `RChunk.subSeqG` from the start of the groups:
    // `(0, k)` in the current group, `(j + 1, k)` to a later one. `None`
    // unless increasing.
    let steps = |ks: &[usize]| -> Option<String> {
        let mut prev: Option<usize> = None;
        let mut v = Vec::new();
        for &k in ks {
            let (g, o) = (k / GROUP, k % GROUP);
            let st = match prev {
                None => (g + 1, o),
                Some(p) if k <= p => return None,
                Some(p) if p / GROUP == g => (0, o - p % GROUP - 1),
                Some(p) => (g - p / GROUP, o),
            };
            v.push(format!("({}, {})", st.0, st.1));
            prev = Some(k);
        }
        Some(v.join(", "))
    };
    for i in 0..old.funcs.len() {
        let cl = closure(old, i);
        let fs: Vec<String> = cl.iter().map(|j| format!("{old_ns}.f_{j}")).collect();
        let fs = format!("[{}]", fs.join(", "));
        let at: Vec<Option<usize>> = cl
            .iter()
            .map(|&j| idx.get(old.funcs[j].name.as_str()).copied())
            .collect();
        let same = cl.iter().zip(&at).all(|(&j, k)| {
            k.is_some_and(|k| {
                let (g, h) = (&old.funcs[j], &new.funcs[k]);
                h.words == g.words && h.relocs == g.relocs
            })
        });
        let name = str_lit(&old.funcs[i].name);
        // The closure in the new module's order (by its index there), and
        // whether that is another order than the old module's.
        let order: Option<Vec<(usize, usize)>> = cl
            .iter()
            .zip(&at)
            .map(|(&j, k)| k.map(|k| (k, j)))
            .collect::<Option<Vec<_>>>()
            .map(|mut v| {
                v.sort();
                v
            });
        let Some(order) = order else {
            // A callee gone: no theorem and no control.
            ctls += 1;
            let _ = writeln!(o, "-- {name}: a callee is gone; not attempted\n");
            continue;
        };
        let ks: Vec<usize> = order.iter().map(|&(k, _)| k).collect();
        let kb = steps(&ks).expect("sorted and distinct");
        let moved = order.iter().map(|&(_, j)| j).ne(cl.iter().copied());
        let fs2: Vec<String> = order
            .iter()
            .map(|(_, j)| format!("{old_ns}.f_{j}"))
            .collect();
        let fs2 = format!("[{}]", fs2.join(", "));
        if !same {
            ctls += 1;
            let _ = writeln!(
                o,
                "/-- {name} changed (in itself or a callee): no reuse. -/\ntheorem c_{i} : RChunk.subSeqG {fs2} [{kb}] [] {new_ns}.groups = false := by decide +kernel\n"
            );
            continue;
        }
        thms += 1;
        let old_m = format!("(Module.ofChunks {fs} {old_ns}.datas)");
        let new_m = format!("(Module.ofChunks {new_ns}.groups.flatten {new_ns}.datas)");
        match form {
            ReuseForm::Verified => {
                let proof = if moved {
                    format!(
                        "Verified.of_groups_perm (fs' := {fs2}) (ks := [{kb}]) (by decide +kernel) (by decide +kernel) h"
                    )
                } else {
                    format!("Verified.of_groups (ks := [{kb}]) (by decide +kernel) h")
                };
                let _ = writeln!(
                    o,
                    "theorem r_{i} {{α : Type}} {{sp : Layout → Spec α}} (h : Verified {old_m} {name} sp) :\n    Verified {new_m} {name} sp :=\n  {proof}\n"
                );
            }
            ReuseForm::Refines => {
                let ka = steps(&cl).expect("a closure is sorted");
                let old_a = format!("(Module.ofChunks {old_ns}.groups.flatten {old_ns}.datas)");
                let proof = if moved {
                    format!(
                        "Refines.of_groups_perm (fs' := {fs2}) (ka := [{ka}]) (kb := [{kb}]) hA hB (by decide +kernel) (by decide +kernel) (by decide +kernel) h"
                    )
                } else {
                    format!(
                        "Refines.of_groups (ka := [{ka}]) (kb := [{kb}]) hA hB (by decide +kernel) (by decide +kernel) h"
                    )
                };
                let _ = writeln!(
                    o,
                    "theorem r_{i} {{α : Type}} {{sp : Layout → Spec α}} {{L : Layout}}\n    (hA : {old_a}.Ok L)\n    (hB : {new_m}.Ok L)\n    (h : Verified {old_m} {name} sp) :\n    Refines (sp L) ({old_a}.link L) ({old_m}.dom L {name}) (L.addr {name})\n      ({new_m}.link L) ({old_m}.dom L {name}) (L.addr {name}) :=\n  {proof}\n"
                );
            }
        }
    }
    let _ = writeln!(o, "end {namespace}");
    (o, thms, ctls)
}
