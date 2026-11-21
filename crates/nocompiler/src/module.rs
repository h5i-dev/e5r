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
pub struct Module {
    pub funcs: Vec<RFunc>,
    pub data: Vec<RData>,
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
    let m = of_binary_unchecked(bin)?;
    let addr = |s: &str| -> Option<u64> {
        m.funcs
            .iter()
            .find(|f| f.name == s)
            .map(|f| f.entry)
            .or_else(|| m.data.iter().find(|d| d.name == s).map(|d| d.addr))
    };
    for f in &m.funcs {
        let b = bin.funcs.iter().find(|g| g.entry == f.entry).unwrap();
        let w =
            patched(f, &addr).ok_or_else(|| format!("{}: a relocation names no symbol", f.name))?;
        if w != b.words {
            let k = w
                .iter()
                .zip(&b.words)
                .position(|(x, y)| x != y)
                .unwrap_or(0);
            return Err(format!(
                "{}: relinked at its own address, the word at {:#x} differs (a misattributed relocation)",
                f.name,
                f.entry + 4 * k as u64
            ));
        }
    }
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
    let mut ordered: Vec<_> = bin.funcs.iter().collect();
    ordered.sort_by(|a, b| names[&a.entry].cmp(&names[&b.entry])); // by name: the same module at every layout
    for f in ordered {
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
            if let Some(Instr::Jalr(_, rs1, lo)) = f.words.get(k + 1).and_then(|w| isa::decode(*w))
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
        funcs.push(RFunc {
            name: names[&f.entry].clone(),
            entry: f.entry,
            words,
            relocs,
        });
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
