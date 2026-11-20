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

/// The module of a binary, or why its code is not relocatable.
pub fn of_binary(bin: &Binary) -> Result<Module, String> {
    let sym_at = |t: u64| -> Option<(String, i64)> {
        if let Some(f) = bin.funcs.iter().find(|f| f.entry == t) {
            return Some((f.name.clone(), 0));
        }
        bin.segments
            .iter()
            .find(|g| t >= g.addr && t <= g.addr + g.bytes.len() as u64)
            .map(|g| (g.name.clone(), (t - g.addr) as i64))
    };
    let mut funcs = Vec::new();
    let mut ordered: Vec<_> = bin.funcs.iter().collect();
    ordered.sort_by(|a, b| a.name.cmp(&b.name)); // by name: the same module at every layout
    for f in ordered {
        let mut words = f.words.clone();
        let mut relocs = Vec::new();
        let n = words.len();
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
                        sym: g.name.clone(),
                        addend: 0,
                        hi_off: 4 * k as u64,
                    });
                    words[k] &= !U_FIELD;
                    words[k + 1] &= !I_FIELD;
                    k += 2;
                    continue;
                }
            }
            // A data address: the users of rd until it is written again.
            let mut users = Vec::new();
            for j in k + 1..n {
                let Some(i) = isa::decode(f.words[j]) else {
                    break;
                };
                if let Some((lo, s_type)) = lo_user(&i, rd) {
                    users.push((j, lo, s_type));
                } else if reads_or_writes(&i, rd).0 {
                    return Err(format!(
                        "{}: the auipc at {pc:#x} is used at {:#x} other than as a base",
                        f.name,
                        f.entry + 4 * j as u64
                    ));
                }
                let (_, w) = reads_or_writes(&i, rd);
                if w || matches!(i, Instr::Branch(..) | Instr::Jal(..) | Instr::Jalr(..)) {
                    break;
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
            name: f.name.clone(),
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
            "{{\"name\":{},\"sha256\":{},\"level\":{},\"depth\":{},\"theorem\":{},\"spec\":{}}}",
            q(&e.name),
            q(&e.sha256),
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
