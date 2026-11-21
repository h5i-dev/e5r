//! Export a binary to a Lean module for proofs (docs/isa/toolchain.md,
//! "Proving a function").
//!
//! The module holds the `.text` words exactly as they are in the file, one
//! `@[nocompiler_image]` lemma per decodable address saying which instruction is
//! there (checked by the kernel evaluating the Lean decoder, so this
//! exporter's own decoder is not trusted), and each function's entry and code
//! region. `lean/Audit.lean` re-reads the ELF file in Lean and checks the
//! words against the module, so the exporter's ELF reader is not trusted
//! either.

use crate::Binary;
use crate::isa;
use crate::profile::FuncMeta;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

/// A Lean identifier from a symbol name.
pub fn ident(name: &str) -> String {
    let mut s: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() || s.as_bytes()[0].is_ascii_digit() {
        s.insert(0, 'f');
    }
    s
}

/// The code region of a function: itself and everything it calls, transitively.
pub fn closure(f: &FuncMeta, metas: &BTreeMap<u64, &FuncMeta>) -> Result<Vec<(u64, u64)>, String> {
    let mut seen = BTreeSet::new();
    let mut work = vec![f.entry];
    let mut out = Vec::new();
    while let Some(e) = work.pop() {
        if !seen.insert(e) {
            continue;
        }
        let m = metas.get(&e).ok_or_else(|| {
            format!(
                "{} calls {e:#x}, which did not pass the profile check",
                f.name
            )
        })?;
        out.push((m.entry, m.size));
        work.extend(m.callees.iter().copied());
    }
    out.sort();
    Ok(out)
}

/// The functions whose code region can be formed: those that call, transitively,
/// only functions that passed the profile check. Every other one is skipped,
/// and reported on stderr; skipping one can skip its callers, so to a fixpoint.
pub fn exportable(metas: &[FuncMeta]) -> Vec<FuncMeta> {
    let mut keep: Vec<FuncMeta> = metas.to_vec();
    loop {
        let by_entry: BTreeMap<u64, &FuncMeta> = keep.iter().map(|m| (m.entry, m)).collect();
        let bad: BTreeSet<u64> = keep
            .iter()
            .filter_map(|m| match closure(m, &by_entry) {
                Ok(_) => None,
                Err(e) => {
                    eprintln!("nocompiler: skipping {} ({e})", m.name);
                    Some(m.entry)
                }
            })
            .collect();
        if bad.is_empty() {
            return keep;
        }
        keep.retain(|m| !bad.contains(&m.entry));
    }
}

pub fn export(
    bin: &Binary,
    metas: &[FuncMeta],
    namespace: &str,
    source: &str,
) -> Result<String, String> {
    export_as(bin, metas, namespace, source, false)
}

/// The image in chunks (lean/NoCompiler/Image.lean, "Code in chunks"): `.text`
/// as one literal per symbol, no lemma per instruction, data segments in
/// parts; elaborates in time and memory linear in the binary.
pub fn export_chunks(
    bin: &Binary,
    metas: &[FuncMeta],
    namespace: &str,
    source: &str,
) -> Result<String, String> {
    export_as(bin, metas, namespace, source, true)
}

/// `Σ xs[i] << (4 * digits * i)` as a hexadecimal Lean literal: the number
/// `Chunk` (digits 8) and `Segment.bytesOfNat` (digits 2) decode.
pub fn nat_hex(xs: &[u32], digits: usize) -> String {
    let mut h = String::with_capacity(2 + digits * xs.len());
    h.push_str("0x");
    for x in xs.iter().rev() {
        write!(h, "{x:0digits$x}").unwrap();
    }
    if xs.is_empty() {
        h.push('0');
    }
    h
}

/// Gap chunks (no function in them) are cut to this many words.
const PART: usize = 1024;

/// Chunk boundaries, in words from the start of `.text`: every function's entry
/// and end, but none strictly inside a function, so each function is in one
/// chunk; stretches with no function in them cut every `PART` words.
pub fn chunk_bounds(bin: &Binary) -> Vec<(usize, usize)> {
    let n = bin.text.len();
    let iv: Vec<(usize, usize)> = bin
        .funcs
        .iter()
        .filter(|f| f.entry >= bin.text_addr && !f.words.is_empty())
        .map(|f| {
            let a = ((f.entry - bin.text_addr) / 4) as usize;
            (a.min(n), (a + f.words.len()).min(n))
        })
        .collect();
    let mut cut: BTreeSet<usize> = [0, n].into_iter().collect();
    for &(a, b) in &iv {
        cut.insert(a);
        cut.insert(b);
    }
    cut.retain(|&c| !iv.iter().any(|&(a, b)| a < c && c < b));
    let cut: Vec<usize> = cut.into_iter().collect();
    let mut out = Vec::new();
    for w in cut.windows(2) {
        let (a, b) = (w[0], w[1]);
        if a == b {
            continue;
        }
        if iv.iter().any(|&(x, _)| a <= x && x < b) {
            out.push((a, b));
        } else {
            let mut x = a;
            while x < b {
                out.push((x, (x + PART).min(b)));
                x += PART;
            }
        }
    }
    out
}

fn export_as(
    bin: &Binary,
    metas: &[FuncMeta],
    namespace: &str,
    source: &str,
    chunked: bool,
) -> Result<String, String> {
    // A function's `_dom` is it and everything it calls, so the array format
    // exports only the functions whose callees passed (`exportable`). The
    // chunk format exports every function that passed: its level check is on
    // its own chunk and needs only `entries`, and it gets `_dom` when its
    // callees passed too.
    let ok = exportable(metas);
    let metas = if chunked { metas.to_vec() } else { ok.clone() };
    let metas = &metas[..];
    let by_entry: BTreeMap<u64, &FuncMeta> = ok.iter().map(|m| (m.entry, m)).collect();
    // Levels and certificates, from checking the binary again.
    let levels: BTreeMap<u64, (crate::profile::Level, Vec<crate::frame::CertFact>)> = bin
        .check()
        .into_iter()
        .filter_map(|r| Some((r.entry, (r.level?, r.cert))))
        .collect();
    let mut o = String::new();
    let sha = crate::sha256::hex(&crate::sha256::digest(bin.bytes));
    writeln!(o, "/-").unwrap();
    writeln!(
        o,
        "Generated by `nocompiler export` {}; do not edit.",
        env!("CARGO_PKG_VERSION")
    )
    .unwrap();
    writeln!(o, "Source: {source}").unwrap();
    writeln!(o, "SHA-256: {sha}").unwrap();
    writeln!(o, "-/").unwrap();
    writeln!(o, "import NoCompiler\n").unwrap();
    let bounds = if chunked { chunk_bounds(bin) } else { vec![] };
    if chunked {
        // `decide` on one function's chunk, and `Chunk.contig` over the list.
        let big = bounds
            .iter()
            .map(|(a, b)| b - a)
            .max()
            .unwrap_or(0)
            .max(bounds.len());
        writeln!(o, "set_option maxRecDepth {}\n", (64 * big).max(512)).unwrap();
    } else if bin.text.len() > 128 {
        // Each `instr_` lemma evaluates `Code.instr` on the array literal, which
        // recurses once per element before its index; the default depth runs
        // out a little past 128 words.
        writeln!(o, "set_option maxRecDepth {}\n", 64 * bin.text.len()).unwrap();
    }
    writeln!(o, "namespace {namespace}").unwrap();
    writeln!(o, "open NoCompiler\n").unwrap();
    writeln!(
        o,
        "/-- SHA-256 of the ELF file this module was exported from. -/"
    )
    .unwrap();
    writeln!(o, "def elfSha256 : String := \"{sha}\"\n").unwrap();
    writeln!(
        o,
        "/-- `.text`, {} words from {:#x}. -/",
        bin.text.len(),
        bin.text_addr
    )
    .unwrap();
    if chunked {
        let base = format!("0x{:x}#64", bin.text_addr);
        for (k, &(a, b)) in bounds.iter().enumerate() {
            writeln!(
                o,
                "def chunk_{k} : Chunk := ⟨{a}, {}, {}⟩",
                b - a,
                nat_hex(&bin.text[a..b], 8)
            )
            .unwrap();
        }
        let names: Vec<String> = (0..bounds.len()).map(|k| format!("chunk_{k}")).collect();
        writeln!(o, "\n/-- The chunks, in order. -/").unwrap();
        writeln!(o, "def chunks : List Chunk := [{}]", names.join(", ")).unwrap();
        writeln!(o, "def code : Code := Code.ofChunks {base} chunks").unwrap();
        writeln!(
            o,
            "theorem chunks_contig : Chunk.contig 0 chunks = true := by decide +kernel"
        )
        .unwrap();
        writeln!(
            o,
            "theorem chunks_bound : 4 * Chunk.total chunks < 2 ^ 64 := by decide +kernel\n"
        )
        .unwrap();
    } else {
        write!(o, "def code : Code := ⟨0x{:x}#64, #[", bin.text_addr).unwrap();
        for (i, w) in bin.text.iter().enumerate() {
            o.push_str(if i == 0 {
                "\n  "
            } else if i % 6 == 0 {
                ",\n  "
            } else {
                ", "
            });
            write!(o, "0x{w:08x}#32").unwrap();
        }
        writeln!(o, "]⟩\n").unwrap();
    }
    let mut names = Vec::new();
    for g in &bin.segments {
        let id = format!("seg{}", ident(&g.name.replace('.', "_")));
        writeln!(
            o,
            "/-- `{}`, {} bytes from {:#x}{}. -/",
            g.name,
            g.bytes.len(),
            g.addr,
            if g.writable { ", writable" } else { "" }
        )
        .unwrap();
        let bytes = if g.zero {
            format!("Array.replicate {} 0", g.bytes.len())
        } else if chunked {
            let ws: Vec<u32> = g.bytes.iter().map(|&x| x as u32).collect();
            format!("Segment.bytesOfNat {} {}", g.bytes.len(), nat_hex(&ws, 2))
        } else {
            let mut b = String::from("#[");
            for (i, x) in g.bytes.iter().enumerate() {
                b.push_str(if i == 0 {
                    "\n    "
                } else if i % 12 == 0 {
                    ",\n    "
                } else {
                    ", "
                });
                write!(b, "0x{x:02x}#8").unwrap();
            }
            b.push(']');
            b
        };
        writeln!(
            o,
            "def {id} : Segment :=\n  {{ name := \"{}\", base := 0x{:x}#64, writable := {},\n    bytes := {bytes} }}\n",
            g.name, g.addr, g.writable
        )
        .unwrap();
        names.push(id);
    }
    writeln!(o, "/-- Every allocated section that is not code. -/").unwrap();
    writeln!(o, "def segments : List Segment := [{}]\n", names.join(", ")).unwrap();
    for (i, &w) in bin.text.iter().enumerate() {
        if chunked {
            break;
        }
        let pc = bin.text_addr + 4 * i as u64;
        if let Some(ins) = isa::decode(w) {
            writeln!(o, "/-- `{}` -/", ins.asm(pc)).unwrap();
            writeln!(
                o,
                "@[nocompiler_image] theorem instr_{pc:x} : code.instr 0x{pc:x}#64 = some ({}) := by rfl",
                ins.lean()
            )
            .unwrap();
        }
    }
    let entries: Vec<String> = bin
        .funcs
        .iter()
        .map(|f| format!("0x{:x}#64", f.entry))
        .collect();
    writeln!(
        o,
        "\n/-- Every function entry: where calls and tail calls may go. -/"
    )
    .unwrap();
    writeln!(o, "def entries : List Word := [{}]", entries.join(", ")).unwrap();
    // Two local symbols can have one name: those get their address appended.
    let mut seen_ids: BTreeMap<String, usize> = BTreeMap::new();
    for m in metas {
        *seen_ids.entry(ident(&m.name)).or_default() += 1;
    }
    for m in metas {
        let id = match ident(&m.name) {
            id if seen_ids[&id] > 1 => format!("{id}_{:x}", m.entry),
            id => id,
        };
        let mut nodes = Vec::new();
        fn flat(ns: &[crate::profile::Node], out: &mut Vec<String>) {
            for n in ns {
                let k = match n.kind {
                    crate::profile::Kind::Block => "block",
                    crate::profile::Kind::Loop => "loop",
                };
                out.push(format!("⟨.{k}, 0x{:x}#64, 0x{:x}#64⟩", n.start, n.end));
                flat(&n.children, out);
            }
        }
        flat(&m.nodes, &mut nodes);
        writeln!(
            o,
            "\n/-- `{}`'s block/loop structure (rules R1 to R3, checked below with R4 to R6). -/",
            m.name
        )
        .unwrap();
        writeln!(
            o,
            "def {id}_func : Struct.Func := ⟨0x{:x}#64, {}, [{}]⟩",
            m.entry,
            m.size / 4,
            nodes.join(", ")
        )
        .unwrap();
        // Labels, named as `disasm` names them (crates/nocompiler/src/text.rs): the
        // recorded one, else $b<k> / $l<k> by pre-order index; a block's label
        // is its end, a loop's its head.
        let mut labels = Vec::new();
        fn lab(ns: &[crate::profile::Node], k: &mut usize, out: &mut Vec<String>) {
            for n in ns {
                let loop_ = n.kind == crate::profile::Kind::Loop;
                let l = n
                    .label
                    .clone()
                    .map(|l| l.trim_start_matches('$').to_string())
                    .unwrap_or_else(|| format!("{}{}", if loop_ { "l" } else { "b" }, *k));
                *k += 1;
                out.push(format!(
                    "(\"{l}\", 0x{:x}#64)",
                    if loop_ { n.start } else { n.end }
                ));
                lab(&n.children, k, out);
            }
        }
        lab(&m.nodes, &mut 0, &mut labels);
        writeln!(
            o,
            "/-- `{}`'s labels: where `$l` is, for `loop_inv $l` (a loop's head, a block's end). -/",
            m.name
        )
        .unwrap();
        writeln!(
            o,
            "def {id}_labels : List (String × Word) := [{}]",
            labels.join(", ")
        )
        .unwrap();
        let (level, cert) = levels
            .get(&m.entry)
            .cloned()
            .unwrap_or((crate::profile::Level::L1, vec![]));
        let slots: Vec<String> = m
            .slots
            .iter()
            .map(|s| match s.kind {
                crate::profile::SlotKind::Save(r) => format!("⟨{}, .save {}⟩", s.off, r.0),
                crate::profile::SlotKind::Spill => format!("⟨{}, .spill⟩", s.off),
            })
            .collect();
        let ranges: Vec<String> = m
            .ranges
            .iter()
            .map(|g| format!("⟨{}, {}⟩", g.off, g.len))
            .collect();
        writeln!(
            o,
            "/-- `{}`'s frame (rule R6): {} bytes, its slots and address-taken ranges. -/",
            m.name, m.frame
        )
        .unwrap();
        writeln!(
            o,
            "def {id}_frame : Struct.Frame := ⟨{}, [{}], [{}]⟩",
            m.frame,
            slots.join(", "),
            ranges.join(", ")
        )
        .unwrap();
        let facts: Vec<String> = cert
            .iter()
            .map(|c| {
                let keep: Vec<String> = c.keep.iter().map(|r| r.to_string()).collect();
                let held: Vec<String> = c.held.iter().map(|(k, r)| format!("({k}, {r})")).collect();
                format!(
                    "⟨{}, [{}], [{}]⟩",
                    c.depth,
                    keep.join(", "),
                    held.join(", ")
                )
            })
            .collect();
        writeln!(
            o,
            "/-- The certificate for rules R4 to R6 (NoCompiler/Frame.lean): the fact before each instruction. -/"
        )
        .unwrap();
        // As runs, when every `keep` is increasing (so a mask gives it back).
        let sorted = cert
            .iter()
            .all(|c| c.keep.windows(2).all(|w| w[0] < w[1]) && c.keep.iter().all(|&r| r < 32));
        if facts.is_empty() {
            writeln!(o, "def {id}_cert : Struct.Cert := []").unwrap();
        } else if chunked && sorted {
            let mut runs: Vec<(usize, &crate::frame::CertFact)> = Vec::new();
            for c in cert.iter() {
                match runs.last_mut() {
                    Some((n, last)) if *last == c => *n += 1,
                    _ => runs.push((1, c)),
                }
            }
            let rs: Vec<String> = runs
                .iter()
                .map(|(n, c)| {
                    let mask: u64 = c.keep.iter().map(|&r| 1u64 << r).sum();
                    let held: Vec<String> =
                        c.held.iter().map(|(k, r)| format!("({k}, {r})")).collect();
                    format!("({n}, {}, {mask}, [{}])", c.depth, held.join(", "))
                })
                .collect();
            writeln!(
                o,
                "def {id}_cert : Struct.Cert := Struct.Cert.ofRuns [{}]",
                rs.join(", ")
            )
            .unwrap();
        } else {
            writeln!(
                o,
                "def {id}_cert : Struct.Cert := [\n  {}]",
                facts.join(",\n  ")
            )
            .unwrap();
        }
        let lv = match level {
            crate::profile::Level::L0 => "l0",
            crate::profile::Level::L1 => "l1",
            crate::profile::Level::L2 => "l2",
        };
        writeln!(
            o,
            "/-- `{}` is at level {:?} (docs/isa/v1.md), as the kernel checks it. -/",
            m.name, level
        )
        .unwrap();
        if chunked {
            let w = ((m.entry - bin.text_addr) / 4) as usize;
            let k = bounds
                .iter()
                .position(|&(a, b)| a <= w && w < b)
                .ok_or_else(|| format!("{}: in no chunk", m.name))?;
            let base = format!("0x{:x}#64", bin.text_addr);
            writeln!(
                o,
                "theorem {id}_checked : Struct.level (chunk_{k}.code {base}) {id}_func entries {id}_frame {id}_cert = some .{lv} := by decide +kernel"
            )
            .unwrap();
            writeln!(
                o,
                "/-- The image is `{}`'s chunk where the chunk is. -/",
                m.name
            )
            .unwrap();
            writeln!(
                o,
                "theorem {id}_chunk : ∀ x, Dom.mem [chunk_{k}.range {base}] x → code.instr x = (chunk_{k}.code {base}).instr x :=\n  Code.ofChunks_instr (k := {k}) chunks_contig (by decide +kernel) chunks_bound"
            )
            .unwrap();
        } else {
            writeln!(
                o,
                "theorem {id}_checked : Struct.level code {id}_func entries {id}_frame {id}_cert = some .{lv} := by decide"
            )
            .unwrap();
        }
        writeln!(
            o,
            "\n/-- `{}`: [{:#x}, {:#x}), frame {} bytes. -/",
            m.name,
            m.entry,
            m.entry + m.size,
            m.frame
        )
        .unwrap();
        writeln!(o, "def {id}_entry : Word := 0x{:x}#64", m.entry).unwrap();
        if !by_entry.contains_key(&m.entry) {
            writeln!(
                o,
                "-- no `{id}_dom`: `{}` calls, transitively, a function that did not pass the profile check",
                m.name
            )
            .unwrap();
            continue;
        }
        let dom = closure(m, &by_entry)?;
        let ranges: Vec<String> = dom
            .iter()
            .map(|(e, s)| format!("(0x{e:x}#64, {s})"))
            .collect();
        writeln!(o, "/-- `{}` and every function it calls. -/", m.name).unwrap();
        writeln!(o, "def {id}_dom : Dom := [{}]", ranges.join(", ")).unwrap();
    }
    writeln!(o, "\nend {namespace}").unwrap();
    Ok(o)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::Level;

    fn meta(name: &str, entry: u64, callees: &[u64]) -> FuncMeta {
        FuncMeta {
            name: name.into(),
            entry,
            size: 8,
            level: Level::L2,
            frame: 0,
            depth: None,
            callees: callees.to_vec(),
            nodes: vec![],
            slots: vec![],
            ranges: vec![],
            ext: vec![],
        }
    }

    #[test]
    fn nat_hex_puts_the_first_word_lowest() {
        assert_eq!(nat_hex(&[0x13, 0xdeadbeef], 8), "0xdeadbeef00000013");
        assert_eq!(nat_hex(&[1, 2, 0xff], 2), "0xff0201");
        assert_eq!(nat_hex(&[], 8), "0x0");
    }

    /// Chunks cover `.text` back to back, every function inside one chunk, gaps
    /// cut to `PART` words.
    #[test]
    fn chunks_partition_text_and_keep_functions_whole() {
        let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
        for elf in ["examples/elf/hello.elf", "examples/demo/elf/cobs.b.elf"] {
            let bytes = std::fs::read(format!("{root}/{elf}")).unwrap();
            let bin = crate::load(&bytes).unwrap();
            let cs = chunk_bounds(&bin);
            assert_eq!(cs.first().unwrap().0, 0);
            assert_eq!(cs.last().unwrap().1, bin.text.len());
            assert!(cs.windows(2).all(|w| w[0].1 == w[1].0 && w[0].0 < w[0].1));
            for f in &bin.funcs {
                let a = ((f.entry - bin.text_addr) / 4) as usize;
                let b = a + f.words.len();
                assert!(
                    cs.iter().any(|&(x, y)| x <= a && b <= y),
                    "{elf}: {}",
                    f.name
                );
            }
            assert!(cs.iter().all(|&(x, y)| y - x <= PART
                || bin.funcs.iter().any(|f| {
                    let a = ((f.entry - bin.text_addr) / 4) as usize;
                    x <= a && a < y
                })));
        }
    }

    /// With `write_all` taken as failing the profile check, the array format
    /// drops `hello` (its `_dom` would include `write_all`); the chunk format
    /// still checks `hello`'s level, and only leaves out its `_dom`.
    #[test]
    fn chunks_check_functions_whose_callees_failed() {
        let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
        let bytes = std::fs::read(format!("{root}/examples/elf/hello.elf")).unwrap();
        let bin = crate::load(&bytes).unwrap();
        let metas: Vec<FuncMeta> = bin
            .check()
            .into_iter()
            .filter_map(|r| r.result.ok())
            .filter(|m| m.name != "write_all")
            .collect();
        assert!(metas.iter().any(|m| m.name == "hello"));
        let a = export(&bin, &metas, "T", "hello.elf").unwrap();
        assert!(!a.contains("theorem hello_checked"));
        let c = export_chunks(&bin, &metas, "T", "hello.elf").unwrap();
        assert!(c.contains("theorem hello_checked"));
        assert!(c.contains("def hello_entry"));
        assert!(!c.contains("def hello_dom"));
        assert!(c.contains("-- no `hello_dom`"));
    }

    /// Two functions with one name (local symbols) get their entries appended.
    #[test]
    fn colliding_names_get_their_entry() {
        let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
        let bytes = std::fs::read(format!("{root}/examples/elf/hello.elf")).unwrap();
        let bin = crate::load(&bytes).unwrap();
        let mut metas: Vec<FuncMeta> = bin
            .check()
            .into_iter()
            .filter_map(|r| r.result.ok())
            .collect();
        for m in metas.iter_mut() {
            if m.name == "write_all" {
                m.name = "hello".into();
            }
        }
        let c = export_chunks(&bin, &metas, "T", "hello.elf").unwrap();
        assert!(!c.contains("def hello_func"));
        for m in metas.iter().filter(|m| m.name == "hello") {
            assert!(c.contains(&format!("def hello_{:x}_func", m.entry)));
        }
    }

    /// A function calling one that did not pass the profile check is skipped,
    /// and so is its caller, transitively; the rest are kept.
    #[test]
    fn exportable_skips_callers_of_non_conforming_functions() {
        let ms = [
            meta("leaf", 0x100, &[]),
            meta("calls_leaf", 0x200, &[0x100]),
            meta("calls_bad", 0x300, &[0x900]),
            meta("calls_calls_bad", 0x400, &[0x300, 0x100]),
        ];
        let names: Vec<String> = exportable(&ms).into_iter().map(|m| m.name).collect();
        assert_eq!(names, ["leaf", "calls_leaf"]);
    }
}
