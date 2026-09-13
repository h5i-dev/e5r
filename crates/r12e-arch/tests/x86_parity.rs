//! G3 for x86-64: the decoder must agree with llvm-objdump in Intel syntax.
//!
//! The host here is aarch64, so the oracle is `llvm-objdump --x86-asm-syntax=intel`
//! over cross-compiled objects. Skipped when neither is available.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_arch::x86;
use r12e_core::Addr;

/// Coverage floor over the corpus. Raise it as the tables fill in.
const MIN_COVERAGE: f64 = 0.999;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// The first llvm-objdump on this machine that can do Intel syntax.
fn objdump() -> Option<&'static str> {
    ["llvm-objdump-18", "llvm-objdump-15", "llvm-objdump"]
        .into_iter()
        .find(|&c| Command::new(c).arg("--version").output().is_ok())
        .map(|v| v as _)
}

struct Line {
    addr: u64,
    bytes: Vec<u8>,
    text: String,
}

fn disassemble(tool: &str, path: &Path) -> Vec<Line> {
    let out = Command::new(tool)
        .args(["-d", "--x86-asm-syntax=intel"])
        .arg(path)
        .output();
    let Ok(out) = out else { return Vec::new() };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lines = Vec::new();
    for l in text.lines() {
        // "       0: 85 ff                        \ttest\tedi, edi"
        let Some((left, rest)) = l.split_once(": ") else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let Some((raw, body)) = rest.split_once('\t') else {
            continue;
        };
        let bytes: Option<Vec<u8>> = raw
            .split_whitespace()
            .map(|h| u8::from_str_radix(h, 16).ok())
            .collect();
        let Some(bytes) = bytes else { continue };
        if bytes.is_empty() {
            continue;
        }
        // Drop the symbolic suffix llvm appends to branch targets.
        let body = match body.find(" #").or_else(|| body.find(" <")) {
            Some(i) => &body[..i],
            None => body,
        };
        lines.push(Line {
            addr,
            bytes,
            text: body.trim_end().to_string(),
        });
    }
    lines
}

#[derive(Default)]
struct Tally {
    matched: usize,
    undecoded: usize,
    wrong: Vec<String>,
}

impl Tally {
    fn total(&self) -> usize {
        self.matched + self.undecoded + self.wrong.len()
    }
    fn coverage(&self) -> f64 {
        if self.total() == 0 {
            return 1.0;
        }
        (self.matched + self.wrong.len()) as f64 / self.total() as f64
    }
}

fn check(tool: &str, path: &Path) -> Tally {
    let mut t = Tally::default();
    for l in disassemble(tool, path) {
        if l.text.starts_with("<unknown>") || l.text.is_empty() {
            continue;
        }
        match x86::decode(&l.bytes, Addr(l.addr)) {
            None => t.undecoded += 1,
            Some(i) if i.len as usize != l.bytes.len() => t.wrong.push(format!(
                "{:x}: {:02x?} length {} != llvm's {}",
                l.addr,
                l.bytes,
                i.len,
                l.bytes.len()
            )),
            Some(i) => {
                let got = x86::format(&i, x86::Style::default());
                if got == l.text {
                    t.matched += 1;
                } else {
                    t.wrong.push(format!(
                        "{:x}: {:02x?} llvm {:?} != ours {:?}",
                        l.addr, l.bytes, l.text, got
                    ));
                }
            }
        }
    }
    t
}

fn fixtures() -> Vec<PathBuf> {
    let Some(dir) = corpus() else {
        return Vec::new();
    };
    std::fs::read_dir(dir)
        .map(|rd| {
            rd.filter_map(|e| {
                let p = e.ok()?.path();
                let n = p.file_name()?.to_string_lossy().into_owned();
                n.contains("x64").then_some(p)
            })
            .collect()
        })
        .unwrap_or_default()
}

#[test]
fn x86_64_matches_llvm_objdump() {
    let (Some(tool), files) = (objdump(), fixtures()) else {
        return;
    };
    if files.is_empty() {
        return;
    }
    let mut all = Tally::default();
    let mut named = Vec::new();
    for p in &files {
        let t = check(tool, p);
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        named.extend(t.wrong.iter().map(|w| format!("{name}: {w}")));
        all.matched += t.matched;
        all.undecoded += t.undecoded;
        all.wrong.extend(t.wrong);
    }
    if all.total() < 20 {
        return; // nothing useful to compare
    }

    if !named.is_empty() {
        let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
        for f in &named {
            let kind = f
                .split("llvm \"")
                .nth(1)
                .and_then(|s| s.split(['\t', '"']).next())
                .unwrap_or("length")
                .to_string();
            *by_kind.entry(kind).or_default() += 1;
        }
        let summary: Vec<String> = by_kind.iter().map(|(k, n)| format!("{k} x{n}")).collect();
        panic!(
            "{} of {} x86 instructions decode differently\nby mnemonic: {}\nfirst 20:\n{}",
            named.len(),
            all.total(),
            summary.join(", "),
            named
                .iter()
                .take(20)
                .cloned()
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
    assert!(
        all.coverage() >= MIN_COVERAGE,
        "decoded {:.2}% of {} x86 instructions, floor is {:.0}% ({} undecoded)",
        all.coverage() * 100.0,
        all.total(),
        MIN_COVERAGE * 100.0,
        all.undecoded
    );
    println!(
        "x86 parity: {} instructions, {} matched, {} undecoded, {:.2}% coverage",
        all.total(),
        all.matched,
        all.undecoded,
        all.coverage() * 100.0
    );
}

/// A work list, like the AArch64 one. Ignored by default.
#[test]
#[ignore]
fn x86_parity_report() {
    let (Some(tool), files) = (objdump(), fixtures()) else {
        return;
    };
    let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut example: BTreeMap<String, String> = BTreeMap::new();
    let mut undecoded = 0;
    let mut total = 0;
    for p in &files {
        for l in disassemble(tool, p) {
            if l.text.is_empty() {
                continue;
            }
            total += 1;
            let key = l.text.split('\t').next().unwrap_or("?").to_string();
            match x86::decode(&l.bytes, Addr(l.addr)) {
                None => {
                    undecoded += 1;
                    *by_kind.entry(format!("UNDECODED {key}")).or_default() += 1;
                    example
                        .entry(format!("UNDECODED {key}"))
                        .or_insert(format!("{:02x?} {}", l.bytes, l.text));
                }
                Some(i) => {
                    let got = x86::format(&i, x86::Style::default());
                    if got != l.text || i.len as usize != l.bytes.len() {
                        *by_kind.entry(key.clone()).or_default() += 1;
                        example.entry(key).or_insert(format!(
                            "{:02x?} llvm {:?} ours {:?}",
                            l.bytes, l.text, got
                        ));
                    }
                }
            }
        }
    }
    let mut v: Vec<_> = by_kind.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("{total} instructions, {undecoded} undecoded");
    for (k, n) in v.iter().take(40) {
        println!("{n:>6}  {k:<24} {}", example[k]);
    }
}
