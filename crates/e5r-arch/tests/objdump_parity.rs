//! G3: the AArch64 decoder must agree with objdump, instruction for
//! instruction, over the whole fixture corpus.
//!
//! The oracle is `objdump -d`, so the expectations are not our own decoder's
//! opinion. A disagreement is either a bug here or a deliberate divergence with
//! a written reason in `DIVERGENCES`; there is no third category.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_arch::aarch64;
use e5r_core::Addr;

/// Deliberate divergences from objdump, each with its reason.
///
/// Relocated branches are the only one. In a relocatable object a `bl` whose
/// encoded offset is zero carries an R_AARCH64_CALL26 relocation, and objdump
/// prints the relocated target while we print what the bytes say. Applying
/// relocations is the loader's job, not the decoder's, so the decoder is right
/// and the comparison is unfair rather than failing.
#[allow(dead_code)]
const DIVERGENCES: &[(&str, &str)] = &[(
    "relocated branch",
    "objdump resolves R_AARCH64_CALL26; the decoder reports the encoded offset",
)];

/// True when this is the relocated-branch case described above.
fn is_relocated_branch(path: &Path, insn: &e5r_arch::Insn) -> bool {
    let object_file = path.extension().is_some_and(|e| e == "o");
    object_file && insn.flow.target() == Some(insn.addr)
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// One objdump line: address, encoded word, and the text after the encoding.
struct Line {
    addr: u64,
    word: u32,
    text: String,
}

/// Parse `objdump -d` output, keeping only fully decoded 4-byte instructions.
fn objdump(path: &Path) -> Vec<Line> {
    let out = Command::new("objdump")
        .args(["-d", "--show-raw-insn"])
        .arg(path)
        .output()
        .expect("objdump");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lines = Vec::new();
    for l in text.lines() {
        // "  4006e8:\t910043ff \tadd\tsp, sp, #0x10"
        let Some((left, rest)) = l.split_once(":\t") else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let mut parts = rest.splitn(2, '\t');
        let Some(hex) = parts.next() else { continue };
        let hex = hex.trim();
        if hex.len() != 8 {
            continue;
        }
        let Ok(word) = u32::from_str_radix(hex, 16) else {
            continue;
        };
        let Some(body) = parts.next() else {
            // No text at all: objdump could not decode it either.
            continue;
        };
        // Drop the symbolic suffix and objdump's alias comments.
        let body = body.split("//").next().unwrap_or(body);
        let body = match body.find(" <") {
            Some(i) => &body[..i],
            None => body,
        };
        lines.push(Line {
            addr,
            word,
            text: unprefixed(body.trim_end()),
        });
    }
    lines
}

/// Strip the `0x` objdump puts on a branch target it has no symbol for.
///
/// With a symbol it prints `b.lt 4002a4 <use_struct+0x20>`, and without one
/// `b.lt 0x11080`, so the same instruction is spelled two ways depending on
/// whether the binary was stripped. Only the last operand, and only when the
/// whole of it is an address.
fn unprefixed(text: &str) -> String {
    let cut = text.rfind(['\t', ' ']).map(|i| i + 1).unwrap_or(0);
    let last = &text[cut..];
    match last.strip_prefix("0x") {
        Some(hex) if !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()) => {
            format!("{}{hex}", &text[..cut])
        }
        _ => text.to_string(),
    }
}

/// Coverage floor: the fraction of objdump-decodable instructions we also
/// decode. What remains is the single-structure SIMD loads and stores, the
/// by-element multiplies, the memory-tagging instructions, and the Scalable
/// Vector Extension, which is a separate architecture's worth of encodings.
/// Raise this as the gap closes; never lower it.
const MIN_COVERAGE: f64 = 0.998;

/// What comparing one file found.
#[derive(Default)]
struct Tally {
    /// Decoded, and the text matches objdump.
    matched: usize,
    /// Not decoded at all. A gap, not a wrong answer.
    undecoded: usize,
    /// Decoded differently from objdump. These are bugs.
    wrong: Vec<String>,
    /// Mnemonics objdump decoded and we did not.
    missing: Vec<String>,
}

impl Tally {
    fn merge(&mut self, other: Tally) {
        self.matched += other.matched;
        self.undecoded += other.undecoded;
        self.wrong.extend(other.wrong);
        self.missing.extend(other.missing);
    }

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

/// Compare every instruction in one file.
fn check(path: &Path) -> Tally {
    let mut t = Tally::default();
    for l in objdump(path) {
        // objdump spells undefined encodings in ways we do not try to match.
        if l.text.starts_with(".inst") || l.text.starts_with(".word") || l.text.is_empty() {
            continue;
        }
        let want = l.text.as_str();
        let Some(insn) = aarch64::decode_word(l.word, Addr(l.addr)) else {
            t.undecoded += 1;
            t.missing
                .push(l.text.split('\t').next().unwrap_or("?").to_string());
            continue;
        };
        let got = aarch64::format(&insn, aarch64::Style { objdump: true });
        if got == want || is_relocated_branch(path, &insn) {
            t.matched += 1;
        } else {
            t.wrong.push(format!(
                "{:x}: {:08x} objdump {:?} != ours {:?}",
                l.addr, l.word, want, got
            ));
        }
    }
    t
}

/// System binaries, which cost nothing to add and are tens of thousands of
/// instructions of real compiler output apiece.
fn system_binaries() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for p in [
        "/bin/ls",
        "/bin/bash",
        "/usr/bin/objdump",
        "/lib/aarch64-linux-gnu/libc.so.6",
        "/usr/lib/aarch64-linux-gnu/libc.so.6",
        "/usr/lib/aarch64-linux-gnu/libstdc++.so.6",
        "/usr/lib/aarch64-linux-gnu/libcrypto.so.3",
    ] {
        let p = PathBuf::from(p);
        if p.is_file() {
            out.push(p);
        }
    }
    out
}

#[test]
fn aarch64_matches_objdump_on_every_fixture() {
    let Some(dir) = corpus() else { return };
    let mut all = Tally::default();
    let mut files = 0;

    let fixtures = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.ok()?.path();
            let n = p.file_name()?.to_string_lossy().into_owned();
            (n.contains("a64") || n.contains("hello")).then_some(p)
        })
        .chain(system_binaries());

    let mut named: Vec<String> = Vec::new();
    for p in fixtures {
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        let t = check(&p);
        if t.total() == 0 {
            continue;
        }
        files += 1;
        named.extend(t.wrong.iter().map(|b| format!("{name}: {b}")));
        all.merge(t);
    }

    assert!(files > 0, "no aarch64 fixtures found in {}", dir.display());
    assert!(
        all.total() > 100,
        "only {} instructions compared",
        all.total()
    );

    // A wrong answer is a bug, and there is no allowance for any.
    if !named.is_empty() {
        let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
        for f in &named {
            let kind = f
                .split("objdump \"")
                .nth(1)
                .and_then(|s| s.split(['\t', '"']).next())
                .unwrap_or("?")
                .to_string();
            *by_kind.entry(kind).or_default() += 1;
        }
        let summary: Vec<String> = by_kind.iter().map(|(k, n)| format!("{k} x{n}")).collect();
        panic!(
            "{} of {} instructions decode differently from objdump\nby mnemonic: {}\nfirst 20:\n{}",
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

    // A gap is not a bug, but its floor only moves up.
    assert!(
        all.coverage() >= MIN_COVERAGE,
        "decoded {:.3}% of {} instructions, floor is {:.1}% ({} undecoded)",
        all.coverage() * 100.0,
        all.total(),
        MIN_COVERAGE * 100.0,
        all.undecoded
    );
    println!(
        "objdump parity: {} instructions, {} matched, {} undecoded, {:.3}% coverage",
        all.total(),
        all.matched,
        all.undecoded,
        all.coverage() * 100.0
    );
}

#[test]
fn decoding_is_a_pure_function_of_the_word() {
    // Same word, same address, same answer, every time.
    for w in [0x910043ffu32, 0xd65f03c0, 0x14000008, 0xb9400000] {
        let a = aarch64::decode_word(w, Addr(0x1000));
        let b = aarch64::decode_word(w, Addr(0x1000));
        assert_eq!(a, b);
    }
}

#[test]
fn no_encoding_panics() {
    // The whole 32-bit space is too slow for a unit test; a wide stride over it
    // still crosses every top-level group many times.
    let mut w: u32 = 0;
    loop {
        let _ = aarch64::decode_word(w, Addr(0x1000));
        let Some(next) = w.checked_add(0x3ff1) else {
            break;
        };
        w = next;
    }
}

/// A work list rather than a pass/fail: prints the disagreement classes,
/// biggest first, so the next decoder gap is obvious. Ignored by default.
#[test]
#[ignore]
fn parity_report() {
    let Some(dir) = corpus() else { return };
    let mut by_mnemonic: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: BTreeMap<String, String> = BTreeMap::new();
    let files = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.ok()?.path();
            let n = p.file_name()?.to_string_lossy().into_owned();
            (n.contains("a64") || n.contains("hello")).then_some(p)
        })
        .chain(system_binaries());
    for p in files {
        for b in check(&p).wrong {
            // "addr: word objdump "mnem\t..." != ours "..."" or "we decoded nothing"
            let key = b
                .split("objdump ")
                .nth(1)
                .and_then(|s| s.strip_prefix('"'))
                .and_then(|s| s.split(['\t', '"']).next())
                .unwrap_or("?")
                .to_string();
            *by_mnemonic.entry(key.clone()).or_default() += 1;
            examples.entry(key).or_insert(b);
        }
    }
    let mut v: Vec<_> = by_mnemonic.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, n) in v.iter().take(40) {
        println!("{n:>7}  {k:<12} {}", examples[k]);
    }
    let mut missing: BTreeMap<String, usize> = BTreeMap::new();
    for p in std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.ok()?.path();
            let n = p.file_name()?.to_string_lossy().into_owned();
            (n.contains("a64") || n.contains("hello")).then_some(p)
        })
        .chain(system_binaries())
    {
        for m in check(&p).missing {
            *missing.entry(m).or_default() += 1;
        }
    }
    let mut mv: Vec<_> = missing.into_iter().collect();
    mv.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("--- undecoded ---");
    for (k, n) in mv.iter().take(40) {
        println!("{n:>7}  {k}");
    }
}

/// The system register table says the same thing the assembler and the
/// disassembler do, over every encoding an `MRS` can name.
///
/// The table is data, and data written by hand goes wrong quietly: the
/// encodings for `midr_el1`, `cntfrq_el0` and six others were wrong for as
/// long as no fixture happened to read them. This checks all 32768 of them.
#[test]
fn sysreg_names_match_binutils() {
    let dir = std::env::temp_dir().join(format!("e5r-sysreg-{}", std::process::id()));
    if std::fs::create_dir_all(&dir).is_err() {
        return;
    }
    let mut asm = String::new();
    let mut encodings = Vec::new();
    for op0 in 2..4u32 {
        for op1 in 0..8u32 {
            for crn in 0..16u32 {
                for crm in 0..16u32 {
                    for op2 in 0..8u32 {
                        asm.push_str(&format!("mrs x0, s{op0}_{op1}_c{crn}_c{crm}_{op2}\n"));
                        encodings.push(op0 << 14 | op1 << 11 | crn << 7 | crm << 3 | op2);
                    }
                }
            }
        }
    }
    let src = dir.join("sys.s");
    let obj = dir.join("sys.o");
    if std::fs::write(&src, &asm).is_err() {
        return;
    }
    let assembled = Command::new("as").arg("-o").arg(&obj).arg(&src).status();
    if !matches!(assembled, Ok(s) if s.success()) {
        return; // no aarch64 assembler here
    }
    let lines = objdump(&obj);
    assert_eq!(lines.len(), encodings.len(), "objdump lost instructions");

    let mut wrong = Vec::new();
    for (line, enc) in lines.iter().zip(&encodings) {
        let theirs = line.text.rsplit("x0, ").next().unwrap_or("").trim();
        let ours = aarch64::sysreg_name(*enc);
        // A name binutils does not have prints as the generic spelling, which
        // is what it prints too.
        if ours != theirs {
            wrong.push(format!("{enc:#06x}: objdump {theirs:?} != ours {ours:?}"));
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "{} of {} system register names disagree\nfirst 20:\n{}",
        wrong.len(),
        encodings.len(),
        wrong
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
