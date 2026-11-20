//! G3 for ARM: the A32 and T32 decoders must agree with llvm-objdump.
//!
//! The oracle is `llvm-objdump-18 -d` over cross-compiled objects, the same
//! source built twice so the two instruction sets are measured against each
//! other's coverage as well as against the tool. Thumb is walked in address
//! order rather than sampled, because an instruction inside an IT block is
//! conditional and only the instructions before it say so.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_arch::arm::{self, ItState, Mode, Thumb};
use e5r_core::Addr;

/// Coverage floor over the corpus, which is at 100% today. What the decoders
/// decline outside it is the Advanced SIMD register file, the parallel
/// arithmetic and saturating packing instructions, and the encodings the
/// architecture calls unpredictable; `arm_parity_report` lists whatever the
/// corpus is currently missing. Raise this as it grows; never lower it.
const MIN_COVERAGE: f64 = 0.999;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// The first llvm-objdump on this machine. Version 18 is what the ARM
/// spellings here were written against.
fn objdump() -> Option<&'static str> {
    ["llvm-objdump-18", "llvm-objdump"]
        .into_iter()
        .find(|&c| Command::new(c).arg("--version").output().is_ok())
}

/// One disassembled line, or the start of a function.
enum Line {
    Insn {
        addr: u64,
        bytes: Vec<u8>,
        text: String,
    },
    Label,
}

/// Parse `llvm-objdump -d`. ARM prints one eight-digit word per instruction
/// and Thumb one or two four-digit halfwords, both already byte-swapped.
fn disassemble(tool: &str, path: &Path) -> Vec<Line> {
    let Ok(out) = Command::new(tool).arg("-d").arg(path).output() else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lines = Vec::new();
    for l in text.lines() {
        if l.ends_with(">:") {
            lines.push(Line::Label);
            continue;
        }
        let Some((left, rest)) = l.split_once(": ") else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let Some((raw, body)) = rest.split_once('\t') else {
            continue;
        };
        let mut bytes = Vec::new();
        let mut ok = true;
        for t in raw.split_whitespace() {
            match u32::from_str_radix(t, 16) {
                Ok(v) if t.len() == 8 => bytes.extend_from_slice(&v.to_le_bytes()),
                Ok(v) if t.len() == 4 => bytes.extend_from_slice(&(v as u16).to_le_bytes()),
                _ => ok = false,
            }
        }
        if !ok || bytes.is_empty() {
            continue;
        }
        // Drop the symbolic suffix and the immediate comment llvm appends.
        let cut = body.find(" <").into_iter().chain(body.find(" @")).min();
        let body = match cut {
            Some(i) => &body[..i],
            None => body,
        };
        lines.push(Line::Insn {
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

fn check(tool: &str, path: &Path, mode: Mode) -> Tally {
    let mut t = Tally::default();
    let mut thumb = Thumb::new();
    for l in disassemble(tool, path) {
        let (addr, bytes, want) = match l {
            // An IT block never spans a function, so the state resets here.
            Line::Label => {
                thumb.resume(ItState::default());
                continue;
            }
            Line::Insn { addr, bytes, text } => (addr, bytes, text),
        };
        if want.is_empty() || want.starts_with("<unknown>") || want.starts_with(".word") {
            continue;
        }
        let decoded = match mode {
            Mode::A32 => arm::decode(&bytes, Addr(addr)),
            Mode::T32 => {
                let before = thumb.state();
                let i = thumb.decode(&bytes, Addr(addr));
                if i.is_none() {
                    thumb.resume(before.advance());
                }
                i
            }
        };
        match decoded {
            None => {
                t.undecoded += 1;
                t.missing
                    .push(want.split('\t').next().unwrap_or("?").to_string());
            }
            Some(i) if i.len as usize != bytes.len() => t.wrong.push(format!(
                "{addr:x}: {bytes:02x?} length {} != llvm's {}",
                i.len,
                bytes.len()
            )),
            Some(i) => {
                let got = arm::format(&i);
                if got == want {
                    t.matched += 1;
                } else {
                    t.wrong.push(format!(
                        "{addr:x}: {bytes:02x?} llvm {want:?} != ours {got:?}"
                    ));
                }
            }
        }
    }
    t
}

/// Every ARM fixture, paired with the instruction set it was built for.
fn fixtures() -> Vec<(PathBuf, Mode)> {
    let Some(dir) = corpus() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let Ok(rd) = std::fs::read_dir(dir) else {
        return out;
    };
    for e in rd.flatten() {
        let p = e.path();
        let name = p
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        if name.contains(".arm.") {
            out.push((p, Mode::A32));
        } else if name.contains(".thumb.") {
            out.push((p, Mode::T32));
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

#[test]
fn arm_matches_llvm_objdump() {
    let (Some(tool), files) = (objdump(), fixtures()) else {
        return;
    };
    if files.is_empty() {
        return;
    }
    let mut all = Tally::default();
    let mut named = Vec::new();
    for (p, mode) in &files {
        let t = check(tool, p, *mode);
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        named.extend(t.wrong.iter().map(|w| format!("{name}: {w}")));
        all.merge(t);
    }
    if all.total() < 100 {
        return; // nothing useful to compare
    }

    // A wrong answer is a bug, and there is no allowance for any.
    if !named.is_empty() {
        let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
        for f in &named {
            let kind = f
                .split("llvm \"")
                .nth(1)
                .and_then(|s| s.split("\\t").next())
                .and_then(|s| s.split('"').next())
                .unwrap_or("length")
                .to_string();
            *by_kind.entry(kind).or_default() += 1;
        }
        let summary: Vec<String> = by_kind.iter().map(|(k, n)| format!("{k} x{n}")).collect();
        panic!(
            "{} of {} ARM instructions decode differently\nby mnemonic: {}\nfirst 20:\n{}",
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
        "decoded {:.3}% of {} ARM instructions, floor is {:.1}% ({} undecoded)",
        all.coverage() * 100.0,
        all.total(),
        MIN_COVERAGE * 100.0,
        all.undecoded
    );
    println!(
        "arm parity: {} instructions, {} matched, {} undecoded, {:.3}% coverage",
        all.total(),
        all.matched,
        all.undecoded,
        all.coverage() * 100.0
    );
}

#[test]
fn a32_decoding_is_a_pure_function_of_the_word() {
    for w in [0xe0813081u32, 0xe12fff1e, 0xea000004, 0xe92d4800] {
        assert_eq!(
            arm::decode_word(w, Addr(0x1000)),
            arm::decode_word(w, Addr(0x1000))
        );
    }
}

#[test]
fn no_encoding_panics() {
    // A wide stride still crosses every top-level group many times, which is
    // what a full sweep of the word space would cost too much to do here.
    let mut w: u32 = 0;
    loop {
        let _ = arm::decode_word(w, Addr(0x1000));
        let b = w.to_le_bytes();
        let _ = arm::decode_thumb(&b, Addr(0x1000), ItState::default());
        let Some(next) = w.checked_add(0x3ff1) else {
            break;
        };
        w = next;
    }
}

#[test]
fn it_blocks_predicate_the_instructions_after_them() {
    // `itt mi` then two instructions that print with the `mi` suffix, and a
    // third that does not.
    let mut t = Thumb::new();
    let bytes = [0x44u8, 0xbf, 0x00, 0x20, 0x00, 0x20, 0x00, 0x20];
    let mut out = Vec::new();
    let mut at = 0u64;
    while at < 8 {
        let i = t.decode(&bytes[at as usize..], Addr(at)).expect("decode");
        out.push(arm::format(&i));
        at += i.len as u64;
    }
    assert_eq!(
        out,
        [
            "itt\tmi",
            "movmi\tr0, #0x0",
            "movmi\tr0, #0x0",
            "movs\tr0, #0x0"
        ]
    );
}

/// A work list rather than a pass or fail: the disagreement and gap classes,
/// biggest first. Ignored by default.
#[test]
#[ignore]
fn arm_parity_report() {
    let (Some(tool), files) = (objdump(), fixtures()) else {
        return;
    };
    let mut wrong: BTreeMap<String, usize> = BTreeMap::new();
    let mut missing: BTreeMap<String, usize> = BTreeMap::new();
    let mut example: BTreeMap<String, String> = BTreeMap::new();
    let mut all = Tally::default();
    for (p, mode) in &files {
        let t = check(tool, p, *mode);
        for b in &t.wrong {
            let key = b
                .split("llvm \"")
                .nth(1)
                .and_then(|s| s.split("\\t").next())
                .and_then(|s| s.split('"').next())
                .unwrap_or("length")
                .to_string();
            *wrong.entry(key.clone()).or_default() += 1;
            example.entry(key).or_insert_with(|| b.clone());
        }
        for m in &t.missing {
            *missing.entry(m.clone()).or_default() += 1;
        }
        all.merge(t);
    }
    let mut v: Vec<_> = wrong.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!(
        "{} instructions, {} wrong, {} undecoded, {:.3}% coverage",
        all.total(),
        all.wrong.len(),
        all.undecoded,
        all.coverage() * 100.0
    );
    for (k, n) in v.iter().take(40) {
        println!("{n:>6}  {k:<16} {}", example[k]);
    }
    let mut mv: Vec<_> = missing.into_iter().collect();
    mv.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("--- undecoded ---");
    for (k, n) in mv.iter().take(40) {
        println!("{n:>6}  {k}");
    }
}

/// The barriers, which share their encoding space with the branches.
///
/// `dsb`, `dmb` and `isb` sit in the rows of the branch-and-miscellaneous
/// space where the field a conditional branch reads as its condition is 1110
/// or 1111 and is not one. A dispatch that tests the wrong bits sends them to
/// the branch decoder, which rejects them, and every function containing one
/// then stops at it: firmware is full of them and a Cortex-M image lost its
/// whole reset path to this.
#[test]
fn the_thumb_barriers_decode() {
    for (bytes, want) in [
        ([0xbfu8, 0xf3, 0x4f, 0x8f], "dsb"),
        ([0xbf, 0xf3, 0x5f, 0x8f], "dmb"),
        ([0xbf, 0xf3, 0x6f, 0x8f], "isb"),
    ] {
        let (i, _) = arm::decode_thumb(&bytes, Addr(0x1000), ItState::default())
            .unwrap_or_else(|| panic!("{want} does not decode"));
        assert_eq!(i.mnemonic, want);
        assert_eq!(i.len, 4);
    }
    // And a conditional branch in the same space still decodes as one, which
    // is the half that would pass if the barriers simply took everything.
    let (i, _) = arm::decode_thumb(
        &[0x00u8, 0xf0, 0x02, 0x80],
        Addr(0x1000),
        ItState::default(),
    )
    .expect("a wide conditional branch decodes");
    assert!(i.mnemonic.starts_with('b'), "{}", i.mnemonic);
}
