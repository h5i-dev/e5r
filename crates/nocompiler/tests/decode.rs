//! The decoder against llvm-mc, the external oracle (CONTRIBUTING.md).
//!
//! Every decision the decoder makes is covered by a structured enumeration
//! (every funct7/funct3 pair of the register-register opcodes, every 12-bit
//! immediate of the immediate opcodes, every funct3 of the rest) plus random
//! words. For each word:
//!
//! * if nocompiler decodes it, llvm-mc must decode it to the same text;
//! * if llvm-mc decodes it and nocompiler does not, the mnemonic must be one the
//!   profile excludes on purpose (CSR, FENCE, EBREAK, privileged).
//!
//! Skips, loudly, when llvm-mc is not installed.

use std::io::Write;
use std::process::{Command, Stdio};

/// What llvm-mc decodes that the profile leaves out (docs/isa/profile.md, section 2).
const EXCLUDED: &[&str] = &[
    "fence",
    "fence.i",
    "fence.tso",
    "pause",
    "ebreak",
    "csrrw",
    "csrrs",
    "csrrc",
    "csrrwi",
    "csrrsi",
    "csrrci",
    "unimp",
    "sret",
    "mret",
    "uret",
    "wfi",
    "sfence.vma",
    "dret",
];

/// The hypervisor extension's loads, stores and fences, which LLVM 15 decodes
/// without being asked to: privileged, so outside a user-mode profile.
fn is_excluded(m: &str) -> bool {
    EXCLUDED.contains(&m)
        || ["hlv.", "hlvx.", "hsv.", "hfence.", "hinval."]
            .iter()
            .any(|p| m.starts_with(p))
}

fn llvm_mc() -> Option<String> {
    let mc = std::env::var("LLVM_MC").unwrap_or_else(|_| "llvm-mc".into());
    Command::new(&mc)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|_| mc)
}

/// llvm-mc's text for each word, `None` where it reports an invalid encoding.
fn oracle(mc: &str, words: &[u32]) -> Vec<Option<String>> {
    let mut child = Command::new(mc)
        .args([
            "--disassemble",
            "-triple=riscv64",
            "-mattr=+m,+zba,+zbb",
            "-M",
            "no-aliases",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("llvm-mc runs");
    let mut input = String::new();
    for w in words {
        let b = w.to_le_bytes();
        input.push_str(&format!(
            "0x{:02x} 0x{:02x} 0x{:02x} 0x{:02x}\n",
            b[0], b[1], b[2], b[3]
        ));
    }
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()).unwrap());
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    let mut invalid = vec![false; words.len()];
    for line in stderr.lines() {
        if let Some(rest) = line.strip_prefix("<stdin>:") {
            if line.contains("invalid instruction encoding") {
                let n: usize = rest.split(':').next().unwrap().parse().unwrap();
                invalid[n - 1] = true;
            }
        }
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut texts = stdout
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && *l != ".text")
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "));
    let res: Vec<Option<String>> = invalid
        .iter()
        .map(|&bad| {
            if bad {
                None
            } else {
                Some(texts.next().expect("one line per valid word"))
            }
        })
        .collect();
    assert!(
        texts.next().is_none(),
        "llvm-mc printed more lines than valid words"
    );
    res
}

fn corpus() -> Vec<u32> {
    let mut w = Vec::new();
    let regs = (1u32 << 7) | (2 << 15) | (3 << 20); // rd = ra, rs1 = sp, rs2 = gp
    for opc in [0x33u32, 0x3b] {
        for f7 in 0..128u32 {
            for f3 in 0..8u32 {
                w.push(opc | regs | f3 << 12 | f7 << 25);
                // zext.h needs rs2 = 0.
                w.push(opc | (1 << 7) | (2 << 15) | f3 << 12 | f7 << 25);
            }
        }
    }
    for opc in [0x13u32, 0x1b, 0x03, 0x67, 0x73] {
        for f3 in 0..8u32 {
            for imm in 0..4096u32 {
                w.push(opc | (5 << 7) | f3 << 12 | (6 << 15) | imm << 20);
            }
        }
    }
    for opc in [0x23u32, 0x63] {
        for f3 in 0..8u32 {
            for hi in 0..128u32 {
                w.push(opc | (0x15 << 7) | f3 << 12 | (6 << 15) | (7 << 20) | hi << 25);
            }
        }
    }
    for opc in [0x37u32, 0x17, 0x6f] {
        for x in [0u32, 1, 0x7ff, 0x800, 0xfffff, 0x12345, 0x80000] {
            w.push(opc | (10 << 7) | x << 12);
        }
    }
    // Random words, mostly with an opcode the profile uses so they exercise
    // the field checks rather than the opcode check.
    let mut x: u64 = 0x9e3779b97f4a7c15;
    let opcodes = [
        0x37u32, 0x17, 0x6f, 0x67, 0x63, 0x03, 0x23, 0x13, 0x1b, 0x33, 0x3b, 0x73, 0x0f,
    ];
    for i in 0..60_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let r = (x >> 16) as u32;
        // Low bits 11: a 32-bit encoding. llvm-mc reads its input as a byte
        // stream and would resynchronise after a 16-bit parcel.
        w.push(if i % 8 == 0 {
            r | 3
        } else {
            (r & !0x7f) | opcodes[(x as usize) % opcodes.len()]
        });
    }
    w
}

#[test]
fn decoder_agrees_with_llvm_mc() {
    let Some(mc) = llvm_mc() else {
        eprintln!("SKIPPED decoder_agrees_with_llvm_mc: llvm-mc not found (set LLVM_MC)");
        return;
    };
    let words = corpus();
    let want = oracle(&mc, &words);
    let (mut decoded, mut excluded, mut wrong) = (0, 0, Vec::new());
    for (&w, theirs) in words.iter().zip(&want) {
        match (nocompiler::isa::decode(w), theirs) {
            (Some(i), Some(t)) => {
                decoded += 1;
                if i.asm_rel() != *t {
                    wrong.push(format!(
                        "{w:#010x}: nocompiler `{}`, llvm-mc `{t}`",
                        i.asm_rel()
                    ));
                }
            }
            (Some(i), None) => wrong.push(format!(
                "{w:#010x}: nocompiler `{}`, llvm-mc invalid",
                i.asm_rel()
            )),
            (None, Some(t)) => {
                let m = t.split_whitespace().next().unwrap_or("");
                if is_excluded(m) {
                    excluded += 1;
                } else {
                    wrong.push(format!(
                        "{w:#010x}: nocompiler none, llvm-mc `{t}` (not excluded by the profile)"
                    ));
                }
            }
            (None, None) => {}
        }
    }
    eprintln!(
        "{} words: {decoded} decoded identically, {excluded} excluded by the profile",
        words.len()
    );
    assert!(
        decoded > 50_000,
        "the corpus must exercise the decoder ({decoded})"
    );
    assert!(
        wrong.is_empty(),
        "{} disagreements:\n{}",
        wrong.len(),
        wrong[..wrong.len().min(40)].join("\n")
    );
}

/// The block/loop structure the profile tools recover from the committed example.
#[test]
fn sum_example_structure() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");
    let bytes = std::fs::read(path).expect("examples/elf/sum.elf is committed");
    let bin = nocompiler::load(&bytes).unwrap();
    assert!(
        bin.recorded.is_some(),
        "the committed example carries .nocompiler.struct"
    );
    let reports = bin.check();
    let sum = reports.iter().find(|r| r.name == "sum").unwrap();
    let m = sum.result.as_ref().unwrap();
    use nocompiler::profile::Kind;
    assert_eq!(m.nodes.len(), 1);
    assert_eq!(
        (m.nodes[0].kind, m.nodes[0].start, m.nodes[0].end),
        (Kind::Block, 0x11194, 0x111ac)
    );
    let l = &m.nodes[0].children[0];
    assert_eq!((l.kind, l.start, l.end), (Kind::Loop, 0x11198, 0x111ac));
    assert_eq!((m.frame, m.callees.len()), (0, 0));
    assert!(reports.iter().all(|r| r.result.is_ok()));
}
