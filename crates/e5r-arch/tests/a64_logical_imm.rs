//! The logical-immediate encoding space, swept and checked against llvm.
//!
//! One instruction group, every encoding of it. `orr Rd, ZR, #imm` is the one
//! that carries an alias decision -- it prints as `mov` only when no `movz` or
//! `movn` could spell the same constant -- and that decision is a three-branch
//! arithmetic predicate over `N`, `immr` and `imms` with no natural test case.
//! The corpus gate could not see it: a compiler emits the constants a program
//! happens to use, and the branch that was wrong covers constants with their
//! zeros in the top halfword, which the fixtures never asked for.
//!
//! So this walks the field space instead of a corpus, which is the only way
//! the count of encodings checked is a property of the architecture rather
//! than of whatever was compiled. `llvm-mc -disassemble` is the oracle.

use std::io::Write;
use std::process::{Command, Stdio};

use e5r_arch::aarch64;
use e5r_core::Addr;

fn llvm_mc() -> Option<&'static str> {
    ["llvm-mc-18", "llvm-mc"]
        .into_iter()
        .find(|c| Command::new(c).arg("--version").output().is_ok())
}

/// Every logical-immediate encoding, for both operations that take one.
///
/// `sf`, `opc`, `N`, `immr` and `imms` are the whole encoding; `Rn` and `Rd`
/// are held at `ZR` and `x0` because the alias turns on the first and the
/// second names no behaviour. Invalid `(N, imms)` pairs are swept too -- what
/// llvm rejects, this must reject.
fn candidates() -> Vec<u32> {
    let mut out = Vec::new();
    for sf in [0u32, 1] {
        // ORR, which aliases to MOV, and AND, which does not: the second is
        // the control, so a disagreement that shows up in both is not about
        // the alias.
        for opc in [0b01u32, 0b00] {
            for n in 0..2u32 {
                for immr in 0..64u32 {
                    for imms in 0..64u32 {
                        out.push(
                            (sf << 31)
                                | (opc << 29)
                                | (0b100100 << 23)
                                | (n << 22)
                                | (immr << 16)
                                | (imms << 10)
                                | (31 << 5),
                        );
                    }
                }
            }
        }
    }
    out
}

/// What llvm makes of each word, in order. `None` where it decodes nothing.
fn llvm_says(mc: &str, words: &[u32]) -> Vec<Option<String>> {
    let mut input = String::new();
    for w in words {
        for b in w.to_le_bytes() {
            input.push_str(&format!("0x{b:02x} "));
        }
        input.push('\n');
    }
    let mut child = Command::new(mc)
        .args(["-triple=aarch64", "-disassemble"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("llvm-mc did not start");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let text = String::from_utf8_lossy(&out.stdout);
    let err = String::from_utf8_lossy(&out.stderr);

    // One line of output per line of input, except that a word llvm cannot
    // decode produces a diagnostic on stderr and nothing on stdout. So the
    // undecodable ones are counted off stderr by their line number, and the
    // decoded ones consumed in order.
    let mut bad = std::collections::BTreeSet::new();
    for line in err.lines() {
        if let Some(n) = line.split(':').nth(1).and_then(|n| n.parse::<usize>().ok()) {
            bad.insert(n - 1);
        }
    }
    let mut decoded = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('.'));
    (0..words.len())
        .map(|i| {
            if bad.contains(&i) {
                None
            } else {
                // `udf` is how llvm-mc spells a word it could not decode, so it
                // is a decline here rather than an instruction.
                decoded
                    .next()
                    .and_then(|l| l.split_whitespace().next())
                    .filter(|m| *m != "udf")
                    .map(str::to_string)
            }
        })
        .collect()
}

/// Our mnemonic for a word, which is what the alias decision moves.
fn ours(w: u32) -> Option<String> {
    let insn = aarch64::decode(&w.to_le_bytes(), Addr(0x1000))?;
    Some(insn.mnemonic.to_string())
}

#[test]
fn every_logical_immediate_agrees_with_llvm() {
    let Some(mc) = llvm_mc() else {
        // Not a silent pass: the harness says what it could not check, and the
        // CI job installs llvm precisely so this never prints.
        panic!("no llvm-mc on PATH; this gate cannot run and must not report a pass");
    };
    let words = candidates();
    let theirs = llvm_says(mc, &words);
    assert_eq!(theirs.len(), words.len());

    let mut wrong = Vec::new();
    let mut ungated = 0;
    for (w, want) in words.iter().zip(&theirs) {
        match (ours(*w), want) {
            // Both decline. The encoding is not one.
            (None, None) => {}
            // llvm declines and we do not, or the reverse: a decoder that
            // invents an instruction is the worse of the two, and a decoder
            // that misses one is a gap. Both are wrong here, because this
            // space is small enough to be complete.
            (Some(got), None) => wrong.push((*w, got, "<undecodable>".to_string())),
            (None, Some(want)) => wrong.push((*w, "<declined>".to_string(), want.clone())),
            // Mnemonics, which is the whole question here: `mov` or `orr` is
            // the alias decision, and the operands of this group are checked
            // instruction for instruction by `objdump_parity`.
            (Some(got), Some(want)) => {
                if got != *want {
                    wrong.push((*w, got, want.clone()));
                } else {
                    ungated += 1;
                }
            }
        }
    }
    if !wrong.is_empty() {
        let shown: Vec<String> = wrong
            .iter()
            .take(10)
            .map(|(w, got, want)| format!("  {w:#010x}  ours {got:<28} llvm {want}"))
            .collect();
        panic!(
            "{} of {} logical-immediate encodings disagree with llvm-mc:\n{}",
            wrong.len(),
            words.len(),
            shown.join("\n")
        );
    }
    assert!(
        ungated > 4000,
        "only {ungated} encodings decoded at all: the sweep is not reaching the group"
    );
}
