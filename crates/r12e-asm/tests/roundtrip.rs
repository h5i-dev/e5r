//! G1 for the assembler: every instruction in the corpus, decoded, printed,
//! assembled, and compared against the bytes it came from.
//!
//! This is the property the crate exists for. A user copies a line out of
//! `r12e disas`, changes a register, and assembles it back; if the unchanged
//! line does not reproduce its own bytes then nothing built on top of this can
//! be trusted. The corpus is enumerated with an external disassembler rather
//! than with `r12e-format`, because the loader lives above this crate in the
//! dependency order and an assembler that needs a container parser to be
//! tested is an assembler wired the wrong way round.
//!
//! Where an encoding is not unique the comparison weakens: the produced bytes
//! are decoded again and the two instructions must be equal. The count of
//! those is reported, because it is the size of the gap between "assembles
//! back" and "assembles back to the same bytes".

mod common;

use common::{Line, corpus, decode_for, disassemble, normalize, objdump, render};

use r12e_asm::{AsmError, assemble};
use r12e_core::{Addr, Arch};

#[derive(Default)]
struct Tally {
    attempted: usize,
    exact: usize,
    equivalent: Vec<String>,
    refused: Vec<String>,
    wrong: Vec<String>,
}

fn roundtrip(arch: &Arch, lines: &[Line], t: &mut Tally) {
    for l in lines {
        let Some(insn) = decode_for(arch, &l.bytes, Addr(l.addr)) else {
            continue;
        };
        if insn.len as usize != l.bytes.len() {
            continue;
        }
        let text = render(arch, &insn);
        t.attempted += 1;
        match assemble(arch, &text, Addr(l.addr)) {
            Ok(e) if e.bytes() == l.bytes.as_slice() => t.exact += 1,
            Ok(e) => match decode_for(arch, e.bytes(), Addr(l.addr)) {
                Some(again)
                    if normalize(&again) == normalize(&insn) && again.len as usize == e.len() =>
                {
                    t.equivalent.push(format!(
                        "{}\t{} bytes for {}",
                        insn.mnemonic,
                        e.len(),
                        l.bytes.len()
                    ))
                }
                other => t.wrong.push(format!(
                    "{text:?} at {:#x}: {:02x?} became {:02x?}{}",
                    l.addr,
                    l.bytes,
                    e.bytes(),
                    match other {
                        Some(a) => format!(" which is {}", render(arch, &a)),
                        None => " which does not decode".to_string(),
                    }
                )),
            },
            Err(e) => t.refused.push(reason(insn.mnemonic, &e)),
        }
    }
}

/// One line per refusal, keyed so the report can count them by kind.
fn reason(mnemonic: &str, e: &AsmError) -> String {
    let kind = match e {
        AsmError::UnknownMnemonic(_) => "unknown mnemonic",
        AsmError::UnknownRegister(_) => "unknown register",
        AsmError::UnsupportedForm { .. } => "unsupported form",
        AsmError::UnsizedOperand { .. } => "unsized operand",
        AsmError::Syntax { .. } => "syntax",
        AsmError::Range { .. } | AsmError::BranchRange { .. } => "out of range",
        AsmError::Unaligned { .. } => "unaligned",
        AsmError::NoEncoding { .. } => "no encoding",
        _ => "other",
    };
    format!("{mnemonic}\t{kind}")
}

fn report(name: &str, t: &Tally) {
    let mut by_kind: std::collections::BTreeMap<&str, usize> = Default::default();
    for r in &t.refused {
        *by_kind.entry(r.as_str()).or_default() += 1;
    }
    println!(
        "{name}: attempted {}, exact {}, equivalent {}, refused {}, wrong {}",
        t.attempted,
        t.exact,
        t.equivalent.len(),
        t.refused.len(),
        t.wrong.len()
    );
    let mut alt: std::collections::BTreeMap<&str, usize> = Default::default();
    for a in &t.equivalent {
        *alt.entry(a.as_str()).or_default() += 1;
    }
    let mut alts: Vec<_> = alt.into_iter().collect();
    alts.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, n) in alts.iter().take(30) {
        println!("  alternative {n:>6}  {k}");
    }
    let mut kinds: Vec<_> = by_kind.into_iter().collect();
    kinds.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, n) in kinds.iter().take(200) {
        println!("  refused {n:>6}  {k}");
    }
    for w in t.wrong.iter().take(30) {
        println!("  WRONG {w}");
    }
}

fn run(arch: &Arch, tag: &str, floor: f64) {
    let Some(dir) = corpus() else {
        eprintln!("no fixtures, skipping");
        return;
    };
    let Some(tool) = objdump(arch) else {
        eprintln!("no disassembler for {arch:?}, skipping");
        return;
    };
    let mut t = Tally::default();
    let mut files = 0usize;
    for e in std::fs::read_dir(&dir).expect("fixtures").flatten() {
        let p = e.path();
        let Some(n) = p.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !n.contains(tag) || !p.is_file() {
            continue;
        }
        let lines = disassemble(tool, &p, arch);
        if lines.is_empty() {
            continue;
        }
        files += 1;
        roundtrip(arch, &lines, &mut t);
    }
    if t.attempted == 0 {
        eprintln!("no instructions found for {arch:?}, skipping");
        return;
    }
    println!("{arch:?}: {files} files");
    report(&format!("{arch:?}"), &t);
    assert!(
        t.wrong.is_empty(),
        "{} instructions assembled to different instructions",
        t.wrong.len()
    );
    let rate = (t.exact + t.equivalent.len()) as f64 / t.attempted as f64;
    assert!(
        rate >= floor,
        "{arch:?} round trip {rate:.4} is below the floor {floor:.4}"
    );
}

// The floors sit under the measured rates rather than on them. What is
// refused is SIMD and floating point, and how much of a corpus that is depends
// on which fixtures the fetch script got; a floor pinned to today's number
// would fail on a more vector-heavy fixture set without anything having
// regressed. A floor this far below it still fails the moment a whole family
// stops encoding, which is the regression worth catching.
//
// Measured when this was written: AArch64 13751/14387 exact, x86-64 11226
// exact plus 843 equivalent of 13777. Both zero wrong.

#[test]
fn x86_64_round_trips() {
    run(&Arch::X86_64, ".x64.", 0.80);
}

#[test]
fn aarch64_round_trips() {
    run(&Arch::AArch64, ".a64.", 0.90);
}
