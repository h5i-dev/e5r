//! G2 for the assembler: the system assembler is asked the same question.
//!
//! The round-trip gate proves the encoder agrees with e5r's own decoder,
//! which would still be satisfied by two halves that are wrong in the same
//! direction. This one sends the same text to `as` and compares the bytes,
//! so an error would have to be shared with binutils to survive.
//!
//! A difference in bytes is not automatically a fault: `add eax, 0x1` has
//! several correct encodings and only one can be emitted. Those are counted
//! and reported. A difference that decodes to a different instruction is a
//! bug and fails the test.
//!
//! Each instruction is placed at its own sixteen-byte slot, so one assembler
//! run covers thousands of them and the k-th slot is the k-th instruction
//! whatever length either side chose. Instructions whose encoding depends on
//! where they sit are excluded here and covered by
//! [`branch_displacements_match_the_system_assembler`], which places them at
//! addresses it controls.

mod common;

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

use common::{corpus, decode_for, disassemble, normalize, objdump, render};

use e5r_asm::assemble;
use e5r_core::{Addr, Arch};

/// Bytes per slot. Longer than the longest x86 encoding, and a power of two so
/// `.p2align` states it directly.
const SLOT: u64 = 16;

/// The system assembler for `arch`, and the flags that make it read what the
/// printers emit.
fn assembler(arch: &Arch) -> Option<(&'static str, Vec<String>)> {
    match arch {
        Arch::X86_64 => {
            for (tool, args) in [
                ("clang", vec!["-target", "x86_64-linux-gnu", "-c"]),
                ("as", vec!["--64"]),
            ] {
                if Command::new(tool).arg("--version").output().is_ok() {
                    return Some((tool, args.into_iter().map(str::to_string).collect()));
                }
            }
            None
        }
        Arch::AArch64 => ["aarch64-linux-gnu-as", "as"]
            .into_iter()
            .find(|t| Command::new(t).arg("--version").output().is_ok())
            .map(|t| (t, Vec::new())),
        _ => None,
    }
}

/// What `.org` pads a gap with, chosen so the gap decodes in step.
fn fill(arch: &Arch) -> &'static str {
    match arch {
        Arch::X86_64 => ", 0x90",
        _ => "",
    }
}

fn header(arch: &Arch) -> &'static str {
    match arch {
        // The printers emit Intel syntax with no register sigils, which is not
        // what `as` defaults to.
        Arch::X86_64 => ".intel_syntax noprefix\n.text\n",
        _ => ".text\n",
    }
}

/// Run the system assembler over `body`, returning the object file path.
fn run_assembler(arch: &Arch, body: &str, dir: &Path) -> Option<std::path::PathBuf> {
    let (tool, args) = assembler(arch)?;
    let src = dir.join("oracle.s");
    let obj = dir.join("oracle.o");
    std::fs::write(&src, body).ok()?;
    let out = Command::new(tool)
        .args(&args)
        .arg(&src)
        .arg("-o")
        .arg(&obj)
        .output()
        .ok()?;
    if !out.status.success() {
        eprintln!(
            "system assembler refused the whole file:\n{}",
            String::from_utf8_lossy(&out.stderr)
                .lines()
                .take(10)
                .collect::<Vec<_>>()
                .join("\n")
        );
        return None;
    }
    Some(obj)
}

/// The line numbers `as` or `clang` complained about, one-based.
fn rejected_lines(arch: &Arch, body: &str, dir: &Path) -> Vec<usize> {
    let Some((tool, args)) = assembler(arch) else {
        return Vec::new();
    };
    let src = dir.join("probe.s");
    if std::fs::write(&src, body).is_err() {
        return Vec::new();
    }
    let Ok(out) = Command::new(tool)
        .args(&args)
        .arg(&src)
        .arg("-o")
        .arg(dir.join("probe.o"))
        .output()
    else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stderr);
    let mut bad = Vec::new();
    for l in text.lines() {
        // "probe.s:17: Error: ..." from as, "probe.s:17:5: error: ..." from clang.
        let Some(rest) = l.split(".s:").nth(1) else {
            continue;
        };
        let n: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(n) = n.parse::<usize>() {
            bad.push(n);
        }
    }
    bad.sort_unstable();
    bad.dedup();
    bad
}

#[derive(Default)]
struct Tally {
    compared: usize,
    same: usize,
    alternative: BTreeMap<String, usize>,
    wrong: Vec<String>,
    unassemblable: usize,
}

/// True when the bytes depend on where the instruction sits.
fn position_dependent(arch: &Arch, i: &e5r_arch::insn::Insn) -> bool {
    if matches!(
        i.flow,
        e5r_arch::insn::Flow::Branch(_)
            | e5r_arch::insn::Flow::CondBranch(_)
            | e5r_arch::insn::Flow::Call(_)
    ) {
        return true;
    }
    i.operands().iter().any(|o| match o {
        e5r_arch::insn::Operand::Addr(_) => true,
        e5r_arch::insn::Operand::Mem(m) => m.is_pc_relative(),
        _ => false,
    })
    // `adrp` and the literal loads carry a target without a branching flow.
    || matches!(arch, Arch::AArch64) && matches!(i.mnemonic, "adr" | "adrp")
}

fn compare(arch: &Arch, texts: &[(String, Vec<u8>)], dir: &Path, t: &mut Tally) {
    if texts.is_empty() {
        return;
    }
    // Some of what the printers emit is not what `as` accepts; those lines are
    // dropped rather than allowed to fail the whole file. Two passes is enough
    // in practice and keeps the runtime bounded.
    let mut kept: Vec<usize> = (0..texts.len()).collect();
    for _ in 0..2 {
        let body = source(arch, texts, &kept);
        let bad = rejected_lines(arch, &body, dir);
        if bad.is_empty() {
            break;
        }
        // Line one is the syntax directive, so the k-th instruction is on line
        // `2 + 2 * k`: a `.p2align` and then the instruction itself.
        let drop: std::collections::BTreeSet<usize> = bad
            .iter()
            .filter_map(|n| n.checked_sub(3).map(|d| d / 2))
            .collect();
        t.unassemblable += drop.len();
        kept = kept
            .iter()
            .enumerate()
            .filter(|(k, _)| !drop.contains(k))
            .map(|(_, v)| *v)
            .collect();
    }
    if kept.is_empty() {
        return;
    }
    let body = source(arch, texts, &kept);
    let Some(obj) = run_assembler(arch, &body, dir) else {
        return;
    };
    let Some(tool) = objdump(arch) else { return };
    let lines = disassemble(tool, &obj, arch);
    let mut at_slot: BTreeMap<u64, Vec<u8>> = BTreeMap::new();
    for l in lines {
        if l.addr % SLOT == 0 {
            at_slot.entry(l.addr).or_insert(l.bytes);
        }
    }
    for (k, ix) in kept.iter().enumerate() {
        let Some(theirs) = at_slot.get(&(k as u64 * SLOT)) else {
            continue;
        };
        let (text, ours) = &texts[*ix];
        t.compared += 1;
        if theirs == ours {
            t.same += 1;
            continue;
        }
        let mine = decode_for(arch, ours, Addr(0));
        let yours = decode_for(arch, theirs, Addr(0));
        match (mine, yours) {
            (Some(a), Some(b)) if normalize(&a) == normalize(&b) => {
                *t.alternative
                    .entry(format!(
                        "{}\t{} bytes for {}",
                        a.mnemonic,
                        ours.len(),
                        theirs.len()
                    ))
                    .or_default() += 1;
            }
            _ => t
                .wrong
                .push(format!("{text:?}: e5r {ours:02x?}, system {theirs:02x?}")),
        }
    }
}

fn source(arch: &Arch, texts: &[(String, Vec<u8>)], kept: &[usize]) -> String {
    let mut body = String::from(header(arch));
    for ix in kept {
        body.push_str(".p2align 4\n");
        // A tab separates the mnemonic from its operands in what the printers
        // emit, which is exactly what an assembler wants anyway.
        body.push_str(&texts[*ix].0);
        body.push('\n');
    }
    body
}

fn run(arch: &Arch, tag: &str) {
    let Some(dir) = corpus() else {
        eprintln!("no fixtures, skipping");
        return;
    };
    if assembler(arch).is_none() {
        eprintln!("no system assembler for {arch:?}, skipping");
        return;
    }
    let Some(tool) = objdump(arch) else {
        eprintln!("no disassembler for {arch:?}, skipping");
        return;
    };
    let tmp = std::env::temp_dir().join(format!("e5r-asm-oracle-{tag}"));
    let _ = std::fs::create_dir_all(&tmp);

    // One entry per distinct text, so the oracle spends its budget on
    // distinct forms rather than on the same prologue a thousand times.
    let mut seen: BTreeMap<String, Vec<u8>> = BTreeMap::new();
    for e in std::fs::read_dir(&dir).expect("fixtures").flatten() {
        let p = e.path();
        let Some(n) = p.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !n.contains(tag) || !p.is_file() {
            continue;
        }
        for l in disassemble(tool, &p, arch) {
            let Some(insn) = decode_for(arch, &l.bytes, Addr(l.addr)) else {
                continue;
            };
            if insn.len as usize != l.bytes.len() || position_dependent(arch, &insn) {
                continue;
            }
            let text = render(arch, &insn);
            if seen.contains_key(&text) {
                continue;
            }
            let Ok(ours) = assemble(arch, &text, Addr(0)) else {
                continue;
            };
            seen.insert(text, ours.bytes().to_vec());
        }
    }
    let texts: Vec<(String, Vec<u8>)> = seen.into_iter().collect();
    let mut t = Tally::default();
    // In batches, so one line the system assembler cannot parse costs a batch
    // rather than the corpus.
    for chunk in texts.chunks(400) {
        compare(arch, chunk, &tmp, &mut t);
    }
    println!(
        "{arch:?} oracle: distinct forms {}, compared {}, identical {}, alternative {}, unparsed by the system assembler {}, wrong {}",
        texts.len(),
        t.compared,
        t.same,
        t.alternative.values().sum::<usize>(),
        t.unassemblable,
        t.wrong.len()
    );
    let mut alts: Vec<_> = t.alternative.iter().collect();
    alts.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    for (k, n) in alts.iter().take(25) {
        println!("  alternative {n:>5}  {k}");
    }
    for w in t.wrong.iter().take(25) {
        println!("  WRONG {w}");
    }
    assert!(
        t.wrong.is_empty(),
        "{} instructions disagree with the system assembler in meaning, not only in encoding",
        t.wrong.len()
    );
    assert!(t.compared > 100, "the oracle compared almost nothing");
}

#[test]
fn x86_64_agrees_with_the_system_assembler() {
    run(&Arch::X86_64, ".x64.");
}

#[test]
fn aarch64_agrees_with_the_system_assembler() {
    run(&Arch::AArch64, ".a64.");
}

/// Branches, placed where this test says rather than where a fixture put them.
///
/// `.org` gives the system assembler the same addresses e5r was told, and the
/// targets are real labels in the same section so the assembler resolves them
/// itself rather than emitting a relocation. This is where the short-form
/// choice is checked: an assembler that always emitted the near form would
/// pass every other test in this file.
///
/// The displacements straddle the byte-displacement boundary on purpose, and
/// none of them is small enough to land a label inside another instruction,
/// which is what would make `.org` walk backwards.
#[test]
fn branch_displacements_match_the_system_assembler() {
    const BASE: u64 = 0x4000;
    const STRIDE: u64 = 0x100;
    for (arch, mnemonics, spread) in [
        (
            Arch::X86_64,
            &["jmp", "call", "je", "jne", "jg", "jbe"][..],
            &[
                -0x1000i64, -200, -127, -126, 0x20, 0x40, 129, 130, 200, 0x1000, 0x2000,
            ][..],
        ),
        (
            Arch::AArch64,
            &["b", "bl", "b.eq", "b.ne", "cbz", "cbnz", "tbz"][..],
            &[-0x2000i64, -0x1000, -8, 8, 0x1000, 0x2000][..],
        ),
    ] {
        if assembler(&arch).is_none() {
            eprintln!("no system assembler for {arch:?}, skipping");
            continue;
        }
        let tmp = std::env::temp_dir().join("e5r-asm-oracle-branch");
        let _ = std::fs::create_dir_all(&tmp);

        // Operands the branch takes ahead of its target, so the compare and
        // test forms are exercised too.
        let lead = |m: &str| match m {
            "cbz" | "cbnz" => "x0, ",
            "tbz" | "tbnz" => "x0, #3, ",
            _ => "",
        };

        let mut want: Vec<(String, Vec<u8>, u64)> = Vec::new();
        let mut labels: BTreeMap<u64, Vec<String>> = BTreeMap::new();
        let mut code: BTreeMap<u64, String> = BTreeMap::new();
        let mut at = BASE;
        for m in mnemonics {
            for d in spread {
                let target = at.wrapping_add(*d as u64);
                let text = format!("{m}\t{}{target:#x}", lead(m));
                let Ok(e) = assemble(&arch, &text, Addr(at)) else {
                    continue;
                };
                let label = format!("t{}", want.len());
                code.insert(at, format!("{m}\t{}{label}", lead(m)));
                labels.entry(target).or_default().push(label);
                want.push((text, e.bytes().to_vec(), at));
                at += STRIDE;
            }
        }
        let mut body = String::from(header(&arch));
        let mut addrs: Vec<u64> = labels.keys().chain(code.keys()).copied().collect();
        addrs.sort_unstable();
        addrs.dedup();
        for a in addrs {
            // Filling the gaps with one-byte no-ops rather than zeroes keeps
            // the disassembler in step: a five-byte instruction followed by an
            // odd number of zero bytes desynchronizes it, and the next
            // instruction is then never reported at the address it is at.
            body.push_str(&format!(".org {a}{}\n", fill(&arch)));
            for l in labels.get(&a).into_iter().flatten() {
                body.push_str(&format!("{l}:\n"));
            }
            if let Some(c) = code.get(&a) {
                body.push_str(c);
                body.push('\n');
            }
        }
        let Some(obj) = run_assembler(&arch, &body, &tmp) else {
            panic!("the system assembler refused the branch file");
        };
        let tool = objdump(&arch).expect("disassembler");
        let got: BTreeMap<u64, Vec<u8>> = disassemble(tool, &obj, &arch)
            .into_iter()
            .map(|l| (l.addr, l.bytes))
            .collect();
        let mut checked = 0usize;
        let mut differ = Vec::new();
        for (text, ours, at) in &want {
            let Some(theirs) = got.get(at) else {
                continue;
            };
            checked += 1;
            if theirs != ours {
                differ.push(format!(
                    "{text} at {at:#x}: e5r {ours:02x?}, system {theirs:02x?}"
                ));
            }
        }
        assert!(differ.is_empty(), "{}", differ.join("\n"));
        println!("{arch:?}: {checked} branch displacements match");
        assert!(
            checked > 10,
            "{arch:?} branch oracle compared almost nothing"
        );
    }
}

/// A target the encoding cannot reach is an error that says so, never a
/// displacement with its top bits thrown away.
#[test]
fn an_unreachable_branch_is_refused_rather_than_truncated() {
    use e5r_asm::AsmError;
    for (arch, text, from, to) in [
        (Arch::AArch64, "b.eq\t0x200000", 0u64, 0x200000u64),
        (Arch::AArch64, "cbz\tx0, 0x200000", 0, 0x200000),
        (Arch::AArch64, "tbz\tx0, #1, 0x20000", 0, 0x20000),
        (Arch::AArch64, "b\t0x10000000", 0, 0x10000000),
        (Arch::X86_64, "call\t0x90000000", 0, 0x90000000),
    ] {
        let e = assemble(&arch, text, Addr(from)).expect_err(text);
        match e {
            AsmError::BranchRange { from: f, to: t, .. } => {
                assert_eq!((f, t), (from, to), "{text}");
            }
            other => panic!("{text}: expected a branch range error, got {other}"),
        }
    }
    // One inside the range, so the test cannot pass by refusing everything.
    assert!(assemble(&Arch::AArch64, "b.eq\t0x1000", Addr(0)).is_ok());
    assert!(assemble(&Arch::AArch64, "b\t0x1000000", Addr(0)).is_ok());
}
