//! Parse coverage over a real corpus of processor specifications.
//!
//! The only honest measure of a front end for someone else's language is how
//! much of that language's published corpus it reads. Ghidra ships a hundred
//! and fifty `.slaspec` files, each pulling in several `.sinc` files, written
//! by dozens of people over two decades, and between them they use every
//! corner of the grammar including the corners the manual does not mention.
//!
//! Two tests live here. `gate` is not ignored and runs in the ordinary suite:
//! it parses the toy specification checked in next to it, and, when a Ghidra
//! tree is present, a named handful of real ones. `report` is `#[ignore]`d and
//! sweeps the whole tree, printing the table that goes in the milestone notes.
//! Point either at a tree with `R12E_GHIDRA=/path/to/ghidra`.

use r12e_sleigh::model::Approximation;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Where the corpus is, if it is anywhere. A checkout that does not have one
/// still runs the suite it can.
fn ghidra_root() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("R12E_GHIDRA") {
        let p = PathBuf::from(p);
        return p.is_dir().then_some(p);
    }
    for guess in [
        "../ghidra",
        "../../ghidra",
        concat!(env!("HOME"), "/Ref/ghidra"),
        "/opt/ghidra",
    ] {
        let p = PathBuf::from(guess);
        if p.join("Ghidra/Processors").is_dir() {
            return Some(p);
        }
    }
    None
}

fn data_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

/// Every `.slaspec` under a directory, sorted so the report is stable.
fn specs(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    // Bounded so a symlink loop in someone's tree cannot turn a test into a
    // walk of the filesystem.
    let mut visited = 0usize;
    while let Some(dir) = stack.pop() {
        visited += 1;
        if visited > 100_000 {
            break;
        }
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            match entry.file_type() {
                Ok(t) if t.is_dir() => stack.push(path),
                Ok(t) if t.is_file() && path.extension().is_some_and(|e| e == "slaspec") => {
                    out.push(path)
                }
                _ => {}
            }
        }
    }
    out.sort();
    out
}

struct Outcome {
    name: String,
    result: Result<Stats, String>,
    millis: u128,
}

struct Stats {
    tables: usize,
    constructors: usize,
    /// The root table's width, as `min..max`.
    root: String,
    /// Constructors whose masks are only a filter, by what stopped the
    /// reduction.
    right_justified: usize,
    unknown_offset: usize,
    too_many: usize,
    /// Operands placed relative to a variable width subtable rather than at a
    /// fixed offset. Not a shortfall: it is the only correct answer for x86.
    relative: usize,
    /// Operands nothing in the constructor binds, which is the specification's
    /// own mistake rather than the parser's.
    unbound: usize,
    /// Operands measured from an operand that `Constructor::order` resolves
    /// later, which a decoder could not resolve at all. Anything but zero is a
    /// bug here.
    out_of_order: usize,
    /// Things the front end read but thought were wrong.
    warnings: usize,
}

/// Operands placed relative to one that is not resolved before them, and
/// orders that are not a permutation of the operand list.
fn out_of_order(spec: &r12e_sleigh::Spec) -> usize {
    let mut bad = 0;
    for c in &spec.constructors {
        let mut at = vec![usize::MAX; c.operands.len()];
        for (position, &i) in c.order.iter().enumerate() {
            match at.get_mut(i as usize) {
                Some(slot) if *slot == usize::MAX => *slot = position,
                _ => bad += 1,
            }
        }
        for (i, operand) in c.operands.iter().enumerate() {
            if let Some(base) = operand.offset.base {
                let (base, here) = (at.get(base as usize).copied().unwrap_or(usize::MAX), at[i]);
                if base >= here {
                    bad += 1;
                }
            }
        }
    }
    bad
}

fn parse_one(path: &Path) -> Outcome {
    let started = Instant::now();
    let result = r12e_sleigh::parse_file(path)
        .map(|spec| Stats {
            tables: spec.tables.len(),
            constructors: spec.constructors.len(),
            right_justified: spec
                .approximate_constructors()
                .filter(|(_, why)| *why == Approximation::RightJustified)
                .count(),
            unknown_offset: spec
                .approximate_constructors()
                .filter(|(_, why)| *why == Approximation::UnknownTokenOffset)
                .count(),
            too_many: spec
                .approximate_constructors()
                .filter(|(_, why)| *why == Approximation::TooManyAlternatives)
                .count(),
            relative: spec
                .constructors
                .iter()
                .flat_map(|c| &c.operands)
                .filter(|o| !o.offset.is_absolute())
                .count(),
            unbound: spec
                .constructors
                .iter()
                .flat_map(|c| &c.operands)
                .filter(|o| o.source == r12e_sleigh::model::OperandSource::Unbound)
                .count(),
            out_of_order: out_of_order(&spec),
            warnings: spec.warnings.len(),
            root: {
                let t = spec.table(spec.root());
                let max = if t.max_length == usize::MAX {
                    "*".to_string()
                } else {
                    t.max_length.to_string()
                };
                format!("{}..{max}", t.min_length)
            },
        })
        .map_err(|e| e.to_string());
    Outcome {
        name: path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default(),
        result,
        millis: started.elapsed().as_millis(),
    }
}

#[test]
fn a_toy_specification_from_the_manual_parses() {
    let path = data_dir().join("toy.slaspec");
    let spec = r12e_sleigh::parse_file(&path).expect("the toy specification parses");
    assert_eq!(spec.endian, r12e_sleigh::model::Endian::Big);
    let root = spec.table(spec.root());
    assert_eq!(root.constructors.len(), 3, "and, xor, or");
    // `op2` is a real subtable with three constructors.
    let op2 = match spec.lookup("op2") {
        Some(r12e_sleigh::model::Symbol::Table(id)) => id,
        other => panic!("op2 should be a table, found {other:?}"),
    };
    assert_eq!(spec.table(op2).constructors.len(), 3);
}

#[test]
fn gate() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set R12E_GHIDRA to run the corpus gate");
        return;
    };
    // The architectures M2 is gated on. Each is a different shape of
    // specification: fixed width, variable width, context driven, eight bit.
    // The expected root width is part of the gate, because a specification
    // that parses into constructors of the wrong length is not a pass: the
    // lengths are what a decoder steps the program counter by.
    // `*` is a width with no static bound, which is the honest answer where a
    // specification writes a prefix as a constructor that concatenates the
    // root table with itself: x86's 0x66 and 0xf3 and MIPS16's EXTEND. What
    // stops the recursion in practice is a context bit the pattern tests, and
    // this analysis does not evaluate context.
    let wanted = [
        ("6502", "1..3"),
        ("z80", "1..4"),
        ("avr8", "2..4"),
        ("TI_MSP430", "2..6"),
        ("SparcV9_32", "4..4"),
        ("riscv.ilp32d", "2..4"),
        ("ppc_32_be", "4..4"),
        ("mips32be", "2..*"),
        ("ARM7_le", "2..4"),
        ("AARCH64", "4..4"),
        ("x86-64", "1..*"),
    ];
    let all = specs(&root);
    let mut checked = 0usize;
    let mut failures = Vec::new();
    for (name, width) in wanted {
        let Some(path) = all
            .iter()
            .find(|p| p.file_stem().is_some_and(|s| s == name))
        else {
            continue;
        };
        checked += 1;
        let outcome = parse_one(path);
        match outcome.result {
            Ok(stats) => {
                assert!(
                    stats.constructors > 0,
                    "{name} parsed but produced no constructors"
                );
                assert_eq!(stats.root, width, "{name} root table width");
                assert_eq!(
                    stats.unbound, 0,
                    "{name} left {} operands bound to nothing",
                    stats.unbound
                );
                assert_eq!(
                    stats.out_of_order, 0,
                    "{name} placed operands a decoder could not resolve in order"
                );
            }
            Err(e) => failures.push(format!("{name}: {e}")),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {checked} gated specifications failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(
        checked > 0,
        "a Ghidra tree was found but held no gated specifications"
    );
}

#[test]
#[ignore = "sweeps the whole Ghidra corpus; run with --ignored for the table"]
fn report() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set R12E_GHIDRA to run the sweep");
        return;
    };
    let paths = specs(&root);
    let mut by_processor: BTreeMap<String, Vec<Outcome>> = BTreeMap::new();
    for path in &paths {
        // The processor directory is the useful grouping: `Ghidra/Processors/
        // <name>/data/languages/<spec>.slaspec`.
        let processor = path
            .ancestors()
            .nth(3)
            .and_then(|p| p.file_name())
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "other".into());
        by_processor
            .entry(processor)
            .or_default()
            .push(parse_one(path));
    }

    let mut ok = 0usize;
    let mut failed = 0usize;
    println!(
        "\n| processor | specification | result | tables | constructors | root | right just | unknown offset | too many alts | relative operands | unbound operands | out of order | warnings | ms |"
    );
    println!(
        "| --- | --- | --- | ---: | ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
    );
    for (processor, outcomes) in &by_processor {
        for outcome in outcomes {
            match &outcome.result {
                Ok(s) => {
                    ok += 1;
                    println!(
                        "| {processor} | {} | ok | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                        outcome.name,
                        s.tables,
                        s.constructors,
                        s.root,
                        s.right_justified,
                        s.unknown_offset,
                        s.too_many,
                        s.relative,
                        s.unbound,
                        s.out_of_order,
                        s.warnings,
                        outcome.millis
                    );
                }
                Err(e) => {
                    failed += 1;
                    println!(
                        "| {processor} | {} | FAILED | | | | | | | | | | | {} |\n|  |  | `{}` | | | | | | | | | | | |",
                        outcome.name,
                        outcome.millis,
                        e.replace('|', "/")
                    );
                }
            }
        }
    }
    let bad: usize = by_processor
        .values()
        .flatten()
        .filter_map(|o| o.result.as_ref().ok())
        .map(|s| s.out_of_order)
        .sum();
    println!("\n{ok} of {} parse, {failed} fail.", paths.len());
    assert_eq!(bad, 0, "operands placed out of resolution order");
}
