//! G4: function recovery measured against the symbol table as ground truth.
//!
//! A symbol table is not DWARF, but on a binary that has one it names every
//! function the compiler emitted, which is exactly the set discovery has to
//! find. Running against the stripped copy of the same binary measures what
//! discovery achieves with the symbols taken away.

use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::Addr;
use r12e_format::{LoadOptions, SymbolKind};

/// Recall floors. Raise as discovery improves; never lower.
///
/// Stripped sits high because `.eh_frame` survives stripping and carries the
/// boundaries, which is the reason the loader reads it. A fixture built without
/// unwind tables would sit well below this, and would need its own floor rather
/// than a lowering of this one.
const MIN_RECALL_NAMED: f64 = 0.99;
const MIN_RECALL_STRIPPED: f64 = 0.95;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// Function entries the symbol table names, which is the answer key.
fn ground_truth(p: &Program) -> Vec<Addr> {
    let mut v: Vec<Addr> = p
        .object
        .symbols
        .iter()
        .filter(|s| {
            s.kind == SymbolKind::Function
                && s.addr != Addr::ZERO
                && p.object.memory.is_executable(s.addr)
        })
        .map(|s| s.addr)
        .collect();
    v.sort_unstable();
    v.dedup();
    v
}

fn recall(p: &Program, truth: &[Addr]) -> f64 {
    if truth.is_empty() {
        return 1.0;
    }
    let found = truth.iter().filter(|a| p.function(**a).is_some()).count();
    found as f64 / truth.len() as f64
}

#[test]
fn every_named_function_is_recovered() {
    let Some(p) = open("hello.a64.O0") else {
        return;
    };
    let truth = ground_truth(&p);
    assert!(
        truth.len() >= 5,
        "only {} functions in the answer key",
        truth.len()
    );
    let r = recall(&p, &truth);
    let missed: Vec<String> = truth
        .iter()
        .filter(|a| p.function(**a).is_none())
        .map(|a| {
            format!(
                "{a} {}",
                p.object
                    .symbol_at(*a)
                    .map(|s| s.name.clone())
                    .unwrap_or_default()
            )
        })
        .collect();
    assert!(
        r >= MIN_RECALL_NAMED,
        "recall {:.3} below {MIN_RECALL_NAMED}; missed {missed:?}",
        r
    );
}

#[test]
fn stripping_the_symbols_keeps_most_functions() {
    let (Some(full), Some(stripped)) = (open("hello.a64.O2"), open("hello.a64.O2.stripped")) else {
        return;
    };
    let truth = ground_truth(&full);
    if truth.len() < 5 {
        return;
    }
    let r = recall(&stripped, &truth);
    assert!(
        r >= MIN_RECALL_STRIPPED,
        "stripped recall {:.3} below {MIN_RECALL_STRIPPED} on {} functions",
        r,
        truth.len()
    );
}

#[test]
fn analysis_is_deterministic_across_thread_counts() {
    let Some(dir) = corpus() else { return };
    let data = std::fs::read(dir.join("hello.a64.O0")).unwrap();
    let obj = r12e_format::load(&data, &LoadOptions::default()).unwrap();

    let fingerprint = |threads: usize| {
        let p = analyze(
            obj.clone(),
            &Options {
                threads: Some(threads),
                ..Options::default()
            },
        );
        let funcs: Vec<(u64, usize, u32)> = p
            .functions_by_address()
            .map(|f| (f.entry.get(), f.cfg.blocks.len(), f.cfg.insns()))
            .collect();
        let xrefs: Vec<(u64, u64)> = p
            .xrefs
            .all()
            .iter()
            .map(|x| (x.from.get(), x.to.get()))
            .collect();
        (funcs, xrefs, p.strings.len())
    };

    let one = fingerprint(1);
    for t in [2, 4, 8] {
        assert_eq!(one, fingerprint(t), "thread count {t} changed the answer");
    }
}

#[test]
fn no_function_claims_bytes_outside_executable_memory() {
    let Some(p) = open("hello.a64.O0") else {
        return;
    };
    for f in p.functions_by_address() {
        for b in f.cfg.blocks.values() {
            assert!(
                p.object.memory.is_executable(b.range.start()),
                "{} block at {} is not executable",
                f.display_name(),
                b.range
            );
        }
    }
}

#[test]
fn blocks_within_a_function_do_not_overlap() {
    let Some(p) = open("hello.a64.O0") else {
        return;
    };
    for f in p.functions_by_address() {
        let mut ranges: Vec<_> = f.cfg.blocks.values().map(|b| b.range).collect();
        ranges.sort_by_key(|r| r.start());
        for w in ranges.windows(2) {
            assert!(
                !w[0].overlaps(w[1]),
                "{}: {} overlaps {}",
                f.display_name(),
                w[0],
                w[1]
            );
        }
    }
}

#[test]
fn every_block_successor_is_a_block_or_outside_the_function() {
    let Some(p) = open("hello.a64.O0") else {
        return;
    };
    for f in p.functions_by_address() {
        for (at, b) in &f.cfg.blocks {
            for s in &b.successors {
                assert!(
                    f.cfg.blocks.contains_key(s),
                    "{}: block {at} goes to {s}, which is not a block",
                    f.display_name()
                );
            }
        }
    }
}

#[test]
fn a_tail_call_does_not_merge_two_functions() {
    // shapes.c has `tail_call` calling `sum_to` as its last act. The two must
    // stay separate: running them together is the classic sweep failure.
    let Some(p) = open("shapes.a64.O2.o") else {
        return;
    };
    let (Some(tail), Some(sum)) = (
        p.functions_by_address()
            .find(|f| f.name.as_deref() == Some("tail_call")),
        p.functions_by_address()
            .find(|f| f.name.as_deref() == Some("sum_to")),
    ) else {
        return;
    };
    assert_ne!(tail.entry, sum.entry);
    for b in tail.cfg.blocks.values() {
        assert!(
            !b.range.contains(sum.entry),
            "tail_call swallowed sum_to at {}",
            sum.entry
        );
    }
}

#[test]
fn large_binaries_analyze_without_panicking() {
    // The real corpus is where the panics are: this caught a zero-length block
    // that made a BTreeSet range with equal excluded bounds.
    for path in [
        "/lib/aarch64-linux-gnu/libc.so.6",
        "/usr/lib/aarch64-linux-gnu/libc.so.6",
        "/bin/bash",
    ] {
        let p = Path::new(path);
        if !p.is_file() {
            continue;
        }
        let data = std::fs::read(p).unwrap();
        let Ok(obj) = r12e_format::load(&data, &LoadOptions::default()) else {
            continue;
        };
        let prog = analyze(obj, &Options::default());
        assert!(
            prog.functions.len() > 100,
            "{path}: only {} functions",
            prog.functions.len()
        );
    }
}

#[test]
fn a_dense_switch_resolves_to_every_arm() {
    // shapes.c and wide.c both hold a dense switch, which a compiler turns
    // into a jump table. Every arm has to become a successor, or the function
    // is not fully analyzed.
    for (fixture, func, arms) in [
        ("shapes.a64.O2.o", "dense_switch", 8usize),
        ("wide.a64.O2.o", "dense", 12),
        ("wide.x64.O2.o", "dense", 12),
    ] {
        let Some(p) = open(fixture) else { continue };
        let Some(f) = p
            .functions_by_address()
            .find(|f| f.name.as_deref() == Some(func))
        else {
            continue;
        };
        // Either the compiler used a table, in which case it must resolve, or
        // it used a comparison chain, in which case there is nothing indirect.
        if f.cfg.tables.is_empty() {
            assert!(
                !f.cfg.has_indirect,
                "{fixture}/{func}: an indirect branch nothing resolved"
            );
            continue;
        }
        let t = &f.cfg.tables[0];
        assert!(
            t.targets.len() >= arms,
            "{fixture}/{func}: {} targets for {arms} arms",
            t.targets.len()
        );
        for target in &t.targets {
            assert!(
                p.object.memory.is_executable(*target),
                "{fixture}/{func}: target {target} is not executable"
            );
            assert!(
                f.range.contains(*target),
                "{fixture}/{func}: target {target} is outside the function"
            );
        }
        assert!(f.is_complete(), "{fixture}/{func}: still incomplete");
    }
}

/// A work list, not a gate: what jump table recovery found on a real binary.
#[test]
#[ignore]
fn jump_table_report() {
    for path in [
        "/usr/lib/aarch64-linux-gnu/libc.so.6",
        "/lib/aarch64-linux-gnu/libc.so.6",
    ] {
        let p = Path::new(path);
        if !p.is_file() {
            continue;
        }
        let data = std::fs::read(p).unwrap();
        let obj = r12e_format::load(&data, &LoadOptions::default()).unwrap();
        let prog = analyze(obj, &Options::default());
        let mut all: Vec<_> = prog
            .functions_by_address()
            .flat_map(|f| f.cfg.tables.iter().map(move |t| (f.entry, t)))
            .collect();
        all.sort_by_key(|(_, t)| std::cmp::Reverse(t.targets.len()));
        println!("{} tables", all.len());
        for (f, t) in all.iter().take(20) {
            println!(
                "fn {f} branch {} table {} size {} kind {:?} base {} -> {} targets (scan={})",
                t.at,
                t.table,
                t.entry_size,
                t.kind,
                t.base,
                t.targets.len(),
                t.bounded_by_scan
            );
        }
        break;
    }
}
