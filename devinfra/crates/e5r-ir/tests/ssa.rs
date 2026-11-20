//! SSA construction and the dataflow that follows it, on real compiled code.
//!
//! The properties checked are the ones every later pass depends on: one
//! definition per value, every use reaching a definition or an explicit
//! undefined, one phi input per predecessor, and a large reduction in operation
//! count once the bookkeeping lifting produces is removed.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_core::{Addr, Arch};
use e5r_format::LoadOptions;
use e5r_ir::func;
use e5r_ir::opt;
use e5r_ir::ssa::{self, Operand, SsaFunction, SsaKind};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    if obj.arch != Arch::AArch64 {
        return None;
    }
    Some(analyze(obj, &Options::default()))
}

/// Lift one named function and put it in SSA form. Kept for the tests that
/// want a single function rather than the whole corpus.
#[allow(dead_code)]
fn ssa_of(p: &Program, name: &str) -> Option<(func::Function, SsaFunction)> {
    let f = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some(name))?;
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let ir = func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    let s = ssa::build(&ir);
    Some((ir, s))
}

/// Every function in a fixture, for the property checks.
fn all(p: &Program) -> Vec<(String, func::Function, SsaFunction)> {
    p.functions_by_address()
        .filter(|f| f.is_complete() && f.cfg.blocks.len() < 200)
        .filter_map(|f| {
            let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
                .cfg
                .blocks
                .iter()
                .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
                .collect();
            let ir = func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
            if !ir.is_complete() {
                return None;
            }
            let s = ssa::build(&ir);
            Some((f.display_name(), ir, s))
        })
        .collect()
}

#[test]
fn every_value_has_exactly_one_definition() {
    // The property SSA is named for, and the one every later pass assumes.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let functions = all(&p);
    assert!(!functions.is_empty(), "nothing lifted");
    for (name, _, s) in &functions {
        let mut seen = BTreeSet::new();
        for b in s.blocks.values() {
            for op in &b.ops {
                if let Some(v) = op.out {
                    assert!(seen.insert(v), "{name}: {v} defined twice");
                }
            }
        }
    }
}

#[test]
fn every_phi_has_one_input_per_predecessor() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    for (name, _, s) in all(&p) {
        for (at, b) in &s.blocks {
            for op in &b.ops {
                if op.kind != SsaKind::Phi {
                    continue;
                }
                assert_eq!(
                    op.inputs.len(),
                    b.predecessors.len(),
                    "{name} block {at}: phi has {} inputs for {} predecessors",
                    op.inputs.len(),
                    b.predecessors.len()
                );
            }
        }
    }
}

#[test]
fn phis_come_first_in_their_block() {
    // Anything that walks a block assumes this, and a phi in the middle would
    // mean its inputs depend on operations that run after it.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    for (name, _, s) in all(&p) {
        for (at, b) in &s.blocks {
            let mut seen_other = false;
            for op in &b.ops {
                match op.kind {
                    SsaKind::Phi => assert!(
                        !seen_other,
                        "{name} block {at}: a phi follows an ordinary operation"
                    ),
                    _ => seen_other = true,
                }
            }
        }
    }
}

#[test]
fn every_use_reaches_a_definition() {
    // An operand that names a value nothing defines would mean the renaming
    // lost a path, which no later pass could recover from.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    for (name, _, s) in all(&p) {
        let defined: BTreeSet<_> = s.definitions().keys().copied().collect();
        for (at, b) in &s.blocks {
            for op in &b.ops {
                for i in &op.inputs {
                    if let Operand::Value(v) = i {
                        assert!(
                            defined.contains(v),
                            "{name} block {at}: {v} is used but never defined"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn the_dataflow_passes_remove_most_of_the_bookkeeping() {
    // Lifting one instruction produces several operations and most are flags
    // nothing reads. If the passes did not remove them the IR would be
    // unreadable, which is the whole reason they exist.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let mut before = 0usize;
    let mut after = 0usize;
    for (_, _, mut s) in all(&p) {
        before += s.op_count();
        opt::optimize(&mut s);
        after += s.op_count();
    }
    assert!(before > 500, "only {before} operations to work with");
    let kept = after as f64 / before as f64;
    assert!(
        kept < 0.7,
        "the passes kept {:.0}% of {before} operations",
        kept * 100.0
    );
    println!(
        "dataflow: {before} operations to {after} ({:.0}% kept)",
        kept * 100.0
    );
}

#[test]
fn optimizing_preserves_the_single_definition_property() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    for (name, _, mut s) in all(&p) {
        opt::optimize(&mut s);
        let mut seen = BTreeSet::new();
        for b in s.blocks.values() {
            for op in &b.ops {
                if let Some(v) = op.out {
                    assert!(seen.insert(v), "{name}: {v} defined twice after optimizing");
                }
            }
        }
    }
}

#[test]
fn optimizing_keeps_every_operation_that_has_an_effect() {
    // Removing a store, a branch or a call would change what the program does.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    for (name, _, mut s) in all(&p) {
        let count = |f: &SsaFunction| -> usize {
            f.blocks
                .values()
                .flat_map(|b| b.ops.iter())
                .filter(|o| {
                    matches!(
                        o.kind,
                        SsaKind::Op(
                            e5r_ir::Op::Store
                                | e5r_ir::Op::Branch
                                | e5r_ir::Op::CBranch
                                | e5r_ir::Op::Call
                                | e5r_ir::Op::CallInd
                                | e5r_ir::Op::Return
                        )
                    )
                })
                .count()
        };
        let before = count(&s);
        opt::optimize(&mut s);
        assert_eq!(
            count(&s),
            before,
            "{name}: an effectful operation was removed"
        );
    }
}

#[test]
fn optimizing_terminates_on_every_function_in_the_corpus() {
    // A pass that runs to a fixed point has to reach one. Loops, recursion and
    // phi cycles are all here.
    for fixture in ["wide.a64.O2.o", "wide.a64.O0.o", "shapes.a64.O2.o"] {
        let Some(p) = open(fixture) else { continue };
        for (_, _, mut s) in all(&p) {
            let changes = opt::optimize(&mut s);
            // A second run must find nothing, or the fixed point was not one.
            let again = opt::optimize(&mut s);
            assert!(
                again.removed == 0 && again.folded == 0,
                "{fixture}: not at a fixed point after {changes:?}, second run {again:?}"
            );
        }
    }
}

#[test]
fn the_constant_folder_fires_on_real_code() {
    // Checking for a specific literal does not work: asked for a dense switch
    // returning 0x1111, 0x2222 and so on, the compiler emitted
    // `(n + 1) * 0x1111` as two shift-and-adds and no constant appears at all.
    // What can be checked is that folding happens across the corpus, which is
    // what says the folder reaches real code rather than only its own tests.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let mut folded = 0usize;
    for (_, _, mut s) in all(&p) {
        folded += opt::optimize(&mut s).folded;
    }
    assert!(
        folded > 10,
        "the folder fired {folded} times on the whole corpus"
    );
}
