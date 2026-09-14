//! Instruction-granularity diff, measured on a pair of builds whose source
//! difference is known exactly.
//!
//! `insndiff.a64` and its three siblings are the same program with one source
//! line changed each time: one operator substituted, one statement added, one
//! statement removed. The compiler is gcc at `-O0`, so what it emits is a
//! transcription of the source rather than a product of the scheduler, and the
//! expected edit list is exact. These tests assert that list, instruction for
//! instruction, rather than asserting that some difference was found.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::Addr;
use r12e_diff::{Edit, EditKind, FunctionDiff};
use r12e_format::LoadOptions;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

fn entry(p: &Program, name: &str) -> Option<Addr> {
    p.functions_by_address()
        .find(|f| f.raw_name() == Some(name))
        .map(|f| f.entry)
}

/// The instruction diff of one function, with the whole-program match as the
/// map that explains where a call's target went.
fn function_diff(old: &Program, new: &Program, name: &str) -> Option<FunctionDiff> {
    let d = r12e_diff::compare(old, new);
    let map = r12e_diff::mapping(&d);
    r12e_diff::compare_function(old, entry(old, name)?, new, entry(new, name)?, &map)
}

fn kinds(edits: &[Edit]) -> Vec<(EditKind, &str, &str)> {
    edits
        .iter()
        .map(|e| (e.kind, e.old_text.as_str(), e.new_text.as_str()))
        .collect()
}

fn mnemonic(text: &str) -> &str {
    text.split_whitespace().next().unwrap_or("")
}

#[test]
fn a_build_against_itself_has_no_edits() {
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff.a64")) else {
        return;
    };
    let d = function_diff(&a, &b, "mix").expect("mix in both builds");
    assert_eq!(kinds(&d.edits), vec![], "a build differs from itself");
    assert_eq!(d.same, d.old_insns);
    assert!(!d.truncated);
}

#[test]
fn one_substituted_operator_is_one_replaced_instruction() {
    // `acc = acc + i` became `acc = acc - i`. One instruction, same length, so
    // nothing after it moved and there is nothing else in the list.
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-sub.a64")) else {
        return;
    };
    let d = function_diff(&a, &b, "mix").expect("mix in both builds");
    assert_eq!(d.edits.len(), 1, "{:?}", kinds(&d.edits));
    let e = &d.edits[0];
    assert_eq!(e.kind, EditKind::Replace);
    assert_eq!(mnemonic(&e.old_text), "add", "{}", e.old_text);
    assert_eq!(mnemonic(&e.new_text), "sub", "{}", e.new_text);
    assert_eq!(d.old_insns, d.new_insns);
    assert_eq!(d.same, d.old_insns - 1);
    // Both addresses, which is the whole point of doing this at instruction
    // rather than function granularity. They are the same address here
    // because a substitution of equal length moves nothing.
    assert_eq!(e.old, Some(Addr(0x400164)));
    assert_eq!(e.new, e.old);
}

#[test]
fn one_added_statement_is_four_inserted_instructions_and_one_displacement() {
    // `acc = acc ^ 21` added inside the loop. At -O0 that is a load, a
    // constant, the operation and a store; the forward branch that skips into
    // the loop test then points four instructions further along, which is a
    // displacement and not a change.
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-ins.a64")) else {
        return;
    };
    let d = function_diff(&a, &b, "mix").expect("mix in both builds");
    assert_eq!(d.new_insns, d.old_insns + 4);

    let inserted: Vec<&str> = d
        .changes()
        .map(|e| {
            assert_eq!(e.kind, EditKind::Insert, "{:?}", kinds(&d.edits));
            mnemonic(&e.new_text)
        })
        .collect();
    assert_eq!(
        inserted,
        ["ldr", "mov", "eor", "str"],
        "{:?}",
        kinds(&d.edits)
    );

    // Exactly one instruction moved without changing, and it is a branch.
    let displaced: Vec<&Edit> = d
        .edits
        .iter()
        .filter(|e| e.kind == EditKind::Displaced)
        .collect();
    assert_eq!(displaced.len(), 1, "{:?}", kinds(&d.edits));
    assert_eq!(mnemonic(&displaced[0].old_text), "b");
    assert_ne!(displaced[0].old_text, displaced[0].new_text);

    // And nothing was called retargeted, which would mean the alignment could
    // not account for where a target went.
    assert!(!d.edits.iter().any(|e| e.kind == EditKind::Retargeted));
    assert_eq!(d.same, d.old_insns - 1);
}

#[test]
fn one_removed_statement_is_three_deleted_instructions() {
    // The same test in the other direction: `acc = acc - 7` removed.
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-del.a64")) else {
        return;
    };
    let d = function_diff(&a, &b, "mix").expect("mix in both builds");
    assert_eq!(d.old_insns, d.new_insns + 3);

    let deleted: Vec<&str> = d
        .changes()
        .map(|e| {
            assert_eq!(e.kind, EditKind::Delete, "{:?}", kinds(&d.edits));
            mnemonic(&e.old_text)
        })
        .collect();
    assert_eq!(deleted, ["ldr", "sub", "str"], "{:?}", kinds(&d.edits));
    assert_eq!(d.displaced_count(), 1, "{:?}", kinds(&d.edits));
    assert!(!d.edits.iter().any(|e| e.kind == EditKind::Retargeted));
}

#[test]
fn a_function_that_only_moved_has_no_changes_in_it() {
    // This is the claim the whole alignment exists to support. `_start` calls
    // `mix` and `other`; inserting instructions into `mix` pushes `other`
    // along, so every byte of the call in `_start` differs and the
    // function-level diff calls `_start` changed. Nothing in it did change,
    // and the instruction-level answer has to say so.
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-ins.a64")) else {
        return;
    };
    let d = r12e_diff::compare(&a, &b);
    let changed: Vec<&str> = d.changed().map(|m| m.name.as_str()).collect();
    assert!(
        changed.contains(&"_start"),
        "the function-level diff did not flag _start: {changed:?}"
    );

    let detail = function_diff(&a, &b, "_start").expect("_start in both builds");
    assert_eq!(
        detail.change_count(),
        0,
        "_start reported changes: {:?}",
        kinds(&detail.edits)
    );
    assert!(
        detail.displaced_count() >= 1,
        "nothing in _start was recognized as displaced"
    );
    // The call is one of them, and it is only explicable through the function
    // matching: the callee moved and the matcher says where to.
    assert!(
        detail
            .edits
            .iter()
            .any(|e| e.kind == EditKind::Displaced && mnemonic(&e.old_text) == "bl"),
        "{:?}",
        kinds(&detail.edits)
    );
}

#[test]
fn without_the_function_map_a_moved_callee_is_not_claimed_to_be_displaced() {
    // The negative of the test above. With no map, nothing accounts for the
    // call's new target, and the honest answer is that it was retargeted
    // rather than that it merely moved.
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-ins.a64")) else {
        return;
    };
    let empty = BTreeMap::new();
    let d = r12e_diff::compare_function(
        &a,
        entry(&a, "_start").unwrap(),
        &b,
        entry(&b, "_start").unwrap(),
        &empty,
    )
    .expect("_start in both builds");
    assert!(
        d.edits
            .iter()
            .any(|e| e.kind == EditKind::Retargeted && mnemonic(&e.old_text) == "bl"),
        "{:?}",
        kinds(&d.edits)
    );
}

#[test]
fn the_detail_pass_covers_every_function_the_summary_flagged() {
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-ins.a64")) else {
        return;
    };
    let d = r12e_diff::compare(&a, &b);
    let detail = r12e_diff::detail(&a, &b, &d);
    assert_eq!(detail.len(), d.changed_count());
    // Only `mix` actually changed; everything else the summary flagged moved.
    let with_changes: Vec<&str> = detail
        .iter()
        .filter(|f| f.changed())
        .map(|f| f.name.as_str())
        .collect();
    assert_eq!(with_changes, ["mix"], "{with_changes:?}");
}

#[test]
fn the_answer_does_not_depend_on_which_run_produced_it() {
    // Gate G5 applies here too: the alignment walks hash maps, and an answer
    // that came out of an iteration order would be a different answer on the
    // next run.
    let (Some(a), Some(b)) = (open("insndiff.a64"), open("insndiff-ins.a64")) else {
        return;
    };
    let first = r12e_diff::detail(&a, &b, &r12e_diff::compare(&a, &b));
    for _ in 0..4 {
        let again = r12e_diff::detail(&a, &b, &r12e_diff::compare(&a, &b));
        assert_eq!(first.len(), again.len());
        for (x, y) in first.iter().zip(&again) {
            assert_eq!(kinds(&x.edits), kinds(&y.edits), "{} is not stable", x.name);
        }
    }
}

#[test]
fn an_optimization_level_change_is_reported_without_blowing_up() {
    // Not a known-difference fixture: -O0 against -O2 is a rewrite, and the
    // only thing worth asserting is that the alignment terminates, stays
    // inside its budget and never claims more edits than there are
    // instructions.
    let (Some(a), Some(b)) = (open("hello.a64.O0"), open("hello.a64.O2")) else {
        return;
    };
    let d = r12e_diff::compare(&a, &b);
    for f in r12e_diff::detail(&a, &b, &d) {
        assert!(
            f.edits.len() <= (f.old_insns + f.new_insns) as usize,
            "{} reported {} edits for {} and {} instructions",
            f.name,
            f.edits.len(),
            f.old_insns,
            f.new_insns
        );
        assert!(f.same <= f.old_insns.min(f.new_insns));
    }
}
