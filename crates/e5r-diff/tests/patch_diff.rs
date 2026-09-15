//! The use case the matcher exists for: given two builds, say what the patch
//! touched, and say it without burying the answer.

use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_format::LoadOptions;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

#[test]
fn a_build_against_itself_has_nothing_changed() {
    let (Some(a), Some(b)) = (open("hello.a64.O2"), open("hello.a64.O2")) else {
        return;
    };
    let d = e5r_diff::compare(&a, &b);
    assert!(d.matched.len() > 5, "only {} matched", d.matched.len());
    assert_eq!(d.changed_count(), 0, "a build differs from itself");
    assert!(d.added.is_empty() && d.removed.is_empty());
}

#[test]
fn a_one_line_patch_names_one_function() {
    // The whole point: the answer has to be short. A report that says ten
    // thousand things changed is a report nobody reads.
    let (Some(a), Some(b)) = (open("hello.a64.O2"), open("hello-patched.a64.O2")) else {
        return;
    };
    let d = e5r_diff::compare(&a, &b);
    assert!(
        d.changed_count() <= 2,
        "a one-line change reported {} changed functions: {:?}",
        d.changed_count(),
        d.changed().map(|m| m.name.clone()).collect::<Vec<_>>()
    );
    assert!(d.changed_count() >= 1, "the change was not noticed at all");
    assert!(
        d.identical_count() > 5,
        "only {} functions matched as identical",
        d.identical_count()
    );
    // Most changed first, which is the order this is read in.
    let scores: Vec<f64> = d.matched.iter().map(|m| m.similarity).collect();
    assert!(
        scores.windows(2).all(|w| w[0] <= w[1]),
        "the report is not ranked"
    );
}

#[test]
fn added_functions_are_reported_as_added() {
    let (Some(a), Some(b)) = (open("hello.a64.O2"), open("hello-grown.a64.O2")) else {
        return;
    };
    let d = e5r_diff::compare(&a, &b);
    let names: Vec<&str> = d.added.iter().map(|(_, n)| n.as_str()).collect();
    for want in ["extra_helper", "another_one"] {
        assert!(
            names.contains(&want),
            "{want} not reported as added: {names:?}"
        );
    }
    assert!(d.removed.is_empty(), "nothing was removed: {:?}", d.removed);
}

#[test]
fn a_match_that_is_not_byte_identical_is_never_called_unchanged() {
    // The mistake a patch diff must not make. The mnemonic multiset cannot see
    // a reordering, so a perfect score has to come from the bytes.
    let (Some(a), Some(b)) = (open("hello.a64.O2"), open("hello-patched.a64.O2")) else {
        return;
    };
    let d = e5r_diff::compare(&a, &b);
    for m in &d.matched {
        if m.similarity == 1.0 {
            let (Some(fa), Some(fb)) = (a.function(m.old), b.function(m.new)) else {
                continue;
            };
            let bytes = |p: &Program, f: &e5r_analysis::Function| -> Vec<u8> {
                f.cfg
                    .blocks
                    .values()
                    .filter_map(|blk| p.object.memory.slice(blk.range.start(), blk.range.len()))
                    .flatten()
                    .copied()
                    .collect()
            };
            assert_eq!(
                bytes(&a, fa),
                bytes(&b, fb),
                "{} scored 1.0 without identical bytes",
                m.name
            );
        }
    }
}

#[test]
fn optimization_levels_differ_where_the_source_is_ours() {
    // A check in the other direction. Only our own functions: the C runtime
    // stubs come from prebuilt objects and really are identical whatever
    // optimization level the program was compiled at.
    let (Some(a), Some(b)) = (open("hello.a64.O0"), open("hello.a64.O2")) else {
        return;
    };
    let d = e5r_diff::compare(&a, &b);
    let ours: Vec<&e5r_diff::Match> = d
        .matched
        .iter()
        .filter(|m| matches!(m.name.as_str(), "main" | "sum_to" | "classify"))
        .collect();
    if ours.is_empty() {
        return;
    }
    for m in &ours {
        assert!(
            m.changed(),
            "{} called identical across -O0 and -O2",
            m.name
        );
    }
}
