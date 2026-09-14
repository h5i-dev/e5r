//! The lazy session: what it computes, when, and that it agrees with the
//! eager path it replaced.

mod common;

use common::{fingerprint, load};
use r12e_analysis::{Options, Part, Session, analyze};

#[test]
fn asking_for_functions_does_not_compute_strings_or_xrefs() {
    let Some((_, obj)) = load("hello.a64.O2") else {
        return;
    };
    let s = Session::new(obj, Options::default());
    assert!(!s.is_computed(Part::Functions));
    assert!(!s.functions().is_empty());
    assert!(s.is_computed(Part::Functions));
    assert!(
        !s.is_computed(Part::Xrefs) && !s.is_computed(Part::Strings),
        "a session computed parts nothing asked for"
    );
    // And the parts that were asked for are still there afterwards.
    assert!(!s.strings().is_empty());
    assert!(s.is_computed(Part::Strings));
    assert!(!s.is_computed(Part::Xrefs));
}

#[test]
fn cross_references_pull_in_the_functions_they_need() {
    let Some((_, obj)) = load("hello.a64.O2") else {
        return;
    };
    let s = Session::new(obj, Options::default());
    let _ = s.xrefs();
    assert!(
        s.is_computed(Part::Functions),
        "xrefs are read off functions, so asking for them must compute functions"
    );
}

#[test]
fn a_session_forced_to_the_end_equals_the_eager_analysis() {
    for name in ["hello.a64.O2", "hello.a64.O0", "hello.go.stripped"] {
        let Some((_, obj)) = load(name) else {
            continue;
        };
        let eager = analyze(obj, &Options::default());
        let (_, obj2) = load(name).expect("second load");
        let lazy = Session::new(obj2, Options::default()).into_program();
        assert_eq!(
            fingerprint(&eager),
            fingerprint(&lazy),
            "{name}: lazy and eager disagree"
        );
    }
}

#[test]
fn a_part_switched_off_is_empty_either_way() {
    let Some((_, obj)) = load("hello.a64.O2") else {
        return;
    };
    let opts = Options {
        strings: false,
        xrefs: false,
        noreturn: false,
        ..Options::default()
    };
    let s = Session::new(obj, opts.clone());
    assert!(s.strings().is_empty());
    assert!(s.xrefs().is_empty());
    assert!(s.noreturn().is_empty());

    let (_, obj2) = load("hello.a64.O2").expect("second load");
    let eager = analyze(obj2, &opts);
    assert_eq!(fingerprint(&eager), fingerprint(&s.into_program()));
}

#[test]
fn a_thread_count_still_reaches_every_stage() {
    let Some((_, obj)) = load("hello.a64.O2") else {
        return;
    };
    let one = Session::new(
        obj,
        Options {
            threads: Some(1),
            ..Options::default()
        },
    )
    .into_program();
    let (_, obj2) = load("hello.a64.O2").expect("second load");
    let many = Session::new(
        obj2,
        Options {
            threads: Some(4),
            ..Options::default()
        },
    )
    .into_program();
    assert_eq!(fingerprint(&one), fingerprint(&many));
}
