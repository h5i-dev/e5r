//! What a caller watching `analyze()` is told, and what it costs.
//!
//! Two things have to hold for a progress meter to be worth having. It has to
//! report every stage that runs, in the order they run, with a count that only
//! moves forward inside a pass. And attaching one must not change the answer:
//! a run being watched and a run not being watched have to agree function for
//! function, or the meter is measuring something other than the analysis.

mod common;

use std::sync::{Arc, Mutex};

use e5r_analysis::{Options, Session, Stage, Update};
use e5r_format::Object;

/// Analyze with every update recorded.
///
/// The callback owns a handle rather than borrowing one, because it outlives
/// this frame as far as the type system is concerned: the session may hand it
/// to the thread pool.
fn watch(object: Object, opts: &Options) -> (e5r_analysis::Program, Vec<Update>) {
    let seen: Arc<Mutex<Vec<Update>>> = Arc::new(Mutex::new(Vec::new()));
    let into = Arc::clone(&seen);
    let p = Session::new(object, opts.clone())
        .with_progress(move |u| into.lock().unwrap().push(u))
        .into_program();
    let updates = seen.lock().unwrap().clone();
    (p, updates)
}

#[test]
fn every_stage_reports_and_the_counts_only_go_up() {
    let Some((_, object)) = common::load("hello.static.a64") else {
        return;
    };
    let (_, updates) = watch(object, &Options::default());
    assert!(!updates.is_empty(), "analyze() reported nothing");

    // Every stage the options ask for has to appear. A stage that silently
    // stopped reporting would leave a caller staring at a frozen bar.
    for stage in [Stage::Discovery, Stage::Data, Stage::Xrefs, Stage::Strings] {
        assert!(
            updates.iter().any(|u| u.stage == stage),
            "no report from {}",
            stage.label()
        );
    }

    // Inside one pass of one stage, `done` never goes backwards and never
    // passes the total it declared.
    let mut last: Option<Update> = None;
    for u in &updates {
        if let Some(p) = last
            && p.stage == u.stage
            && p.round == u.round
        {
            assert!(
                u.done >= p.done,
                "{} went from {} back to {}",
                u.stage.label(),
                p.done,
                u.done
            );
        }
        if let Some(total) = u.total {
            assert!(
                u.done <= total,
                "{} reported {} of {}",
                u.stage.label(),
                u.done,
                total
            );
            assert!(u.fraction().is_some());
        }
        last = Some(*u);
    }

    // And each pass that declared a total finished at it, so a bar that
    // reached 90% is not left there.
    for stage in [Stage::Xrefs, Stage::Strings, Stage::Data] {
        let last = updates.iter().rfind(|u| u.stage == stage).unwrap();
        assert_eq!(
            Some(last.done),
            last.total,
            "{} stopped short of its own total",
            stage.label()
        );
    }
}

#[test]
fn a_stage_that_is_switched_off_does_not_report() {
    let Some((_, object)) = common::load("hello.a64.O2") else {
        return;
    };
    let opts = Options {
        strings: false,
        xrefs: false,
        ..Options::default()
    };
    let (_, updates) = watch(object, &opts);
    assert!(!updates.iter().any(|u| u.stage == Stage::Strings));
    assert!(!updates.iter().any(|u| u.stage == Stage::Xrefs));
    assert!(updates.iter().any(|u| u.stage == Stage::Discovery));
}

#[test]
fn watching_a_run_does_not_change_it() {
    // The whole point. If these two disagree the meter is not passive.
    let Some((_, a)) = common::load("hello.static.a64") else {
        return;
    };
    let (_, b) = common::load("hello.static.a64").unwrap();
    let opts = Options::default();
    let (watched, updates) = watch(a, &opts);
    let plain = e5r_analysis::analyze(b, &opts);
    assert!(updates.len() > 4);
    assert_eq!(common::fingerprint(&watched), common::fingerprint(&plain));
}
