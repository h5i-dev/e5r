//! The dataflow queries, against calls whose answers are known by
//! construction.
//!
//! `fixtures/dataflow/bounds.c` holds one wrapper per way of bounding a
//! length: a literal, a comparison that guards the call, a mask, a read
//! straight out of memory, and an argument that arrives from the caller. The
//! answer for each is decided by the source rather than by what the analysis
//! happens to manage, so this asserts the whole table rather than that the
//! query returned something.
//!
//! Every expected address is worked out from the cross reference index or by
//! decoding the function, which is a different path through the program than
//! the query takes. A test that asked the query where the call was and then
//! checked the query agreed would be checking nothing.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, XrefKind, analyze};
use r12e_core::Addr;
use r12e_format::LoadOptions;

/// The four builds: two architectures, two optimization levels.
const FIXTURES: [&str; 4] = [
    "df-bounds.a64.O0",
    "df-bounds.a64.O2",
    "df-bounds.x64.O0",
    "df-bounds.x64.O2",
];

fn build() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// One row as a map from column to what it prints as.
type Answer = Vec<BTreeMap<String, String>>;

fn ask(p: &Program, query: &str) -> Answer {
    let answer = r12e_api::query::run(p, query).unwrap_or_else(|e| panic!("{query:?}: {e}"));
    answer
        .rows
        .iter()
        .map(|row| {
            row.values
                .iter()
                .map(|(name, value)| (name.to_string(), value.to_string()))
                .collect()
        })
        .collect()
}

fn field(row: &BTreeMap<String, String>, name: &str) -> String {
    row.get(name)
        .unwrap_or_else(|| panic!("no column {name:?}"))
        .clone()
}

/// The one call from `caller` to `callee`, found through the cross references
/// rather than through the query being tested.
fn call_from(p: &Program, caller: &str, callee: &str) -> Addr {
    let target = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some(callee))
        .unwrap_or_else(|| panic!("no function named {callee}"));
    let mut found: Vec<Addr> = p
        .xrefs
        .to(target.entry)
        .iter()
        .filter(|x| x.kind == XrefKind::Call)
        .filter(|x| {
            p.function_at(x.from)
                .and_then(|f| f.name.clone())
                .as_deref()
                == Some(caller)
        })
        .map(|x| x.from)
        .collect();
    found.sort();
    found.dedup();
    assert_eq!(
        found.len(),
        1,
        "{caller} should hold exactly one call to {callee}, found {found:?}"
    );
    found[0]
}

/// The one indirect call in a function, found by decoding it.
fn indirect_call_in(p: &Program, caller: &str) -> Addr {
    let f = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some(caller))
        .unwrap_or_else(|| panic!("no function named {caller}"));
    // By the decoder's own classification of the instruction, which is a
    // different path to the answer than lifting it. Matched by name because
    // the architecture crate is not a dependency of this one.
    let found: Vec<Addr> = p
        .instructions(f)
        .iter()
        .filter(|i| format!("{:?}", i.flow) == "IndirectCall")
        .map(|i| i.addr)
        .collect();
    assert_eq!(
        found.len(),
        1,
        "{caller} should hold exactly one indirect call, found {found:?}"
    );
    found[0]
}

/// What one call to `memcpy` should say about its third argument.
struct Expect {
    function: &'static str,
    verdict: &'static str,
    basis: &'static str,
    bound: &'static str,
    strength: &'static str,
}

/// The whole table, per build.
///
/// Only one cell differs between builds, and it differs for a reason worth
/// pinning: at `-O0` on x86-64 the length lives in a frame slot that stack
/// promotion refuses, so the comparison that guards the call is a compare
/// against memory and the guard is not visible. The answer then has to be
/// `unknown`, which is the point. Claiming `unconstrained` there would be
/// reporting a limit of the analysis as a fact about the program. If
/// promotion learns that frame, this cell becomes the same `bounded` as the
/// others and this table is what says so.
fn expected(fixture: &str) -> Vec<Expect> {
    let spilled = fixture == "df-bounds.x64.O0";
    vec![
        Expect {
            function: "copy_literal_length",
            verdict: "bounded",
            basis: "literal",
            bound: "32",
            strength: "proven",
        },
        Expect {
            function: "copy_checked_length",
            verdict: if spilled { "unknown" } else { "bounded" },
            basis: if spilled { "no evidence" } else { "guard" },
            bound: if spilled { "-" } else { "0..=64" },
            strength: if spilled { "heuristic" } else { "inferred" },
        },
        Expect {
            function: "copy_masked_length",
            verdict: "bounded",
            basis: "narrowed",
            bound: "0..=63",
            strength: "inferred",
        },
        Expect {
            function: "copy_untrusted_length",
            verdict: "unconstrained",
            basis: "no constraint",
            bound: "-",
            strength: "inferred",
        },
        Expect {
            function: "copy_argument_length",
            verdict: "unknown",
            basis: if spilled {
                "no evidence"
            } else {
                "from the caller"
            },
            bound: "-",
            strength: "heuristic",
        },
    ]
}

#[test]
fn every_memcpy_length_gets_the_answer_its_source_dictates() {
    let mut ran = 0;
    for fixture in FIXTURES {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let want = expected(fixture);

        // The two halves of the question, asked separately: a call is in one
        // or the other and never in both.
        let bounded = ask(&p, "calls to \"memcpy\" where arg3 is bounded");
        let unbounded = ask(&p, "calls to \"memcpy\" where arg3 is not bounded");

        for case in &want {
            let rows = if case.verdict == "bounded" {
                &bounded
            } else {
                &unbounded
            };
            let matching: Vec<&BTreeMap<String, String>> = rows
                .iter()
                .filter(|r| field(r, "function") == case.function)
                .collect();
            assert_eq!(
                matching.len(),
                1,
                "{fixture}: {} should appear once in the {} half, appeared {} times",
                case.function,
                case.verdict,
                matching.len()
            );
            let row = matching[0];
            let at = call_from(&p, case.function, "memcpy");
            assert_eq!(
                field(row, "address"),
                format!("{at}"),
                "{fixture}: {} names the wrong call site",
                case.function
            );
            assert_eq!(field(row, "target"), "memcpy");
            assert_eq!(field(row, "argument"), "arg3");
            assert_eq!(
                field(row, "verdict"),
                case.verdict,
                "{fixture}: {}",
                case.function
            );
            assert_eq!(
                field(row, "basis"),
                case.basis,
                "{fixture}: {}",
                case.function
            );
            assert_eq!(
                field(row, "bound"),
                case.bound,
                "{fixture}: {}",
                case.function
            );
            assert_eq!(
                field(row, "strength"),
                case.strength,
                "{fixture}: {}",
                case.function
            );
        }

        // Exactly these calls and no others: a query that also returned the
        // call in `_start` or one inside `memcpy` would be wrong in a way the
        // per-case checks above cannot see.
        let mut seen: Vec<String> = bounded
            .iter()
            .chain(unbounded.iter())
            .map(|r| field(r, "function"))
            .collect();
        seen.sort();
        let mut all: Vec<String> = want.iter().map(|c| c.function.to_string()).collect();
        all.sort();
        assert_eq!(seen, all, "{fixture}: the two halves are not the whole");
    }
    assert!(ran > 0, "no dataflow fixture was built");
}

#[test]
fn the_two_ways_of_not_being_bounded_are_never_confused() {
    for fixture in FIXTURES {
        let Some(p) = open(fixture) else { continue };
        // The proved half on its own. `copy_untrusted_length` reads the length
        // out of memory and hands it over untouched; `copy_argument_length`
        // takes it from its caller, which this function cannot see, and that
        // is a different sentence.
        let proved = ask(&p, "calls to \"memcpy\" where arg3 is unconstrained");
        let names: Vec<String> = proved.iter().map(|r| field(r, "function")).collect();
        assert_eq!(
            names,
            vec!["copy_untrusted_length".to_string()],
            "{fixture}: only the value read from memory is proved unbounded"
        );
        assert_eq!(
            field(&proved[0], "address"),
            format!("{}", call_from(&p, "copy_untrusted_length", "memcpy"))
        );

        let unknown = ask(&p, "calls to \"memcpy\" where arg3 is unknown");
        let names: Vec<String> = unknown.iter().map(|r| field(r, "function")).collect();
        assert!(
            names.contains(&"copy_argument_length".to_string()),
            "{fixture}: a length that arrives from the caller is unknown, got {names:?}"
        );
        assert!(
            !names.contains(&"copy_untrusted_length".to_string()),
            "{fixture}: a proved answer must not also be reported as unknown"
        );
    }
}

#[test]
fn an_indirect_call_is_found_and_a_direct_one_is_named() {
    for fixture in FIXTURES {
        let Some(p) = open(fixture) else { continue };

        let rows = ask(&p, "calls where target is indirect");
        let names: Vec<String> = rows.iter().map(|r| field(r, "function")).collect();
        assert_eq!(
            names,
            vec!["copy_through_pointer".to_string()],
            "{fixture}: the only computed call in the image is the one through \
             the function pointer"
        );
        assert_eq!(
            field(&rows[0], "address"),
            format!("{}", indirect_call_in(&p, "copy_through_pointer")),
            "{fixture}: the indirect call is at the wrong address"
        );
        assert_eq!(field(&rows[0], "target"), "indirect");
        // That the machine computes its target is what the encoding says.
        assert_eq!(field(&rows[0], "strength"), "proven");

        let rows = ask(&p, "calls to \"strcpy\"");
        let names: Vec<String> = rows.iter().map(|r| field(r, "function")).collect();
        assert_eq!(names, vec!["copy_string".to_string()], "{fixture}");
        assert_eq!(
            field(&rows[0], "address"),
            format!("{}", call_from(&p, "copy_string", "strcpy")),
            "{fixture}"
        );
    }
}

#[test]
fn a_function_that_hands_a_call_something_it_read_is_the_one_reported() {
    for fixture in FIXTURES {
        let Some(p) = open(fixture) else { continue };
        let rows = ask(
            &p,
            "functions where reads any argument of a call to \"system\"",
        );
        let names: Vec<String> = rows.iter().map(|r| field(r, "name")).collect();
        // `run_fixed` passes a command the program carries, which is not a
        // value it read from anywhere.
        assert_eq!(
            names,
            vec!["run_from_input".to_string()],
            "{fixture}: only the function that passes on what it was given"
        );
    }
}

#[test]
fn the_values_reaching_an_argument_are_named_with_their_strength() {
    for fixture in FIXTURES {
        let Some(p) = open(fixture) else { continue };
        let rows = ask(&p, "values reaching arg1 of calls to \"system\"");
        let by_function: BTreeMap<String, &BTreeMap<String, String>> =
            rows.iter().map(|r| (field(r, "function"), r)).collect();
        assert_eq!(
            by_function.keys().cloned().collect::<Vec<_>>(),
            vec!["run_fixed".to_string(), "run_from_input".to_string()],
            "{fixture}: both calls to system have a value reaching their argument"
        );

        let fixed = by_function["run_fixed"];
        assert_eq!(field(fixed, "argument"), "arg1");
        assert_eq!(field(fixed, "source"), "string", "{fixture}");
        assert!(
            field(fixed, "detail").contains("/bin/echo hi"),
            "{fixture}: the command should be read out of the image, got {:?}",
            field(fixed, "detail")
        );
        // A literal is in the encoding, which is as known as anything gets.
        assert_eq!(field(fixed, "strength"), "proven", "{fixture}");
        assert_eq!(
            field(fixed, "address"),
            format!("{}", call_from(&p, "run_fixed", "system")),
            "{fixture}"
        );

        let passed = by_function["run_from_input"];
        assert_ne!(
            field(passed, "source"),
            "string",
            "{fixture}: a command that arrives from outside is not a literal"
        );
        assert_eq!(field(passed, "strength"), "inferred", "{fixture}");
        assert_eq!(
            field(passed, "address"),
            format!("{}", call_from(&p, "run_from_input", "system")),
            "{fixture}"
        );
    }
}

#[test]
fn a_query_about_an_argument_ignores_calls_that_have_no_such_argument() {
    for fixture in FIXTURES {
        let Some(p) = open(fixture) else { continue };
        // `system` takes one argument, so nothing it is passed can answer a
        // question about a third one. The answer is empty rather than every
        // call to it, which is what a missing argument would give if the
        // negation were taken at face value.
        let rows = ask(&p, "calls to \"system\" where arg3 is not bounded");
        assert!(
            rows.is_empty(),
            "{fixture}: a one-argument call has no third argument to be unbounded, \
             got {} rows",
            rows.len()
        );
        let rows = ask(&p, "calls to \"system\" where arg1 is not bounded");
        assert!(
            !rows.is_empty(),
            "{fixture}: the one argument it does take is still a question"
        );
    }
}
