//! Emulating selected paths, measured against what the processor did.
//!
//! `fixtures/emulate/paths.c` is compiled for both architectures and run for
//! real at build time: natively here, under qemu for the other. Its `_start`
//! records every answer it computed. These tests run the same functions in the
//! interpreter and compare against that recording, which is a stronger
//! statement than checking the emulator against itself.
//!
//! The layout of the recording is fixed by `_start`: twenty-five little-endian
//! words, then the twenty-seven plaintext bytes the decryptor produced.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use e5r_analysis::{Function, Options, Program, analyze};
use e5r_api::{Ending, Place, Setup, Span, emulate};
use e5r_core::Addr;
use e5r_format::LoadOptions;

/// Somewhere that is neither the image nor the stack, so a buffer placed there
/// is visibly the caller's doing.
const SCRATCH: u64 = 0x6000_0000;

/// How many plaintext bytes the decryptor produces.
const PLAIN: usize = 27;

/// Every fixture this file runs against. Two optimization levels each, because
/// which shape a compiler emits for a switch changes between them and the
/// point is to check the shape that got emitted.
const FIXTURES: [&str; 4] = [
    "em-paths.a64.O1",
    "em-paths.a64.O2",
    "em-paths.x64.O1",
    "em-paths.x64.O2",
];

fn build() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// What the processor recorded: the words, then the plaintext.
fn recorded(name: &str) -> Option<(Vec<u64>, Vec<u8>)> {
    let data = std::fs::read(build()?.join(format!("{name}.out"))).ok()?;
    if data.len() < PLAIN || (data.len() - PLAIN) % 8 != 0 {
        return None;
    }
    let split = data.len() - PLAIN;
    let words = data[..split]
        .chunks_exact(8)
        .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
        .collect();
    Some((words, data[split..].to_vec()))
}

fn func<'a>(p: &'a Program, name: &str) -> &'a Function {
    p.functions_by_address()
        .find(|f| f.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no function named {name}"))
}

fn address_of(p: &Program, name: &str) -> Addr {
    func(p, name).entry
}

/// Run every fixture that exists, and insist at least one did.
///
/// Returns how many ran, so a caller that counts something inside can tell a
/// real zero from a workspace with no fixtures built.
fn over_fixtures(what: &str, mut body: impl FnMut(&str, &Program, &[u64], &[u8])) -> usize {
    let mut ran = 0;
    for name in FIXTURES {
        let (Some(p), Some((words, plain))) = (open(name), recorded(name)) else {
            continue;
        };
        body(name, &p, &words, &plain);
        ran += 1;
    }
    if build().is_some_and(|d| d.join(FIXTURES[0]).exists()) {
        assert!(ran > 0, "{what}: no fixture ran");
    }
    ran
}

/// 1. A string that only exists once the code has run.
///
/// The ciphertext is in the image and the key rolls with it, so no entry means
/// anything on its own. The caller places a buffer, points the decryptor at it,
/// and reads it back; the answer is compared against the bytes the processor
/// itself produced from the same routine.
#[test]
fn a_decrypted_string_comes_back_as_the_processor_produced_it() {
    over_fixtures("decryption", |name, p, words, plain| {
        let setup = Setup {
            arguments: vec![SCRATCH],
            watch: vec![Span {
                at: SCRATCH,
                len: 64,
            }],
            ..Default::default()
        };
        let run = emulate::run(p, func(p, "decrypt"), &setup);
        assert_eq!(run.ending, Ending::Returned, "{name}");
        assert!(run.clean(), "{name}: {}", run.ending);
        assert_eq!(run.result, words[0], "{name}: length");
        assert_eq!(run.result, PLAIN as u64, "{name}: length");

        let got = run.region(SCRATCH).expect("watched span");
        assert_eq!(&got[..PLAIN], plain, "{name}: plaintext");
        assert_eq!(
            run.text(SCRATCH).as_deref(),
            Some(std::str::from_utf8(plain).unwrap()),
            "{name}"
        );
        // The buffer was not in the image, so every byte of it is a byte the
        // run wrote, and `written` has to agree with the watched span.
        for (i, b) in plain.iter().enumerate() {
            assert_eq!(run.written.get(&(SCRATCH + i as u64)), Some(b), "{name}");
        }
    });
}

/// 2. A control flow that is computed.
///
/// `dispatch` builds a masked table on its stack and indexes it with its
/// argument, so the image says nothing about where the branch goes. Running it
/// settles it, and the set of targets over the inputs is exactly the three
/// functions the source names.
#[test]
fn a_computed_branch_resolves_to_exactly_the_three_targets() {
    over_fixtures("dispatch", |name, p, words, _| {
        let f = func(p, "dispatch");
        let want: BTreeSet<Addr> = ["step_a", "step_b", "step_c"]
            .iter()
            .map(|n| address_of(p, n))
            .collect();
        // Static analysis settled none of the three, which is why running it is
        // worth anything. If a compiler ever folds the mask away, this is the
        // assertion that says the fixture stopped testing what it claims to.
        assert!(
            f.cfg.tables.is_empty() && !f.cfg.calls.iter().any(|c| want.contains(c)),
            "{name}: dispatch's targets are already known statically"
        );

        let inputs: Vec<Vec<u64>> = (0..6u64).map(|i| vec![i]).collect();
        let edges = emulate::resolve(p, f, &Setup::default(), &inputs);
        let inside: Vec<_> = edges
            .iter()
            .filter(|e| f.range.contains(e.at))
            .cloned()
            .collect();
        let got: BTreeSet<Addr> = inside.iter().map(|e| e.to).collect();
        assert_eq!(got, want, "{name}: targets");

        // Every edge carries the inputs it was seen under. That is the whole
        // of the evidence for it: an executed edge is a claim about those
        // inputs and not about the branch.
        for e in &inside {
            assert!(!e.under.is_empty(), "{name}: edge with no evidence");
            assert!(e.under.iter().all(|u| u.len() == 1), "{name}");
        }
        assert_eq!(inside.len(), 3, "{name}: one edge per target");

        // And the answers agree with the processor, seed for seed.
        for seed in 0..6u64 {
            let run = emulate::run(
                p,
                f,
                &Setup {
                    arguments: vec![seed],
                    ..Default::default()
                },
            );
            assert_eq!(run.ending, Ending::Returned, "{name}: dispatch({seed})");
            assert_eq!(
                run.result,
                words[19 + seed as usize],
                "{name}: dispatch({seed})"
            );
        }
    });
}

/// 3. A recovered jump table, confirmed by running the branch.
///
/// `pick` has eleven cases and `pick2`, right behind it in the image, has
/// seven, and the compilers here put the two tables back to back. A scan that
/// is not bounded by the guard runs out of the first into the second and
/// reports eighteen plausible targets for a switch with eleven. Running the
/// branch once per index is the check that catches it: a target nothing selects
/// is reported rather than believed.
///
/// Recovery does not find a table in every one of these functions, and where it
/// does not there is nothing to confirm. Those are skipped and counted, and the
/// count has a floor, so a recovery that quietly stopped finding tables at all
/// would fail here rather than pass by vacuum.
#[test]
fn a_jump_table_is_confirmed_index_by_index() {
    let mut checked = 0;
    let ran = over_fixtures("jump table", |name, p, words, _| {
        for (fname, cases, base) in [("pick", 11usize, 1usize), ("pick2", 7, 12)] {
            let f = func(p, fname);
            // Where recovery found a table, running the branch checks it. Where
            // it did not there is nothing to confirm, and that is a gap in
            // recovery rather than a failure of this gate.
            if let Some(table) = f.cfg.tables.first() {
                checked += 1;
                assert_eq!(table.targets.len(), cases, "{name}: {fname} table size");
                assert!(!table.bounded_by_scan, "{name}: {fname} sized by scanning");

                // Past the last case as well, so the guard rejecting an index
                // is observed rather than assumed.
                let indices: Vec<u64> = (0..cases as u64 + 5).collect();
                let setup = Setup {
                    arguments: vec![0, 3],
                    ..Default::default()
                };
                let c = emulate::confirm(p, f, table, &setup, 0, &indices);

                assert_eq!(c.taken.len(), cases, "{name}: {fname} indices reaching");
                assert_eq!(
                    c.rejected,
                    (cases as u64..cases as u64 + 5).collect::<Vec<_>>(),
                    "{name}: {fname} guard"
                );
                assert!(
                    c.agrees(),
                    "{name}: {fname} unreached {:?}, extra {:?}",
                    c.unreached,
                    c.extra
                );
                assert_eq!(c.reached.len(), cases, "{name}: {fname} distinct targets");
            }

            // The answers behind the cases, against what the processor computed
            // for the same calls. This holds table or no table: emulation
            // follows the branch either way.
            for i in 0..cases {
                let run = emulate::run(
                    p,
                    f,
                    &Setup {
                        arguments: vec![i as u64, 3],
                        ..Default::default()
                    },
                );
                assert_eq!(run.ending, Ending::Returned, "{name}: {fname}({i})");
                assert_eq!(run.result, words[base + i], "{name}: {fname}({i})");
            }

            // And the default arm, which the table does not cover.
            let run = emulate::run(
                p,
                f,
                &Setup {
                    arguments: vec![cases as u64, 3],
                    ..Default::default()
                },
            );
            let fallback = if fname == "pick" { 0xdead } else { 0xbeef };
            assert_eq!(run.result, fallback, "{name}: {fname} default arm");
        }

        // The hazard the confirmation exists for, made concrete: where both
        // tables were recovered they are adjacent, so nothing in the bytes
        // marks where the first one ends.
        if let (Some(a), Some(b)) = (
            func(p, "pick").cfg.tables.first(),
            func(p, "pick2").cfg.tables.first(),
        ) {
            let end = a.table.get() + a.entry_size * a.targets.len() as u64;
            assert_eq!(
                end,
                b.table.get(),
                "{name}: the two tables are not adjacent"
            );
        }
    });
    if ran > 0 {
        assert!(
            checked >= 3,
            "only {checked} recovered tables were confirmed"
        );
    }
}

/// A stubbed `write` records the bytes and writes nowhere.
#[test]
fn a_write_is_answered_and_recorded() {
    over_fixtures("write", |name, p, _, _| {
        let setup = Setup {
            arguments: vec![SCRATCH, 5],
            inputs: vec![Place {
                at: SCRATCH,
                bytes: b"hello".to_vec(),
            }],
            ..Default::default()
        };
        let run = emulate::run(p, func(p, "shout"), &setup);
        assert_eq!(run.ending, Ending::Returned, "{name}: {}", run.ending);
        assert_eq!(run.result, 5, "{name}");
        assert_eq!(run.written_out(), b"hello", "{name}");
        assert_eq!(run.syscalls.len(), 1, "{name}");
        assert!(run.syscalls[0].served(), "{name}");
        assert_eq!(run.syscalls[0].name, Some("write"), "{name}");
        assert_eq!(run.output[0].fd, 1, "{name}");
        // A run that took a stub is not a clean reading of the code alone, and
        // has to say so even though it returned.
        assert!(run.stubbed(), "{name}");
        assert!(!run.clean(), "{name}");
    });
}

/// A stubbed `read` hands back the caller's bytes, and end of file after that.
#[test]
fn a_read_hands_back_what_the_caller_supplied() {
    over_fixtures("read", |name, p, _, _| {
        let mut setup = Setup {
            arguments: vec![SCRATCH, 8],
            watch: vec![Span {
                at: SCRATCH,
                len: 8,
            }],
            ..Default::default()
        };
        setup.kernel.input = b"abcdefgh".to_vec();
        let run = emulate::run(p, func(p, "slurp"), &setup);
        assert_eq!(run.ending, Ending::Returned, "{name}: {}", run.ending);
        assert_eq!(run.result, 8, "{name}");
        assert_eq!(run.region(SCRATCH), Some(&b"abcdefgh"[..]), "{name}");

        // Nothing supplied means end of file, not an invented byte.
        let empty = Setup {
            arguments: vec![SCRATCH, 8],
            ..Default::default()
        };
        let run = emulate::run(p, func(p, "slurp"), &empty);
        assert_eq!(run.result, 0, "{name}: end of file");
        assert!(run.syscalls[0].served(), "{name}");
    });
}

/// A call with no stub stops the run and is reported by number.
#[test]
fn an_unmodelled_call_is_refused_by_number() {
    over_fixtures("refusal", |name, p, _, _| {
        let run = emulate::run(p, func(p, "unmodelled"), &Setup::default());
        match &run.ending {
            Ending::Syscall { number, .. } => assert_eq!(*number, 424242, "{name}"),
            other => panic!("{name}: {other}"),
        }
        assert_eq!(run.syscalls.len(), 1, "{name}");
        assert!(!run.syscalls[0].served(), "{name}");
        assert_eq!(run.syscalls[0].returned, None, "{name}");
        // No plausible value was put in the result register on the way out.
        assert!(run.output.is_empty(), "{name}");
    });
}

/// A budget that stops a run stops it, in bounded time, and says which of the
/// two things happened.
#[test]
fn a_budget_stops_a_run_and_says_so() {
    over_fixtures("budget", |name, p, _, _| {
        let budget = 200_000;
        let started = std::time::Instant::now();
        let run = emulate::run(
            p,
            func(p, "forever"),
            &Setup {
                arguments: vec![1],
                budget,
                ..Default::default()
            },
        );
        let took = started.elapsed();
        assert_eq!(run.ending, Ending::Budget, "{name}");
        assert!(!run.ending.finished(), "{name}");
        // The budget is checked between instructions, so the last one finishes:
        // the bound is the budget plus at most one instruction's worth of
        // operations, not the budget exactly.
        assert!(
            run.ops >= budget && run.ops < budget + 256,
            "{name}: {} operations for a budget of {budget}",
            run.ops
        );
        assert!(took.as_secs() < 30, "{name}: took {took:?}");

        // The same budget, a function that terminates: the reason has to be a
        // different one, or the reason is not saying anything.
        let done = emulate::run(
            p,
            func(p, "decrypt"),
            &Setup {
                arguments: vec![SCRATCH],
                budget,
                ..Default::default()
            },
        );
        assert_eq!(done.ending, Ending::Returned, "{name}");
        assert!(done.ending.finished(), "{name}");
        assert!(done.ops < budget, "{name}");
    });
}
