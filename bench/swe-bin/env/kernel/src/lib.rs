//! swe-bin: the kernel. Every reward and `done` decision of the environment, in the subset of
//! Rust that Charon and Aeneas translate to Lean (no `?`, no closures, no `String`, no
//! iterators). `h5i app extract` turns it into `proofs/generated/`; `proofs/Theorems.lean`
//! proves things about that code.
//!
//! An episode is one task in one mode:
//! * `Patch` (the default): the agent gets the buggy base binary and edits it. This is the port
//!   of SWE-bench: the issue is resolved when every FAIL_TO_PASS test and every PASS_TO_PASS
//!   test passes against the submitted binary.
//! * `Scratch`: SWE-bench-derived (function-level from-scratch). The functions the gold patch
//!   changes are stubbed out, and the agent writes them as binary. Same test criterion.
//!
//! The harness (trusted shell code in the server) runs the tests and the proof checker and
//! reports what it saw with `RecordTests` and `RecordProof`, each about one binary, named by
//! its SHA-256. `Submit` names the final binary: the kernel pays only for reports about that
//! binary.

#![allow(clippy::manual_range_contains, clippy::needless_range_loop)]

/// The reward when every test passes, in thousandths.
pub const FULL_MILLI: u64 = 1000;
/// The bonus on top of `FULL_MILLI` for a checked proof of the mode's kind.
pub const BONUS_MILLI: u64 = 250;
/// Test counts a task may have (so that a count is never near u32 overflow).
pub const MAX_TESTS: u32 = 100_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Patch,
    Scratch,
}

/// What a proof is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofKind {
    /// The functions the agent did not change refine the original binary's
    /// (`Refines.of_sub` / `Verified.of_sub`): patch mode's bonus.
    Refines,
    /// Every function the agent wrote is `Verified` against a spec the agent stated, and the
    /// spec passed the non-vacuity check: scratch mode's bonus.
    Verified,
}

/// A SHA-256 digest, as four big-endian words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hash {
    pub w: [u64; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Task {
    pub id: u32,
    pub mode: Mode,
    /// The number of FAIL_TO_PASS and PASS_TO_PASS tests the harness runs.
    pub f2p: u32,
    pub p2p: u32,
}

/// The harness's test report for one binary: how many tests of each kind passed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tests {
    pub binary: Hash,
    pub f2p_passed: u32,
    pub p2p_passed: u32,
}

/// The proof checker's result for one binary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proof {
    pub binary: Hash,
    pub kind: ProofKind,
    pub checked: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Snapshot {
    pub task: Task,
    pub started: bool,
    pub tests: Option<Tests>,
    pub proof: Option<Proof>,
    pub submitted: Option<Hash>,
    pub done: bool,
    pub reward_milli: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    Reset { task: Task },
    RecordTests { tests: Tests },
    RecordProof { proof: Proof },
    Submit { binary: Hash },
    State,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reply {
    pub reward_milli: u64,
    pub done: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A task without a FAIL_TO_PASS test, or with too many tests.
    InvalidTask,
    /// No `Reset` yet.
    NotStarted,
    /// The episode has ended.
    Done,
    /// A report with more passing tests than the task has.
    InvalidReport,
}

pub fn zero_hash() -> Hash {
    Hash { w: [0, 0, 0, 0] }
}

pub fn initial() -> Snapshot {
    Snapshot {
        task: Task {
            id: 0,
            mode: Mode::Patch,
            f2p: 1,
            p2p: 0,
        },
        started: false,
        tests: None,
        proof: None,
        submitted: None,
        done: false,
        reward_milli: 0,
    }
}

impl Default for Snapshot {
    fn default() -> Self {
        initial()
    }
}

pub fn hash_eq(a: &Hash, b: &Hash) -> bool {
    a.w[0] == b.w[0] && a.w[1] == b.w[1] && a.w[2] == b.w[2] && a.w[3] == b.w[3]
}

/// The tasks `Reset` accepts.
pub fn valid_task(t: &Task) -> bool {
    1 <= t.f2p && t.f2p <= MAX_TESTS && t.p2p <= MAX_TESTS
}

/// The proof kind that earns the bonus in a mode.
pub fn bonus_kind(m: Mode) -> ProofKind {
    match m {
        Mode::Patch => ProofKind::Refines,
        Mode::Scratch => ProofKind::Verified,
    }
}

fn kind_eq(a: ProofKind, b: ProofKind) -> bool {
    match a {
        ProofKind::Refines => match b {
            ProofKind::Refines => true,
            ProofKind::Verified => false,
        },
        ProofKind::Verified => match b {
            ProofKind::Refines => false,
            ProofKind::Verified => true,
        },
    }
}

/// Every test of the task passed against `binary`.
pub fn all_pass(t: &Task, tests: &Option<Tests>, binary: &Hash) -> bool {
    match tests {
        Some(r) => hash_eq(&r.binary, binary) && r.f2p_passed == t.f2p && r.p2p_passed == t.p2p,
        None => false,
    }
}

/// A proof of the mode's kind checked for `binary`.
pub fn proof_ok(t: &Task, proof: &Option<Proof>, binary: &Hash) -> bool {
    match proof {
        Some(p) => p.checked && hash_eq(&p.binary, binary) && kind_eq(p.kind, bonus_kind(t.mode)),
        None => false,
    }
}

/// The reward for submitting `binary`.
pub fn reward(t: &Task, tests: &Option<Tests>, proof: &Option<Proof>, binary: &Hash) -> u64 {
    if all_pass(t, tests, binary) {
        if proof_ok(t, proof, binary) {
            FULL_MILLI + BONUS_MILLI
        } else {
            FULL_MILLI
        }
    } else {
        0
    }
}

fn reply(s: &Snapshot) -> Reply {
    Reply {
        reward_milli: s.reward_milli,
        done: s.done,
    }
}

/// One command: the snapshot to commit (`None` writes nothing) and the reply, or a refusal
/// that commits nothing.
pub fn transition(
    _actor: &(),
    s: &Snapshot,
    cmd: &Command,
) -> Result<(Option<Snapshot>, Reply), Error> {
    match cmd {
        Command::Reset { task } => {
            if valid_task(task) {
                let next = Snapshot {
                    task: *task,
                    started: true,
                    tests: None,
                    proof: None,
                    submitted: None,
                    done: false,
                    reward_milli: 0,
                };
                Ok((Some(next), reply(&next)))
            } else {
                Err(Error::InvalidTask)
            }
        }
        Command::RecordTests { tests } => {
            if s.done {
                Err(Error::Done)
            } else if !s.started {
                Err(Error::NotStarted)
            } else if tests.f2p_passed > s.task.f2p || tests.p2p_passed > s.task.p2p {
                Err(Error::InvalidReport)
            } else {
                let next = Snapshot {
                    task: s.task,
                    started: true,
                    tests: Some(*tests),
                    proof: s.proof,
                    submitted: None,
                    done: false,
                    reward_milli: 0,
                };
                Ok((Some(next), reply(&next)))
            }
        }
        Command::RecordProof { proof } => {
            if s.done {
                Err(Error::Done)
            } else if !s.started {
                Err(Error::NotStarted)
            } else {
                let next = Snapshot {
                    task: s.task,
                    started: true,
                    tests: s.tests,
                    proof: Some(*proof),
                    submitted: None,
                    done: false,
                    reward_milli: 0,
                };
                Ok((Some(next), reply(&next)))
            }
        }
        Command::Submit { binary } => {
            if s.done {
                Err(Error::Done)
            } else if !s.started {
                Err(Error::NotStarted)
            } else {
                let next = Snapshot {
                    task: s.task,
                    started: true,
                    tests: s.tests,
                    proof: s.proof,
                    submitted: Some(*binary),
                    done: true,
                    reward_milli: reward(&s.task, &s.tests, &s.proof, binary),
                };
                Ok((Some(next), reply(&next)))
            }
        }
        Command::State => Ok((None, reply(s))),
    }
}

/// Commit a write set: the next snapshot, or no change.
pub fn apply(s: &Snapshot, w: &Option<Snapshot>) -> Snapshot {
    match w {
        Some(next) => *next,
        None => *s,
    }
}

/// Only `State` reads without writing.
pub fn read_only(cmd: &Command) -> bool {
    match cmd {
        Command::State => true,
        Command::Reset { .. } => false,
        Command::RecordTests { .. } => false,
        Command::RecordProof { .. } => false,
        Command::Submit { .. } => false,
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    fn h(x: u64) -> Hash {
        Hash { w: [x, 0, 0, 0] }
    }

    fn run(s: &Snapshot, c: Command) -> Result<Snapshot, Error> {
        transition(&(), s, &c).map(|(w, _)| apply(s, &w))
    }

    fn task(mode: Mode) -> Task {
        Task {
            id: 7,
            mode,
            f2p: 2,
            p2p: 3,
        }
    }

    fn started(mode: Mode) -> Snapshot {
        run(&initial(), Command::Reset { task: task(mode) }).unwrap()
    }

    fn tests(b: u64, f: u32, p: u32) -> Command {
        Command::RecordTests {
            tests: Tests {
                binary: h(b),
                f2p_passed: f,
                p2p_passed: p,
            },
        }
    }

    fn proof(b: u64, kind: ProofKind, checked: bool) -> Command {
        Command::RecordProof {
            proof: Proof {
                binary: h(b),
                kind,
                checked,
            },
        }
    }

    #[test]
    fn all_tests_pay_full() {
        let s = run(&started(Mode::Patch), tests(1, 2, 3)).unwrap();
        let s = run(&s, Command::Submit { binary: h(1) }).unwrap();
        assert_eq!((s.reward_milli, s.done), (FULL_MILLI, true));
    }

    #[test]
    fn a_failing_test_pays_nothing() {
        for (f, p) in [(1, 3), (2, 2), (0, 0)] {
            let s = run(&started(Mode::Patch), tests(1, f, p)).unwrap();
            let s = run(&s, Command::Submit { binary: h(1) }).unwrap();
            assert_eq!(s.reward_milli, 0);
        }
    }

    #[test]
    fn a_report_about_another_binary_pays_nothing() {
        let s = run(&started(Mode::Patch), tests(1, 2, 3)).unwrap();
        let s = run(&s, Command::Submit { binary: h(2) }).unwrap();
        assert_eq!(s.reward_milli, 0);
    }

    #[test]
    fn the_bonus_needs_the_modes_proof() {
        for (mode, kind) in [
            (Mode::Patch, ProofKind::Refines),
            (Mode::Scratch, ProofKind::Verified),
        ] {
            let s = run(&started(mode), tests(1, 2, 3)).unwrap();
            let good = run(
                &run(&s, proof(1, kind, true)).unwrap(),
                Command::Submit { binary: h(1) },
            )
            .unwrap();
            assert_eq!(good.reward_milli, FULL_MILLI + BONUS_MILLI);
            let other = if kind == ProofKind::Refines {
                ProofKind::Verified
            } else {
                ProofKind::Refines
            };
            for c in [
                proof(1, other, true),
                proof(1, kind, false),
                proof(2, kind, true),
            ] {
                let r = run(&run(&s, c).unwrap(), Command::Submit { binary: h(1) }).unwrap();
                assert_eq!(r.reward_milli, FULL_MILLI);
            }
        }
    }

    #[test]
    fn no_bonus_without_the_tests() {
        let s = run(&started(Mode::Patch), proof(1, ProofKind::Refines, true)).unwrap();
        let s = run(&s, Command::Submit { binary: h(1) }).unwrap();
        assert_eq!(s.reward_milli, 0);
    }

    #[test]
    fn done_is_final() {
        let s = run(&started(Mode::Scratch), Command::Submit { binary: h(1) }).unwrap();
        assert!(s.done);
        for c in [
            tests(1, 2, 3),
            proof(1, ProofKind::Verified, true),
            Command::Submit { binary: h(1) },
        ] {
            assert_eq!(run(&s, c), Err(Error::Done));
        }
    }

    #[test]
    fn reports_need_a_started_episode_and_sane_counts() {
        assert_eq!(run(&initial(), tests(1, 0, 0)), Err(Error::NotStarted));
        assert_eq!(
            run(&started(Mode::Patch), tests(1, 3, 0)),
            Err(Error::InvalidReport)
        );
        let bad = Task {
            id: 1,
            mode: Mode::Patch,
            f2p: 0,
            p2p: 0,
        };
        assert_eq!(
            run(&initial(), Command::Reset { task: bad }),
            Err(Error::InvalidTask)
        );
    }
}
