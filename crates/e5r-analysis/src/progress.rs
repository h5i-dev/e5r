//! Telling a caller what analysis is doing while it does it.
//!
//! `analyze()` is the longest thing the CLI runs and until now it was opaque:
//! `--progress` could count the loops the CLI itself drove and nothing inside.
//! A caller hands in one closure and gets told which stage is running and how
//! far through it is.
//!
//! Three properties, because a progress meter that changes the thing it
//! measures is worse than none:
//!
//! * **Nothing costs nothing.** The sink is a nullable borrowed function
//!   pointer. With no callback attached, every report site is one null check
//!   at a batch boundary, and there is no batch boundary in an inner loop.
//! * **No allocation per report.** [`Update`] is `Copy` and its only text is a
//!   `&'static str`. Whether the callback allocates is the callback's
//!   business.
//! * **No locking on a hot path.** Reports are made from the sequential merge
//!   between parallel batches, never from inside one, so the callback is
//!   called from one thread at a time and nothing in analysis contends for it.
//!   That is also why the granularity is a batch of functions rather than a
//!   function: a report per function would put a call from every thread at
//!   once on the hottest loop in the crate.
//!
//! What a stage cannot say, it does not say. Discovery's rounds queue what
//! they find, so the total for a round is known and the total for the whole
//! stage is not; [`Update::total`] is `None` there rather than a guess that
//! moves backwards.
//!
//! Stages are not strictly one after another either. [`Stage::Data`] runs once
//! in the middle of discovery, because the gap scan needs to know what is data
//! before it sweeps, and again afterwards for the published map. A caller that
//! draws one bar per stage should expect to come back to a stage it has
//! already seen rather than assume the order is a sequence.

/// Which stage of analysis is running.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Stage {
    /// Walking functions and following what they call, in rounds.
    Discovery,
    /// Re-walking the callers of functions that turned out never to return.
    NoReturn,
    /// Proving which regions hold data.
    Data,
    /// Collecting cross references.
    Xrefs,
    /// Scanning for strings.
    Strings,
}

impl Stage {
    /// A name to print. Static, so reporting one allocates nothing.
    pub fn label(self) -> &'static str {
        match self {
            Stage::Discovery => "discovery",
            Stage::NoReturn => "no-return re-walk",
            Stage::Data => "data regions",
            Stage::Xrefs => "cross references",
            Stage::Strings => "strings",
        }
    }
}

/// One report from inside analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Update {
    /// The stage this came from.
    pub stage: Stage,
    /// Which pass, for a stage that runs more than one. Discovery counts its
    /// rounds here; every other stage reports 1.
    pub round: u32,
    /// Units finished in this pass.
    pub done: u64,
    /// Units this pass expects, when the stage knows. `None` means the total
    /// is genuinely not known yet, which is the honest answer for discovery
    /// across rounds.
    pub total: Option<u64>,
}

impl Update {
    /// How far through this pass is, from 0.0 to 1.0, when the total is known.
    pub fn fraction(&self) -> Option<f64> {
        match self.total {
            Some(0) => Some(1.0),
            Some(n) => Some((self.done as f64 / n as f64).clamp(0.0, 1.0)),
            None => None,
        }
    }
}

/// Where progress reports go, or nowhere.
///
/// Borrowed rather than owned and `Copy`, so it can be handed down into the
/// stage functions and captured by a closure that runs on the thread pool
/// without a reference count or a clone.
#[derive(Clone, Copy, Default)]
pub struct Sink<'a> {
    to: Option<&'a (dyn Fn(Update) + Send + Sync)>,
}

impl std::fmt::Debug for Sink<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sink")
            .field("attached", &self.to.is_some())
            .finish()
    }
}

impl<'a> Sink<'a> {
    /// A sink that reports nowhere.
    pub fn none() -> Sink<'a> {
        Sink { to: None }
    }

    /// A sink that calls `f`.
    pub fn new(f: &'a (dyn Fn(Update) + Send + Sync)) -> Sink<'a> {
        Sink { to: Some(f) }
    }

    /// True when someone is listening, so a caller can skip work that only
    /// exists to be reported.
    pub fn is_attached(&self) -> bool {
        self.to.is_some()
    }

    /// Report one step. The whole cost with nothing attached is this branch.
    pub fn report(&self, stage: Stage, round: u32, done: u64, total: Option<u64>) {
        if let Some(f) = self.to {
            f(Update {
                stage,
                round,
                done,
                total,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    #[test]
    fn a_sink_with_nothing_attached_reports_nothing() {
        let s = Sink::none();
        assert!(!s.is_attached());
        s.report(Stage::Discovery, 1, 0, None);
    }

    #[test]
    fn every_report_reaches_the_callback_once() {
        let seen: Mutex<Vec<Update>> = Mutex::new(Vec::new());
        let f = |u: Update| seen.lock().unwrap().push(u);
        let s = Sink::new(&f);
        s.report(Stage::Xrefs, 1, 3, Some(10));
        s.report(Stage::Strings, 1, 2, None);
        let got = seen.into_inner().unwrap();
        assert_eq!(got.len(), 2);
        assert_eq!(got[0].fraction(), Some(0.3));
        assert_eq!(got[1].fraction(), None);
        assert_eq!(got[0].stage.label(), "cross references");
    }

    #[test]
    fn a_pass_with_no_work_is_finished_rather_than_undefined() {
        let u = Update {
            stage: Stage::NoReturn,
            round: 1,
            done: 0,
            total: Some(0),
        };
        assert_eq!(u.fraction(), Some(1.0));
    }
}
