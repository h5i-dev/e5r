//! A deadline and a count, so a long job gives back what it finished.
//!
//! The case this exists for: an agent asks to decompile a 40,000 function
//! binary. Running to completion may take minutes, and the caller has no way
//! to say "enough". Returning nothing after two minutes is the worst of the
//! options, because the work was done and then thrown away.
//!
//! So a job that exceeds its budget stops, returns what it finished, and says
//! why and how much is missing. That is a partial answer that says it is
//! partial, which a caller can act on; a truncated answer that looks complete
//! is not.

use std::time::{Duration, Instant};

/// Why a job stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stopped {
    /// Everything asked for was done.
    Finished,
    /// The time limit was reached.
    OutOfTime,
    /// The item limit was reached.
    OutOfItems,
}

impl Stopped {
    /// True when nothing was left undone.
    pub fn complete(self) -> bool {
        self == Stopped::Finished
    }

    /// The word that goes in a JSON document.
    pub fn as_str(self) -> &'static str {
        match self {
            Stopped::Finished => "finished",
            Stopped::OutOfTime => "out of time",
            Stopped::OutOfItems => "out of items",
        }
    }
}

/// What a job is allowed to spend.
#[derive(Debug, Clone, Copy, Default)]
pub struct Budget {
    /// Wall clock, or `None` for no limit.
    limit: Option<Duration>,
    /// Items, or `None` for no limit.
    items: Option<usize>,
    /// When the budget started.
    started: Option<Instant>,
    /// How many items have been taken.
    taken: usize,
}

impl Budget {
    /// A budget from the command line's two options.
    ///
    /// The clock starts here rather than at the first item, so the time spent
    /// loading and analyzing counts against it: a caller who said "two
    /// seconds" meant two seconds, not two seconds of the last phase.
    pub fn new(seconds: Option<f64>, items: Option<usize>) -> Budget {
        Budget {
            limit: seconds.map(Duration::from_secs_f64),
            items,
            started: Some(Instant::now()),
            taken: 0,
        }
    }

    /// True when nothing is limited, so a caller can skip the bookkeeping.
    pub fn unlimited(&self) -> bool {
        self.limit.is_none() && self.items.is_none()
    }

    /// Take one item, or report why it cannot be taken.
    ///
    /// Checked before the work rather than after, so the budget bounds what is
    /// started and not merely what is finished.
    pub fn take(&mut self) -> Stopped {
        if self.items.is_some_and(|n| self.taken >= n) {
            return Stopped::OutOfItems;
        }
        if let (Some(limit), Some(started)) = (self.limit, self.started)
            && started.elapsed() >= limit
        {
            return Stopped::OutOfTime;
        }
        self.taken += 1;
        Stopped::Finished
    }

    /// How long the budget has been running.
    pub fn elapsed(&self) -> Duration {
        self.started.map(|s| s.elapsed()).unwrap_or_default()
    }
}

/// Say on stderr that a job stopped early, and how much is missing.
///
/// stderr rather than the output, so a partial document is still a valid
/// document and the reason is still visible when the output is redirected.
pub fn report(b: &Budget, why: Stopped, done: usize, total: usize, what: &str) {
    if why.complete() {
        return;
    }
    eprintln!(
        "e5r: {} after {:.1}s and {done} of {total} {what}; {} not done. \
         Raise --budget or --limit, or narrow the target.",
        why.as_str(),
        b.elapsed().as_secs_f64(),
        total.saturating_sub(done)
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unlimited_budget_never_stops() {
        let mut b = Budget::new(None, None);
        assert!(b.unlimited());
        for _ in 0..10_000 {
            assert_eq!(b.take(), Stopped::Finished);
        }
    }

    #[test]
    fn an_item_budget_stops_at_its_count() {
        let mut b = Budget::new(None, Some(3));
        assert_eq!(b.take(), Stopped::Finished);
        assert_eq!(b.take(), Stopped::Finished);
        assert_eq!(b.take(), Stopped::Finished);
        assert_eq!(b.take(), Stopped::OutOfItems);
        // Still refused on a later call: a budget does not recover.
        assert_eq!(b.take(), Stopped::OutOfItems);
    }

    #[test]
    fn a_zero_item_budget_does_nothing_rather_than_one_thing() {
        let mut b = Budget::new(None, Some(0));
        assert_eq!(b.take(), Stopped::OutOfItems);
    }

    #[test]
    fn a_time_budget_stops_once_it_is_spent() {
        let mut b = Budget::new(Some(0.0), None);
        assert_eq!(b.take(), Stopped::OutOfTime);
    }

    #[test]
    fn the_item_limit_is_checked_before_the_clock() {
        // Both exhausted: the item count is the more useful thing to report,
        // because it is the one the caller can reason about.
        let mut b = Budget::new(Some(0.0), Some(0));
        assert_eq!(b.take(), Stopped::OutOfItems);
    }
}
