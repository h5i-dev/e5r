//! Progress on stderr, for the jobs that are not instant.
//!
//! stderr rather than stdout, so a progress line never lands in a document
//! somebody is parsing, and only when stderr is a terminal, so a log file or a
//! pipe gets nothing. That is the whole interface contract: the output of a
//! command is exactly what it was without this file.
//!
//! The estimate is from the rate so far, which is right when the work per item
//! is even and wrong when it is not. It is printed as a time rather than a
//! percentage for that reason: a reader treats "12s left" as the guess it is.

use std::io::{IsTerminal, Write};
use std::time::{Duration, Instant};

/// How often to redraw. Fast enough to look live, slow enough that the
/// terminal is not the bottleneck on a 40,000 item job.
const TICK: Duration = Duration::from_millis(100);

/// A counter that draws itself on stderr.
pub struct Progress {
    what: &'static str,
    total: usize,
    done: usize,
    started: Instant,
    last_drawn: Instant,
    /// False when stderr is not a terminal, in which case nothing is drawn.
    live: bool,
    /// Set once something has been drawn, so the line is only cleared if it
    /// was ever written.
    drawn: bool,
}

impl Progress {
    /// A counter over a known number of items.
    ///
    /// Silent when stderr is not a terminal, when the caller asked for JSON,
    /// or when the job is small enough that a person would not wait for it.
    pub fn new(what: &'static str, total: usize, wanted: bool) -> Progress {
        let live = wanted && total > 64 && std::io::stderr().is_terminal();
        Progress {
            what,
            total,
            done: 0,
            started: Instant::now(),
            // Back-dated so the first item draws immediately: a job that
            // starts with a slow item should say so before it begins it.
            last_drawn: Instant::now() - TICK,
            live,
            drawn: false,
        }
    }

    /// Count one item and redraw if it is time.
    pub fn step(&mut self) {
        self.done += 1;
        if !self.live || self.last_drawn.elapsed() < TICK {
            return;
        }
        self.last_drawn = Instant::now();
        self.draw();
    }

    fn draw(&mut self) {
        let elapsed = self.started.elapsed().as_secs_f64();
        let left = if self.done > 0 && elapsed > 0.2 {
            let per = elapsed / self.done as f64;
            let remaining = self.total.saturating_sub(self.done) as f64 * per;
            format!(", about {}s left", remaining.round() as u64)
        } else {
            String::new()
        };
        let mut e = std::io::stderr();
        // Carriage return and clear to end of line, so the line is rewritten
        // in place rather than scrolling the terminal.
        let _ = write!(
            e,
            "\r\x1b[K{} {} of {}{left}",
            self.what, self.done, self.total
        );
        let _ = e.flush();
        self.drawn = true;
    }

    /// Erase the line, so whatever prints next starts clean.
    pub fn finish(mut self) {
        if self.drawn {
            let mut e = std::io::stderr();
            let _ = write!(e, "\r\x1b[K");
            let _ = e.flush();
            self.drawn = false;
        }
    }
}

impl Drop for Progress {
    /// A job that returns early still clears its line.
    fn drop(&mut self) {
        if self.drawn {
            let mut e = std::io::stderr();
            let _ = write!(e, "\r\x1b[K");
            let _ = e.flush();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nothing_is_drawn_when_it_was_not_asked_for() {
        let mut p = Progress::new("functions", 1000, false);
        for _ in 0..1000 {
            p.step();
        }
        assert!(!p.drawn);
        assert_eq!(p.done, 1000);
    }

    #[test]
    fn a_small_job_is_never_live() {
        // Under the threshold, so it stays silent even on a terminal.
        let p = Progress::new("functions", 10, true);
        assert!(!p.live);
    }

    #[test]
    fn counting_is_independent_of_drawing() {
        let mut p = Progress::new("functions", 100, false);
        p.step();
        p.step();
        assert_eq!(p.done, 2);
    }
}
