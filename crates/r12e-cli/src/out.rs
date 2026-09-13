//! Buffered output that survives a closed pipe.
//!
//! `println!` panics when the reader goes away, which is what happens every
//! time someone pipes a listing into `head`. Writing through a buffer and
//! dropping a broken-pipe error turns that into the normal end of a command.
//! Buffering also matters on its own: a libc listing is 400,000 lines.

use std::io::{BufWriter, Stdout, Write};

/// Where the output goes.
enum Sink {
    /// Standard output, which is the usual case.
    Stdout(BufWriter<Stdout>),
    /// A string, for a command that runs another command and keeps what it
    /// printed rather than letting it out.
    Buffer(String),
}

/// The output stream.
pub struct Out {
    w: Sink,
    /// Set once the reader has gone away; every later write is skipped.
    closed: bool,
}

impl Out {
    /// A 64 KiB buffered writer over stdout.
    pub fn new() -> Out {
        Out {
            w: Sink::Stdout(BufWriter::with_capacity(64 * 1024, std::io::stdout())),
            closed: false,
        }
    }

    /// A stream that collects what is written instead of printing it.
    pub fn buffer() -> Out {
        Out {
            w: Sink::Buffer(String::new()),
            closed: false,
        }
    }

    /// Write one line.
    pub fn line(&mut self, args: std::fmt::Arguments<'_>) {
        if self.closed {
            return;
        }
        match &mut self.w {
            Sink::Stdout(w) => {
                if w.write_fmt(args).is_err() || w.write_all(b"\n").is_err() {
                    self.closed = true;
                }
            }
            Sink::Buffer(s) => {
                let _ = std::fmt::Write::write_fmt(s, args);
                s.push('\n');
            }
        }
    }

    /// What was collected, for a buffered stream.
    pub fn take(self) -> String {
        match self.w {
            Sink::Buffer(s) => s,
            Sink::Stdout(_) => String::new(),
        }
    }

    /// Flush, reporting whether the reader was still there.
    pub fn finish(mut self) -> bool {
        match &mut self.w {
            Sink::Stdout(w) => !self.closed && w.flush().is_ok(),
            Sink::Buffer(_) => !self.closed,
        }
    }
}

/// `println!` for [`Out`].
macro_rules! outln {
    ($o:expr) => { $o.line(format_args!("")) };
    ($o:expr, $($t:tt)*) => { $o.line(format_args!($($t)*)) };
}

pub(crate) use outln;
