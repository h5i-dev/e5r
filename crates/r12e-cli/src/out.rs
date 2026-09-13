//! Buffered output that survives a closed pipe.
//!
//! `println!` panics when the reader goes away, which is what happens every
//! time someone pipes a listing into `head`. Writing through a buffer and
//! dropping a broken-pipe error turns that into the normal end of a command.
//! Buffering also matters on its own: a libc listing is 400,000 lines.

use std::io::{BufWriter, Stdout, Write};

/// The output stream.
pub struct Out {
    w: BufWriter<Stdout>,
    /// Set once the reader has gone away; every later write is skipped.
    closed: bool,
}

impl Out {
    /// A 64 KiB buffered writer over stdout.
    pub fn new() -> Out {
        Out {
            w: BufWriter::with_capacity(64 * 1024, std::io::stdout()),
            closed: false,
        }
    }

    /// Write one line.
    pub fn line(&mut self, args: std::fmt::Arguments<'_>) {
        if self.closed {
            return;
        }
        if self.w.write_fmt(args).is_err() || self.w.write_all(b"\n").is_err() {
            self.closed = true;
        }
    }

    /// Flush, reporting whether the reader was still there.
    pub fn finish(mut self) -> bool {
        !self.closed && self.w.flush().is_ok()
    }
}

/// `println!` for [`Out`].
macro_rules! outln {
    ($o:expr) => { $o.line(format_args!("")) };
    ($o:expr, $($t:tt)*) => { $o.line(format_args!($($t)*)) };
}

pub(crate) use outln;
