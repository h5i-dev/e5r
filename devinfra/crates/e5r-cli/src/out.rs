//! Buffered output that survives a closed pipe, pages when a person is
//! reading, and stays byte-identical when something else is.
//!
//! `println!` panics when the reader goes away, which is what happens every
//! time someone pipes a listing into `head`. Writing through a buffer and
//! dropping a broken-pipe error turns that into the normal end of a command.
//! Buffering also matters on its own: a libc listing is 400,000 lines.
//!
//! Colour and paging are decided once, from whether standard output is a
//! terminal. Piped output has no escape sequences and no truncation, so a
//! listing diffs against the same listing taken a week ago.

use std::io::{BufWriter, IsTerminal, Stdout, Write};
use std::process::{Child, ChildStdin, Command, Stdio};

/// When to colour.
#[derive(Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum)]
pub enum When {
    /// Colour a terminal, and nothing else.
    #[default]
    Auto,
    /// Colour even when redirected, for a consumer that renders it.
    Always,
    /// Never.
    Never,
}

/// Where the output goes.
enum Sink {
    /// Standard output, which is the usual case.
    Stdout(BufWriter<Stdout>),
    /// A pager, which owns the terminal until the reader quits.
    Pager {
        child: Child,
        w: BufWriter<ChildStdin>,
    },
    /// A string, for a command that runs another command and keeps what it
    /// printed rather than letting it out.
    Buffer(String),
}

/// The output stream.
pub struct Out {
    w: Sink,
    /// Set once the reader has gone away; every later write is skipped.
    closed: bool,
    /// Whether to emit escape sequences.
    colour: bool,
    /// Terminal width, or `None` when the output is not a terminal, in which
    /// case nothing is ever truncated.
    width: Option<usize>,
}

impl Out {
    /// A 64 KiB buffered writer over stdout.
    pub fn new() -> Out {
        Out {
            w: Sink::Stdout(BufWriter::with_capacity(64 * 1024, std::io::stdout())),
            closed: false,
            colour: false,
            width: None,
        }
    }

    /// A stream that collects what is written instead of printing it.
    pub fn buffer() -> Out {
        Out {
            w: Sink::Buffer(String::new()),
            closed: false,
            colour: false,
            width: None,
        }
    }

    /// Decide colour and width, and page if a person is reading.
    ///
    /// `NO_COLOR` is honoured because it is the convention every other tool
    /// follows, and a user who set it meant it.
    pub fn attach_terminal(&mut self, when: When, paged: bool) {
        let tty = std::io::stdout().is_terminal();
        self.colour = match when {
            When::Always => true,
            When::Never => false,
            When::Auto => tty && std::env::var_os("NO_COLOR").is_none(),
        };
        if !tty {
            return;
        }
        self.width = terminal_width();
        if paged && matches!(self.w, Sink::Stdout(_)) {
            if let Some((child, stdin)) = pager() {
                self.w = Sink::Pager {
                    child,
                    w: BufWriter::with_capacity(64 * 1024, stdin),
                };
            }
        }
    }

    /// True when escape sequences are wanted.
    pub fn colour(&self) -> bool {
        self.colour
    }

    /// The width to fit a listing into, when there is one.
    pub fn width(&self) -> Option<usize> {
        self.width
    }

    /// Wrap text in a colour, or return it unchanged.
    pub fn paint(&self, role: Role, text: &str) -> String {
        if !self.colour {
            return text.to_string();
        }
        format!("\x1b[{}m{text}\x1b[0m", role.code())
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
            Sink::Pager { w, .. } => {
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
            _ => String::new(),
        }
    }

    /// Flush, reporting whether the reader was still there.
    ///
    /// The pager owns the terminal until the reader quits, so this waits for
    /// it: returning first would let the shell prompt print underneath it.
    pub fn finish(mut self) -> bool {
        match &mut self.w {
            Sink::Stdout(w) => !self.closed && w.flush().is_ok(),
            Sink::Buffer(_) => !self.closed,
            Sink::Pager { .. } => {
                let Sink::Pager { mut child, mut w } =
                    std::mem::replace(&mut self.w, Sink::Buffer(String::new()))
                else {
                    unreachable!("just matched")
                };
                let flushed = w.flush().is_ok();
                // Closing the pipe is how the pager learns there is no more
                // input; waiting is how the shell prompt stays below it.
                drop(w);
                let _ = child.wait();
                !self.closed && flushed
            }
        }
    }
}

/// What a piece of text is, which decides its colour.
#[derive(Clone, Copy)]
pub enum Role {
    /// A column header.
    Head,
    /// An address.
    Addr,
    /// A symbol or function name.
    Name,
    /// How strongly something is believed.
    Strong,
    /// Believed, but not proven.
    Weak,
    /// Something the tool could not work out.
    Unknown,
}

impl Role {
    /// The SGR parameters. Bold and the eight original colours only: a
    /// 256-colour palette looks different on every terminal theme, and half of
    /// them are unreadable on a light background.
    fn code(self) -> &'static str {
        match self {
            Role::Head => "1",
            Role::Addr => "36",
            Role::Name => "32",
            Role::Strong => "32",
            Role::Weak => "33",
            Role::Unknown => "31",
        }
    }
}

/// The terminal's width.
///
/// `COLUMNS` is not exported to children by most shells, so `stty` is asked
/// directly. It is one process at startup and only when a person is reading.
fn terminal_width() -> Option<usize> {
    if let Some(n) = std::env::var("COLUMNS").ok().and_then(|v| v.parse().ok()) {
        return Some(n);
    }
    let out = Command::new("stty")
        .arg("size")
        .stdin(Stdio::inherit())
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    text.split_whitespace().nth(1)?.parse().ok()
}

/// Start the pager, if there is one to start.
///
/// `less -F` quits immediately when the output fits on one screen, so short
/// listings behave as if there were no pager at all. `-R` keeps the colours
/// and `-X` leaves the text on the screen after it exits.
fn pager() -> Option<(Child, ChildStdin)> {
    let chosen = std::env::var("E5R_PAGER")
        .or_else(|_| std::env::var("PAGER"))
        .unwrap_or_else(|_| "less".to_string());
    if chosen.is_empty() || chosen == "cat" {
        return None;
    }
    let mut parts = chosen.split_whitespace();
    let program = parts.next()?;
    let mut cmd = Command::new(program);
    let args: Vec<&str> = parts.collect();
    if args.is_empty() && program.ends_with("less") {
        cmd.args(["-FRX"]);
    } else {
        cmd.args(args);
    }
    let mut child = cmd.stdin(Stdio::piped()).spawn().ok()?;
    let stdin = child.stdin.take()?;
    Some((child, stdin))
}

/// `println!` for [`Out`].
macro_rules! outln {
    ($o:expr) => { $o.line(format_args!("")) };
    ($o:expr, $($t:tt)*) => { $o.line(format_args!($($t)*)) };
}

pub(crate) use outln;
