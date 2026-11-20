//! Where a failure happened, not just that one did.
//!
//! A specification is assembled out of dozens of `@include`d files, so
//! "unexpected token" with no file and line is not actionable. Every error
//! carries the originating file and line of the *source* text, which is what
//! the author can open, rather than an offset into the preprocessed stream.

use std::fmt;
use std::sync::Arc;

/// A point in an original source file, after include and macro expansion have
/// been unwound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    /// The file the line came from, as it was resolved.
    pub file: Arc<str>,
    /// One-based line number within that file.
    pub line: u32,
}

impl Location {
    /// A location, from a file name and a one-based line.
    pub fn new(file: impl Into<Arc<str>>, line: u32) -> Location {
        Location {
            file: file.into(),
            line,
        }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.file, self.line)
    }
}

/// What went wrong, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// The complaint, in lower case and without a trailing stop.
    pub message: String,
    /// The source position, when one is known.
    pub at: Option<Location>,
}

impl Error {
    /// An error with no position.
    pub fn new(message: impl Into<String>) -> Error {
        Error {
            message: message.into(),
            at: None,
        }
    }

    /// An error at a known position.
    pub fn at(location: Location, message: impl Into<String>) -> Error {
        Error {
            message: message.into(),
            at: Some(location),
        }
    }

    /// The same error with a position attached, if it did not have one.
    pub fn or_at(mut self, location: &Location) -> Error {
        if self.at.is_none() {
            self.at = Some(location.clone());
        }
        self
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.at {
            Some(at) => write!(f, "{at}: {}", self.message),
            None => f.write_str(&self.message),
        }
    }
}

impl std::error::Error for Error {}

/// The crate's result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Ceilings on everything a hostile or merely broken input can grow.
///
/// Each one exists because the corresponding loop or allocation is driven by
/// the input. The defaults are far above what the Ghidra corpus needs, which
/// is the point: they stop runaway, they do not shape the language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Limits {
    /// How deep `@include` may nest.
    pub include_depth: usize,
    /// How many files one specification may pull in, counting repeats.
    pub include_files: usize,
    /// Bytes accepted from a single file.
    pub file_bytes: usize,
    /// Lines the preprocessor may emit in total.
    pub total_lines: usize,
    /// `$(name)` substitutions attempted on one line before giving up.
    pub expansions_per_line: usize,
    /// How deep `@if` may nest.
    pub condition_depth: usize,
    /// How deep any parsed expression may nest.
    pub expr_depth: usize,
    /// How many terms one flat operator chain, `a | b | c | ...`, may have.
    /// A chain costs the parser no stack but leans the tree it builds one
    /// level per term, and the tree is walked and dropped recursively.
    pub expr_chain: usize,
    /// Alternatives a single constructor's pattern may reduce to before the
    /// reduction collapses to an approximation.
    pub pattern_alternatives: usize,
    /// Bytes a single constructor's pattern may span.
    pub pattern_bytes: usize,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits {
            include_depth: 64,
            include_files: 4096,
            file_bytes: 64 << 20,
            total_lines: 8_000_000,
            expansions_per_line: 256,
            condition_depth: 64,
            expr_depth: 128,
            expr_chain: 2048,
            pattern_alternatives: 512,
            pattern_bytes: 256,
        }
    }
}
