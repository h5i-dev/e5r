//! Function discovery, control flow, cross references, and strings.
//!
//! Analysis is parallel and deterministic: each round walks its pending
//! entries across threads, then merges in sorted order, so the answer never
//! depends on which thread finished first.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod cfg;
pub mod jumptable;
pub mod noreturn;
pub mod program;
pub mod strings;
pub mod xref;

pub use cfg::{Block, Cfg, Halt, Terminator};
pub use jumptable::{JumpTable, TableKind};
pub use program::{Function, Options, Program, Stats, analyze};
pub use strings::Found;
pub use xref::{Xref, XrefIndex, XrefKind};
