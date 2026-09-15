//! Function discovery, control flow, cross references, and strings.
//!
//! Analysis is parallel and deterministic: each round walks its pending
//! entries across threads, then merges in sorted order, so the answer never
//! depends on which thread finished first.
//!
//! Two ways in. [`Session`] owns a loaded object and computes each part the
//! first time it is asked for, so a caller that wants function names never
//! pays for a string scan; with a [`Cache`] attached it reads those parts back
//! from disk instead of recomputing them. [`analyze`] is the eager shape, a
//! session with every part forced, and is what most of the workspace calls.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod cache;
pub mod cfg;
mod codec;
pub mod data;
pub mod jumptable;
pub mod noreturn;
pub mod program;
pub mod progress;
pub mod session;
pub mod strings;
pub mod xref;

pub use cache::{Cache, ContentHash, Part};
pub use cfg::{Block, Cfg, Halt, Terminator};
pub use data::{DataMap, Proof, Region};
pub use jumptable::{JumpTable, TableKind};
pub use program::{Function, Options, Program, Stats, analyze};
pub use progress::{Sink, Stage, Update};
pub use session::Session;
pub use strings::Found;
pub use xref::{Xref, XrefIndex, XrefKind};
