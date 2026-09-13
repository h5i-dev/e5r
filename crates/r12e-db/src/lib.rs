//! Content anchors and the git-mergeable annotation log.
//!
//! What an analyst writes down is the only knowledge in a program that cannot
//! be recomputed, so it is the only thing worth storing. Boundaries, blocks and
//! cross references stay out of the file: regenerating them can never conflict
//! because they are not there to conflict.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod anchor;
pub mod log;
pub mod patch;
pub mod project;
pub mod signature;

pub use anchor::{Anchor, AnchorIndex, Fnv, Resolution};
pub use log::{Assertion, Field, Log};
