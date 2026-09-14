//! The SLEIGH front end: `.slaspec` source text to an in-memory model.
//!
//! Ghidra's processor specifications are the widest published description of
//! instruction encodings there is, and they are data rather than code, which
//! is why r12e loads them directly. This crate is the half that reads them:
//! preprocessor, lexer, parser, and the reduction of each constructor's bit
//! pattern to masks a decoder can compare bytes against. It does not decode
//! instructions and it does not write `.sla` files.
//!
//! ```no_run
//! use std::path::Path;
//! let spec = r12e_sleigh::parse_file(Path::new("x86-64.slaspec")).expect("parses");
//! let root = spec.table(spec.root());
//! println!("{} instruction constructors", root.constructors.len());
//! ```
//!
//! # What a decode engine does with the result
//!
//! [`model::Spec`] owns everything in flat arenas addressed by small index
//! types. Start at [`model::Spec::root`], try each [`model::Constructor`] of
//! that table in order, and test [`model::Constructor::resolved`] against the
//! instruction bytes and the context register image. See [`model`] for the
//! full walk.
//!
//! # Trust
//!
//! A specification is input like any other. Every count is bounded before it
//! is allocated against, `@include` has a depth limit, every loop is checked
//! to advance, and a truncated or corrupted file produces a typed error rather
//! than a panic. The ceilings live in [`error::Limits`] and are all far above
//! what the published corpus needs.

#![deny(missing_docs)]

pub mod context;
pub mod decode;
pub mod error;
pub mod index;
pub mod lex;
pub mod model;
mod parse;
mod pattern;
pub mod pcode;
pub mod preprocess;

use std::path::Path;

pub use context::{Commit, Context, ContextDb};
pub use decode::{DecodeError, DecodeLimits, Decoded, Decoder, Node, ResolvedOperand, Value};
pub use error::{Error, Limits, Location, Result};
pub use index::Index;
pub use model::Spec;
pub use pcode::{Pcode, lift};

/// Parse one specification file and everything it includes.
pub fn parse_file(path: &Path) -> Result<Spec> {
    let mut loader = preprocess::FileLoader::default();
    parse_with(path, &mut loader, Limits::default(), &[])
}

/// Parse a specification with a caller supplied loader, bounds and
/// preprocessor definitions.
///
/// The definitions are what a `.ldefs` variant or a command line would supply,
/// as `(name, value)` pairs.
pub fn parse_with(
    path: &Path,
    loader: &mut dyn preprocess::Loader,
    limits: Limits,
    defines: &[(&str, &str)],
) -> Result<Spec> {
    let mut pre = preprocess::Preprocessor::new(loader).with_limits(limits.clone());
    for (name, value) in defines {
        pre = pre.define(*name, *value);
    }
    let source = pre.run(path)?;
    parse_source(&source, limits)
}

/// Parse already preprocessed text.
pub fn parse_source(source: &preprocess::Source, limits: Limits) -> Result<Spec> {
    parse::parse(source, limits)
}

/// Parse a specification given as a single string, with no includes.
///
/// Useful for tests and for the small definitions a caller embeds.
pub fn parse_str(text: &str) -> Result<Spec> {
    let mut loader = preprocess::MemoryLoader::new().with("<input>", text);
    parse_with(Path::new("<input>"), &mut loader, Limits::default(), &[])
}
