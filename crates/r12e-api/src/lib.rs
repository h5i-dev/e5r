//! The library surface the command line and the servers share.
//!
//! Everything a caller needs to go from a loaded program to an answer, without
//! reaching into the crate that happens to implement it. The point is that the
//! CLI, the MCP server and the tests take the same path: a difference between
//! what a test checks and what a user gets is a difference that will be found
//! by a user.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod decompile;

pub use decompile::{Decompiled, Unit, decompile_function, decompile_program};
