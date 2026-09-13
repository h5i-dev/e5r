//! The intermediate representation, its lifters, and its interpreter.
//!
//! Lifting turns a decoded machine instruction into a sequence of operations
//! with no implicit effects, so analysis is written once rather than once per
//! architecture.
//!
//! The interpreter ships with the lifters rather than after them. A lifter is a
//! translation between two semantics, and reading one cannot tell you whether
//! it is right; running the original and the translation and comparing can.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod abi;
pub mod exec;
pub mod func;
pub mod interp;
pub mod lift;
pub mod op;
pub mod opt;
pub mod shape;
pub mod ssa;
pub mod stack;

pub use exec::{Outcome, run, run_with};
pub use interp::{Machine, Step, Stop, step};
pub use lift::{Lifted, lift};
pub use op::{IrOp, Op, Space, Varnode};
