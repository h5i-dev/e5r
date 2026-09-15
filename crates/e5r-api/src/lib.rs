//! The library surface the command line and the servers share.
//!
//! Everything a caller needs to go from a loaded program to an answer, without
//! reaching into the crate that happens to implement it. The point is that the
//! CLI and the tests take the same path: a difference between
//! what a test checks and what a user gets is a difference that will be found
//! by a user.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod classes;
pub mod dataflow;
pub mod decompile;
pub mod emulate;
pub mod kernel;
mod msvc;
pub mod prototypes;
pub mod query;
pub mod relocate;
pub mod shapes;
pub mod signatures;
pub mod vtables;

pub use classes::{
    Abi, BaseClass, Class, Classes, Member, Role, Rtti, This, TypeInfoKind, classes, classes_with,
};
pub use dataflow::{ArgumentFact, Basis, CallSite, Source, Verdict, call_sites, call_sites_in};
pub use decompile::{
    Decompiled, Unit, decompile_function, decompile_function_with, decompile_program,
    decompile_program_with,
};
pub use emulate::{
    Confirmed, Ending, Indirect, Place, Region, Resolved, Run, Setup, Span, confirm, resolve,
};
pub use kernel::{Call, Kernel, Output};
pub use prototypes::{Recovered, prototypes};
pub use query::{Answer, Entity, Fact, Query, Row, Want};
pub use relocate::apply_relative_relocations;
pub use shapes::{Pointer, shapes_of};
pub use signatures::{Identified, anchor_of, collect_signatures, identify};
pub use vtables::{VTable, vtables};
