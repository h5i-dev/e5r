//! Expression rebuilding, structuring and C emission.
//!
//! The output is pseudo-C: it says what the machine does, in C's notation,
//! without claiming to be the source. Where the structure does not fit an `if`
//! or a `while`, a labelled `goto` appears rather than a shape that is not
//! there, and the number of them is reported, because it is the honest measure
//! of how well the structuring worked.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod emit;
pub mod expr;
pub mod structure;

pub use emit::{
    Callee, Output, Param, Prototype, decompile, decompile_full, decompile_in, decompile_with,
    identifier,
};
pub use expr::{Expr, c_type, field_name};
pub use structure::{Case, Region, Structured, Switches};
