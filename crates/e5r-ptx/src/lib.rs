//! A strict parser for a small integer subset of NVIDIA PTX, and its export
//! to the Lean model in `verification/ptx` (docs/verification-ptx.md).
//!
//! The parser is not trusted by the proofs. What makes its output usable as
//! a proof subject is [`roundtrip`]: the canonical printing of the parsed
//! module must have exactly the tokens of the original file (comments and
//! whitespace aside), and must parse back to the same module. A parser bug
//! that changes meaning therefore has to be matched by a printer bug that
//! changes it back, and the printer is a short table that reads like PTX.
//! The Lean emitter is a second such table, one line per constructor.
//!
//! Anything outside the subset is refused with the line it is on.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod ast;
pub mod fp;
pub mod interp;
pub mod lean;
pub mod lex;
pub mod parse;
pub mod print;

pub use ast::Module;
pub use parse::parse_module;

/// Parse `src` and check that the canonical printing has the same tokens and
/// re-parses to the same module. Returns the module.
pub fn roundtrip(src: &str) -> Result<Module, String> {
    let m = parse_module(src)?;
    let printed = print::module(&m);
    let a = lex::lex(src)?;
    let b = lex::lex(&printed)?;
    let (a, b): (Vec<_>, Vec<_>) = (
        a.into_iter().map(|t| t.tok).collect(),
        b.into_iter().map(|t| t.tok).collect(),
    );
    if let Some(i) = (0..a.len().max(b.len())).find(|&i| a.get(i) != b.get(i)) {
        return Err(format!(
            "round trip: token {i} differs: source {:?}, printed {:?}",
            a.get(i),
            b.get(i)
        ));
    }
    let again = parse_module(&printed).map_err(|e| format!("round trip: printed text: {e}"))?;
    if again != m {
        return Err("round trip: printed text parses to a different module".into());
    }
    Ok(m)
}

/// Round-trip `src` and render it as a Lean module in namespace `ns`.
pub fn export_lean(src: &str, ns: &str, header: &str) -> Result<String, String> {
    let m = roundtrip(src)?;
    Ok(lean::module(&m, ns, header))
}
