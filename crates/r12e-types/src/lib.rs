//! Demangling, and eventually the type model.
//!
//! A demangled name is the single most visible quality difference in a listing
//! of a C++ or Rust binary, and it costs nothing at analysis time. A name that
//! cannot be demangled is returned unchanged: a wrong name is worse than a
//! mangled one.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod itanium;
pub mod msvc;
pub mod rust;

/// Which scheme a name is mangled in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scheme {
    /// GCC and Clang, the Itanium C++ ABI.
    Itanium,
    /// Rust's v0 scheme.
    RustV0,
    /// Rust's legacy scheme, which is Itanium with a hash suffix.
    RustLegacy,
    /// Microsoft C++.
    Msvc,
}

/// Demangle a name, trying each scheme by its prefix.
///
/// Returns `None` when the name is not mangled or cannot be read, so a caller
/// can keep showing what the file actually says.
pub fn demangle(name: &str) -> Option<(Scheme, String)> {
    if name.starts_with("_R") {
        return rust::demangle_v0(name).map(|s| (Scheme::RustV0, s));
    }
    if name.starts_with('?') {
        return msvc::demangle(name).map(|s| (Scheme::Msvc, s));
    }
    if name.starts_with("_Z") || name.starts_with("__Z") {
        // Rust's legacy scheme is Itanium with a hash on the end.
        if let Some(s) = rust::demangle_legacy(name) {
            return Some((Scheme::RustLegacy, s));
        }
        return itanium::demangle(name).map(|s| (Scheme::Itanium, s));
    }
    None
}

/// Demangle if possible, otherwise hand back the original.
pub fn pretty(name: &str) -> String {
    demangle(name)
        .map(|(_, s)| s)
        .unwrap_or_else(|| name.to_string())
}
