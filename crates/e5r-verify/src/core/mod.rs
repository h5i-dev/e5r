//! Backend-independent verification services. Semantics and platform policy live
//! with each backend; this module must not import either backend.
pub mod artifact;
pub mod process;
pub mod proof;
pub mod workspace;
