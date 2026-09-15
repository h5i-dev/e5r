//! Addresses, memory maps, provenance, and the hostile-input reader.
//!
//! The bottom of the workspace: depends on nothing, everything depends on it.
//!
//! - [`Reader`] is the only way a loader gets bytes out of a file, and [`Caps`]
//!   bounds anything the file gets to count.
//! - [`Addr`] has no `Add`: real files contain headers that wrap.
//! - [`Provenance`] travels with every recovered fact.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod addr;
pub mod arch;
pub mod error;
pub mod memory;
pub mod provenance;
pub mod reader;

pub use addr::{Addr, AddrRange};
pub use arch::{Arch, Bits, Endian};
pub use error::{Caps, Error, Result};
pub use memory::{MemoryMap, Perms, Segment};
pub use provenance::{Evidence, Provenance, Strength};
pub use reader::Reader;
