//! Errors and resource caps.
//!
//! Parsing never panics. Variants carry enough to find the problem in a hex
//! editor: "invalid ELF" is useless, an offset and a length are a bug report.

use std::fmt;

use crate::addr::Addr;

/// The workspace result type.
pub type Result<T> = std::result::Result<T, Error>;

/// What went wrong.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// A read ran past the end of the buffer.
    OutOfBounds {
        /// What the caller was trying to read.
        what: &'static str,
        /// Byte offset the read started at.
        offset: u64,
        /// How many bytes were wanted.
        len: u64,
        /// How many bytes there are.
        available: u64,
    },
    /// A field held a value the format does not allow.
    BadField {
        /// Which field, named as the specification names it.
        field: &'static str,
        /// What it held.
        value: u64,
        /// Why that is not acceptable.
        reason: &'static str,
    },
    /// The file is not in a format this loader recognizes.
    NotRecognized {
        /// What was expected, for the error message.
        expected: &'static str,
    },
    /// The format is recognized but this build cannot handle this variant.
    Unsupported {
        /// The feature that is missing.
        what: String,
    },
    /// An address has no bytes behind it in the memory map.
    Unmapped {
        /// The address that was not mapped.
        addr: Addr,
    },
    /// A count exceeded a cap. The cap is in the error so it can be raised.
    CapExceeded {
        /// What was being counted.
        what: &'static str,
        /// The count the file asked for.
        requested: u64,
        /// The limit in force.
        limit: u64,
    },
    /// Two facts that must agree do not.
    Inconsistent {
        /// A description of the disagreement.
        detail: String,
    },
    /// Something failed underneath, most often the filesystem.
    Io {
        /// What the operation was.
        what: String,
        /// The OS error message.
        detail: String,
    },
}

impl Error {
    /// Build an [`Error::Unsupported`] without the caller writing `.to_string()`.
    pub fn unsupported(what: impl Into<String>) -> Error {
        Error::Unsupported { what: what.into() }
    }

    /// Build an [`Error::Inconsistent`].
    pub fn inconsistent(detail: impl Into<String>) -> Error {
        Error::Inconsistent {
            detail: detail.into(),
        }
    }

    /// True for "not my format", the one error a format probe expects.
    pub fn is_not_recognized(&self) -> bool {
        matches!(self, Error::NotRecognized { .. })
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::OutOfBounds {
                what,
                offset,
                len,
                available,
            } => write!(
                f,
                "{what}: read of {len:#x} bytes at offset {offset:#x} runs past the end \
                 ({available:#x} bytes available)"
            ),
            Error::BadField {
                field,
                value,
                reason,
            } => write!(f, "{field} is {value:#x}, which {reason}"),
            Error::NotRecognized { expected } => write!(f, "not a {expected}"),
            Error::Unsupported { what } => write!(f, "unsupported: {what}"),
            Error::Unmapped { addr } => write!(f, "address {addr} is not mapped"),
            Error::CapExceeded {
                what,
                requested,
                limit,
            } => write!(
                f,
                "{what}: file asks for {requested}, limit is {limit}. Raise it if the file \
                 is genuinely this large."
            ),
            Error::Inconsistent { detail } => write!(f, "inconsistent: {detail}"),
            Error::Io { what, detail } => write!(f, "{what}: {detail}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io {
            what: "io".to_string(),
            detail: e.to_string(),
        }
    }
}

/// Caps on counts the input file controls. A file claiming 4 billion sections
/// must not allocate until the process dies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Caps {
    /// Sections or segments in one container.
    pub sections: u64,
    /// Symbols in one table.
    pub symbols: u64,
    /// Relocations in one table.
    pub relocations: u64,
    /// Bytes in one string, before it is treated as unterminated.
    pub string_len: u64,
    /// Instructions decoded in one function before analysis gives up.
    pub function_insns: u64,
    /// Basic blocks in one function.
    pub function_blocks: u64,
    /// Entries in one recovered jump table.
    pub jump_table_entries: u64,
}

impl Default for Caps {
    fn default() -> Self {
        Caps {
            sections: 1 << 16,
            symbols: 1 << 24,
            relocations: 1 << 24,
            string_len: 1 << 16,
            function_insns: 1 << 20,
            function_blocks: 1 << 18,
            jump_table_entries: 1 << 16,
        }
    }
}

impl Caps {
    /// Check a count against a cap, naming both in the error.
    pub fn check(&self, what: &'static str, requested: u64, limit: u64) -> Result<()> {
        if requested > limit {
            Err(Error::CapExceeded {
                what,
                requested,
                limit,
            })
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn messages_locate_the_problem() {
        let e = Error::OutOfBounds {
            what: "section header 12",
            offset: 0x2a40,
            len: 0x8000_0000,
            available: 0x14c0,
        };
        let s = e.to_string();
        assert!(s.contains("0x2a40"), "{s}");
        assert!(s.contains("0x80000000"), "{s}");
        assert!(s.contains("0x14c0"), "{s}");
    }

    #[test]
    fn not_recognized_is_distinguishable() {
        assert!(Error::NotRecognized { expected: "ELF" }.is_not_recognized());
        assert!(!Error::unsupported("PE32+ on ia64").is_not_recognized());
    }

    #[test]
    fn cap_errors_name_the_limit() {
        let caps = Caps::default();
        let e = caps.check("sections", 1 << 20, caps.sections).unwrap_err();
        assert!(e.to_string().contains("65536"), "{e}");
        assert!(caps.check("sections", 10, caps.sections).is_ok());
    }
}
