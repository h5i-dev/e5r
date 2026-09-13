//! Reader for Ghidra's compiled SLEIGH language files (`.sla`).
//!
//! A `.sla` is the magic `sla`, a one-byte format version, and a zlib stream
//! whose contents are a tagged element tree. None of that is published, so it
//! was worked out the way this toolkit works out any binary format: by
//! compiling `.slaspec` inputs with the shipped SLEIGH compiler, changing one
//! thing at a time, and watching which bytes moved. `docs/sla-format.md` is the
//! write-up, and it separates what was proved that way from what was inferred.
//!
//! The reader has two layers, and both are public on purpose:
//!
//! * [`decode`] turns the payload into a [`Node`] tree of numbered elements,
//!   attributes and values, each node carrying its byte range. Nothing is
//!   interpreted here, so a file using ids this crate has never seen still
//!   reads.
//! * [`model`] turns that tree into spaces, registers, tokens, symbols and
//!   constructors. Anything whose meaning is not established stays in the tree
//!   as raw bytes, and [`Coverage`] reports how many bytes that is, so the gap
//!   is a number rather than a feeling.

#![forbid(unsafe_code)]

pub mod decode;
pub mod ids;
pub mod inflate;
pub mod model;

pub use decode::{DecodeError, Node, Value};
pub use inflate::InflateError;
pub use model::{Coverage, Program, Symbol, SymbolBody};

/// The four magic bytes: `sla` and a format version. Version 4 is what Ghidra
/// 12.1 writes and the only one this reader has seen.
pub const MAGIC: [u8; 3] = *b"sla";

/// The format version this reader was worked out against.
pub const KNOWN_VERSION: u8 = 4;

#[derive(Debug)]
pub enum SlaError {
    /// Shorter than the four-byte header.
    TooShort,
    /// The first three bytes are not `sla`.
    BadMagic([u8; 3]),
    Inflate(InflateError),
    Decode(DecodeError),
    /// The payload's root is not the `sleigh` element.
    NotSleigh {
        root: u32,
    },
    Io(std::io::Error),
}

impl core::fmt::Display for SlaError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::TooShort => f.write_str("file is shorter than the sla header"),
            Self::BadMagic(m) => write!(f, "bad magic {m:?}, expected \"sla\""),
            Self::Inflate(e) => write!(f, "zlib payload: {e}"),
            Self::Decode(e) => write!(f, "element stream: {e}"),
            Self::NotSleigh { root } => write!(f, "root element is {root}, expected 33 (sleigh)"),
            Self::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for SlaError {}

impl From<InflateError> for SlaError {
    fn from(e: InflateError) -> Self {
        Self::Inflate(e)
    }
}

impl From<DecodeError> for SlaError {
    fn from(e: DecodeError) -> Self {
        Self::Decode(e)
    }
}

impl From<std::io::Error> for SlaError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// One loaded `.sla`.
#[derive(Debug, Clone)]
pub struct Sla {
    /// The version byte after the magic.
    pub format_version: u8,
    /// The decompressed payload length, which is what coverage is measured
    /// against.
    pub payload_len: usize,
    /// The whole file as numbered elements, including everything the model
    /// does not interpret.
    pub tree: Node,
    /// The structured view.
    pub program: Program,
    pub coverage: Coverage,
}

impl Sla {
    /// Parse a whole `.sla` file image.
    ///
    /// # Errors
    /// Returns a typed error for a bad header, a payload that does not inflate
    /// or checksum, or an element stream that does not balance. It never
    /// panics and never allocates from a count the file chose.
    pub fn parse(bytes: &[u8]) -> Result<Self, SlaError> {
        Self::parse_with_limit(bytes, inflate::DEFAULT_LIMIT)
    }

    /// As [`Sla::parse`], with an explicit ceiling on the decompressed size.
    ///
    /// # Errors
    /// See [`Sla::parse`].
    pub fn parse_with_limit(bytes: &[u8], limit: usize) -> Result<Self, SlaError> {
        if bytes.len() < 4 {
            return Err(SlaError::TooShort);
        }
        let magic: [u8; 3] = [bytes[0], bytes[1], bytes[2]];
        if magic != MAGIC {
            return Err(SlaError::BadMagic(magic));
        }
        let format_version = bytes[3];
        let payload = inflate::inflate_zlib(&bytes[4..], limit)?;
        let tree = decode::decode(&payload)?;
        if tree.id != ids::el::SLEIGH {
            return Err(SlaError::NotSleigh { root: tree.id });
        }
        let program = model::build(&tree);
        let coverage = Coverage::measure(&tree);
        Ok(Self {
            format_version,
            payload_len: payload.len(),
            tree,
            program,
            coverage,
        })
    }

    /// Read and parse a file.
    ///
    /// # Errors
    /// See [`Sla::parse`], plus any I/O error from reading the path.
    pub fn open(path: impl AsRef<std::path::Path>) -> Result<Self, SlaError> {
        let bytes = std::fs::read(path)?;
        Self::parse(&bytes)
    }

    /// Whether the format version is the one the reader was written against.
    #[must_use]
    pub fn version_is_known(&self) -> bool {
        self.format_version == KNOWN_VERSION
    }
}

/// What a file says about itself that a reader can check against what it
/// found. Anything untrue here means the reader has the format wrong, so it is
/// worth checking rather than trusting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Inconsistency {
    /// The symbol table's count attribute and the bodies found disagree.
    SymbolCount {
        declared: u64,
        found: usize,
    },
    ScopeCount {
        declared: u64,
        found: usize,
    },
    /// A symbol id used by something but never defined.
    MissingSymbol {
        referenced_by: u32,
        id: u32,
    },
    /// A space index used by something but not in the space table.
    MissingSpace {
        index: u32,
    },
    /// Two symbols with the same id.
    DuplicateSymbol {
        id: u32,
    },
    /// A symbol with no header record, so no name.
    UnnamedSymbol {
        id: u32,
    },
    /// A node whose byte range is not inside the payload.
    NodeOutOfRange {
        id: u32,
        start: usize,
        end: usize,
    },
}

impl Sla {
    /// Every self-consistency problem found. An empty result is the claim
    /// that every index in the file resolves and every offset is in range.
    #[must_use]
    pub fn check(&self) -> Vec<Inconsistency> {
        let mut out = Vec::new();
        let p = &self.program;

        if let Some(d) = p.declared_symbols {
            if d != p.symbols.len() as u64 {
                out.push(Inconsistency::SymbolCount {
                    declared: d,
                    found: p.symbols.len(),
                });
            }
        }
        if let Some(d) = p.declared_scopes {
            if d != p.scopes.len() as u64 {
                out.push(Inconsistency::ScopeCount {
                    declared: d,
                    found: p.scopes.len(),
                });
            }
        }

        let mut ids: Vec<u32> = p.symbols.iter().map(|s| s.id).collect();
        ids.sort_unstable();
        for w in ids.windows(2) {
            if w[0] == w[1] {
                out.push(Inconsistency::DuplicateSymbol { id: w[0] });
            }
        }

        // Both lookups run once per reference, and a real language has a few
        // hundred thousand of them, so neither may be a linear scan.
        let has = |id: u32| p.has_symbol(id);
        let mut space_ix: Vec<u32> = p.spaces.iter().map(|s| s.index).collect();
        space_ix.sort_unstable();
        let space_ok = |ix: u32| space_ix.binary_search(&ix).is_ok();

        for s in &p.symbols {
            if s.name.is_none() {
                out.push(Inconsistency::UnnamedSymbol { id: s.id });
            }
            match &s.body {
                SymbolBody::Varnode { space, .. } => {
                    if !space_ok(*space) {
                        out.push(Inconsistency::MissingSpace { index: *space });
                    }
                }
                SymbolBody::Context { varnode, .. } => {
                    if !has(*varnode) {
                        out.push(Inconsistency::MissingSymbol {
                            referenced_by: s.id,
                            id: *varnode,
                        });
                    }
                }
                SymbolBody::VarnodeList { entries, .. } => {
                    for e in entries.iter().flatten() {
                        if !has(*e) {
                            out.push(Inconsistency::MissingSymbol {
                                referenced_by: s.id,
                                id: *e,
                            });
                        }
                    }
                }
                SymbolBody::Operand {
                    sub_symbol: Some(sub),
                    ..
                } => {
                    if !has(*sub) {
                        out.push(Inconsistency::MissingSymbol {
                            referenced_by: s.id,
                            id: *sub,
                        });
                    }
                }
                SymbolBody::Subtable {
                    constructors,
                    decision,
                } => {
                    for c in constructors {
                        if !has(c.parent) {
                            out.push(Inconsistency::MissingSymbol {
                                referenced_by: s.id,
                                id: c.parent,
                            });
                        }
                        for o in &c.operands {
                            if !has(*o) {
                                out.push(Inconsistency::MissingSymbol {
                                    referenced_by: s.id,
                                    id: *o,
                                });
                            }
                        }
                    }
                    if let Some(d) = decision {
                        check_decision(d, constructors.len(), s.id, &mut out);
                    }
                }
                _ => {}
            }
        }

        let len = self.payload_len;
        self.tree.visit(&mut |n| {
            if n.end > len || n.start > n.end {
                out.push(Inconsistency::NodeOutOfRange {
                    id: n.id,
                    start: n.start,
                    end: n.end,
                });
            }
        });
        out
    }
}

fn check_decision(d: &model::Decision, ctors: usize, owner: u32, out: &mut Vec<Inconsistency>) {
    for (ix, _) in &d.pairs {
        if *ix as usize >= ctors {
            out.push(Inconsistency::MissingSymbol {
                referenced_by: owner,
                id: *ix,
            });
        }
    }
    for c in &d.children {
        check_decision(c, ctors, owner, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_short_file_is_an_error() {
        assert!(matches!(Sla::parse(b"sla"), Err(SlaError::TooShort)));
    }

    #[test]
    fn bad_magic_is_an_error() {
        assert!(matches!(
            Sla::parse(b"xxxx....."),
            Err(SlaError::BadMagic(_))
        ));
    }

    #[test]
    fn every_byte_prefix_of_a_header_is_handled() {
        let junk = b"sla\x04\x78\x9c\x00\x01\x02\x03";
        for n in 0..junk.len() {
            let _ = Sla::parse(&junk[..n]);
        }
    }
}
