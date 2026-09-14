//! Identifying a function by what it is, not by where it is.
//!
//! A stripped binary still contains the same code the library did, so a
//! function's fingerprint identifies it across builds. The fingerprint is the
//! content anchor: a hash of the instruction shape stream with branch targets
//! excluded, which survives relinking, and a hash of the bytes, which does not
//! but is exact when it matches.
//!
//! The format is text and sorted, so a signature file is reviewable in a diff
//! and merges the way the annotation log does. A match reports which kind of
//! evidence it rested on, because an exact byte match and a shape match are
//! not the same claim.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::anchor::{Anchor, Resolution};

/// One function's fingerprint and what it is called.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signature {
    /// Hash of the instruction shapes, branch targets excluded.
    pub shape: u64,
    /// Hash of the bytes.
    pub bytes: u64,
    /// How many instructions it has.
    pub insns: u32,
    /// What it is called.
    pub name: String,
    /// Where the signature came from, for the record.
    pub source: String,
}

impl Signature {
    /// A signature for an anchored function.
    pub fn new(anchor: &Anchor, name: &str, source: &str) -> Signature {
        Signature {
            shape: anchor.shape,
            bytes: anchor.bytes,
            insns: anchor.insns,
            name: name.to_string(),
            source: source.to_string(),
        }
    }
}

/// A set of signatures, indexed for lookup.
#[derive(Debug, Clone, Default)]
pub struct Library {
    /// Every signature, sorted so the file is stable.
    pub signatures: Vec<Signature>,
    /// True when a file was longer than the reader would accept and the rest
    /// of it was dropped. The library is then a prefix of what the file said,
    /// which a caller has to be told rather than left to assume.
    pub truncated: bool,
    by_bytes: BTreeMap<u64, Vec<usize>>,
    by_shape: BTreeMap<u64, Vec<usize>>,
}

/// What a match rested on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Match<'a> {
    /// The signature that matched.
    pub signature: &'a Signature,
    /// How it was resolved.
    pub resolution: Resolution,
}

impl Library {
    /// Build from signatures, dropping shapes that name more than one thing.
    pub fn build(mut signatures: Vec<Signature>) -> Library {
        signatures.sort();
        signatures.dedup();
        let mut by_bytes: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        let mut by_shape: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        for (n, s) in signatures.iter().enumerate() {
            by_bytes.entry(s.bytes).or_default().push(n);
            by_shape.entry(s.shape).or_default().push(n);
        }
        Library {
            signatures,
            truncated: false,
            by_bytes,
            by_shape,
        }
    }

    /// How many signatures there are.
    pub fn len(&self) -> usize {
        self.signatures.len()
    }

    /// True when there are none.
    pub fn is_empty(&self) -> bool {
        self.signatures.is_empty()
    }

    /// What a function is, if the library knows.
    ///
    /// An exact byte match is a fact. A shape match is a claim about a
    /// function that was compiled from the same source and linked elsewhere,
    /// and it is only made when exactly one signature has that shape and the
    /// function is long enough for the shape to mean something.
    pub fn identify(&self, anchor: &Anchor) -> Option<Match<'_>> {
        if let Some(signature) = self
            .by_bytes
            .get(&anchor.bytes)
            .and_then(|c| self.agreed(c, anchor.insns))
        {
            return Some(Match {
                signature,
                resolution: Resolution::Exact,
            });
        }
        // A short function's shape is shared by hundreds of others: three
        // instructions of the same lengths and flow classes say nothing.
        if anchor.insns < MIN_SHAPE_INSNS {
            return None;
        }
        let signature = self
            .by_shape
            .get(&anchor.shape)
            .and_then(|c| self.agreed(c, anchor.insns))?;
        Some(Match {
            signature,
            resolution: Resolution::Shape,
        })
    }

    /// The one thing a set of candidates agrees this is.
    ///
    /// Two library functions with the same bytes under different names is a
    /// real thing — every import thunk in a binary differs only in the offset
    /// it loads — and picking one of them would be a coin flip reported as a
    /// fact.
    fn agreed(&self, candidates: &[usize], insns: u32) -> Option<&Signature> {
        let mut matching = candidates
            .iter()
            .filter_map(|n| self.signatures.get(*n))
            .filter(|s| s.insns == insns);
        let first = matching.next()?;
        matching
            .all(|other| other.name == first.name)
            .then_some(first)
    }

    /// The text form: one signature per line, sorted.
    pub fn to_text(&self) -> String {
        let mut out = String::from("# r12e signatures v1\n");
        for s in &self.signatures {
            let _ = writeln!(
                out,
                "{:016x} {:016x} {} {} {}",
                s.shape, s.bytes, s.insns, s.name, s.source
            );
        }
        out
    }

    /// Read the text form, ignoring lines it does not understand.
    ///
    /// A signature library is a file somebody else wrote: it travels between
    /// machines, it is checked into other people's repositories, and it is the
    /// output of a script that ran over packages nobody here chose. So an
    /// unreadable line is skipped rather than fatal, and the length of the
    /// file is bounded before the result is built.
    pub fn from_text(text: &str) -> Library {
        Library::from_text_capped(text, MAX_SIGNATURES)
    }

    /// The same, with the ceiling given explicitly.
    ///
    /// The text form carries no count for a hostile file to lie about, so the
    /// bound has to be on the result instead: reading stops at `max` and says
    /// it stopped, rather than growing until the allocator decides.
    pub fn from_text_capped(text: &str, max: usize) -> Library {
        let mut signatures = Vec::new();
        let mut truncated = false;
        for line in text.lines() {
            if signatures.len() >= max {
                truncated = true;
                break;
            }
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let mut parts = line.splitn(5, ' ');
            let (Some(shape), Some(bytes), Some(insns), Some(name)) =
                (parts.next(), parts.next(), parts.next(), parts.next())
            else {
                continue;
            };
            let (Ok(shape), Ok(bytes), Ok(insns)) = (
                u64::from_str_radix(shape, 16),
                u64::from_str_radix(bytes, 16),
                insns.parse::<u32>(),
            ) else {
                continue;
            };
            signatures.push(Signature {
                shape,
                bytes,
                insns,
                name: name.to_string(),
                source: parts.next().unwrap_or("").to_string(),
            });
        }
        let mut library = Library::build(signatures);
        library.truncated = truncated;
        library
    }

    /// Merge another library in.
    pub fn merge(&mut self, other: Library) {
        let truncated = self.truncated || other.truncated;
        let mut all = std::mem::take(&mut self.signatures);
        all.extend(other.signatures);
        *self = Library::build(all);
        self.truncated = truncated;
    }
}

/// Below this many instructions a shape match means nothing.
const MIN_SHAPE_INSNS: u32 = 24;

/// The most signatures one file may contribute.
///
/// Two million is more than every static archive a distribution ships, and it
/// is a number rather than an allocator failure.
pub const MAX_SIGNATURES: usize = 2_000_000;

#[cfg(test)]
mod tests {
    use super::*;
    use r12e_core::Addr;

    fn anchor(shape: u64, bytes: u64, insns: u32) -> Anchor {
        Anchor {
            shape,
            bytes,
            insns,
            abs: Addr(0x1000),
            offset: 0,
        }
    }

    #[test]
    fn an_exact_byte_match_is_reported_as_exact() {
        let library = Library::build(vec![Signature {
            shape: 1,
            bytes: 2,
            insns: 20,
            name: "memcpy".into(),
            source: "libc".into(),
        }]);
        let found = library.identify(&anchor(1, 2, 20)).expect("a match");
        assert_eq!(found.signature.name, "memcpy");
        assert_eq!(found.resolution, Resolution::Exact);
    }

    #[test]
    fn a_relinked_function_still_matches_by_shape() {
        let library = Library::build(vec![Signature {
            shape: 1,
            bytes: 2,
            insns: 40,
            name: "memcpy".into(),
            source: "libc".into(),
        }]);
        // Same shape, different bytes: the branch targets moved.
        let found = library.identify(&anchor(1, 99, 40)).expect("a match");
        assert_eq!(found.resolution, Resolution::Shape);
    }

    #[test]
    fn two_names_for_the_same_bytes_name_nothing() {
        let library = Library::build(vec![
            Signature {
                shape: 1,
                bytes: 2,
                insns: 20,
                name: "one@plt".into(),
                source: "a".into(),
            },
            Signature {
                shape: 1,
                bytes: 2,
                insns: 20,
                name: "another@plt".into(),
                source: "b".into(),
            },
        ]);
        assert!(library.identify(&anchor(1, 2, 20)).is_none());
    }

    #[test]
    fn an_ambiguous_shape_names_nothing() {
        let library = Library::build(vec![
            Signature {
                shape: 1,
                bytes: 2,
                insns: 40,
                name: "memcpy".into(),
                source: "libc".into(),
            },
            Signature {
                shape: 1,
                bytes: 3,
                insns: 40,
                name: "memmove".into(),
                source: "libc".into(),
            },
        ]);
        assert!(library.identify(&anchor(1, 99, 40)).is_none());
    }

    #[test]
    fn a_short_function_is_not_identified_by_shape_alone() {
        let library = Library::build(vec![Signature {
            shape: 1,
            bytes: 2,
            insns: 4,
            name: "stub".into(),
            source: "libc".into(),
        }]);
        assert!(library.identify(&anchor(1, 99, 4)).is_none());
    }

    #[test]
    fn the_text_form_round_trips() {
        let library = Library::build(vec![
            Signature {
                shape: 0xdead,
                bytes: 0xbeef,
                insns: 20,
                name: "memcpy".into(),
                source: "libc.so.6".into(),
            },
            Signature {
                shape: 1,
                bytes: 2,
                insns: 30,
                name: "strlen".into(),
                source: "libc.so.6".into(),
            },
        ]);
        let text = library.to_text();
        let back = Library::from_text(&text);
        assert_eq!(back.signatures, library.signatures);
        // Sorted, so two runs produce the same file.
        assert_eq!(back.to_text(), text);
    }
}
