//! Content anchors: naming a location so the name survives a rebuild.
//!
//! Keying an annotation to an absolute address means a rebase, a relink, or a
//! recompile that shifts everything by a few bytes throws away the work. An
//! anchor is layered instead, most durable first:
//!
//! - `shape` fingerprints the instruction stream as `(length, flow class)`
//!   pairs. Branch targets are deliberately excluded, which is what makes it
//!   invariant to where the code is loaded.
//! - `bytes` fingerprints the raw body. It captures embedded addresses, so it
//!   matches only the identical binary, and is the fast exact path.
//! - `abs` is the entry address, a last-resort tiebreak.
//!
//! Resolution reports which layer matched, so a confident hit is
//! distinguishable from a best-effort one.

use std::fmt;

use r12e_arch::{Flow, Insn};
use r12e_core::Addr;

/// FNV-1a 64-bit, chosen for being byte-order fixed and reproducible across
/// platforms. Anchoring needs a stable identity, not collision resistance.
#[derive(Clone, Copy)]
pub struct Fnv(u64);

impl Default for Fnv {
    fn default() -> Self {
        Fnv::new()
    }
}

impl Fnv {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;

    /// A fresh hash.
    pub fn new() -> Fnv {
        Fnv(Fnv::OFFSET)
    }

    /// Fold one byte.
    pub fn byte(&mut self, b: u8) {
        self.0 ^= b as u64;
        self.0 = self.0.wrapping_mul(Fnv::PRIME);
    }

    /// Fold a slice.
    pub fn slice(&mut self, s: &[u8]) {
        for &b in s {
            self.byte(b);
        }
    }

    /// Fold a 64-bit value little-endian, so the result is byte-order fixed.
    pub fn u64(&mut self, v: u64) {
        self.slice(&v.to_le_bytes());
    }

    /// The digest.
    pub fn finish(self) -> u64 {
        self.0
    }
}

/// How an instruction transfers control, coarse enough to survive a rebuild.
fn flow_class(f: Flow) -> u8 {
    match f {
        Flow::Next => 0,
        Flow::Branch(_) => 1,
        Flow::CondBranch(_) => 2,
        Flow::IndirectBranch => 3,
        Flow::Call(_) => 4,
        Flow::IndirectCall => 5,
        Flow::Return => 6,
        Flow::Trap => 7,
        Flow::Syscall => 8,
    }
}

/// A stable identity for one location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Anchor {
    /// Rebase-invariant fingerprint of the instruction stream's shape.
    pub shape: u64,
    /// Exact fingerprint of the raw bytes, for the same-binary fast path.
    pub bytes: u64,
    /// How many instructions the shape covers.
    pub insns: u32,
    /// Entry address, a hint rather than an identity.
    pub abs: Addr,
    /// Byte offset from the anchored entry, so a comment can sit on one
    /// instruction rather than on the whole function.
    pub offset: u32,
}

impl Anchor {
    /// Anchor a function from its instructions, in address order, and its bytes.
    pub fn function(entry: Addr, insns: &[Insn], body: &[u8]) -> Anchor {
        let mut shape = Fnv::new();
        for i in insns {
            shape.byte(i.len);
            shape.byte(flow_class(i.flow));
        }
        let mut bytes = Fnv::new();
        bytes.slice(body);
        Anchor {
            shape: shape.finish(),
            bytes: bytes.finish(),
            insns: insns.len() as u32,
            abs: entry,
            offset: 0,
        }
    }

    /// The same anchor, pointing at a byte offset inside it.
    pub fn at_offset(self, offset: u32) -> Anchor {
        Anchor { offset, ..self }
    }

    /// The identity fields, excluding the address hint.
    pub fn identity(&self) -> (u64, u64, u32, u32) {
        (self.shape, self.bytes, self.insns, self.offset)
    }

    /// The address this anchor points at, entry plus offset.
    pub fn target(&self) -> Addr {
        self.abs.wrapping_offset(self.offset as i64)
    }
}

impl fmt::Display for Anchor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}/{:016x}+{}", self.shape, self.bytes, self.offset)
    }
}

/// How an anchor was matched when it was resolved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Resolution {
    /// The raw bytes matched: the same function in the same binary.
    Exact,
    /// The instruction shape matched uniquely: the same function, rebuilt.
    Shape,
    /// Only the address matched, and nothing corroborates it.
    Address,
    /// The shape matched more than one candidate; the address chose between
    /// them, so the answer is a guess.
    Ambiguous,
}

impl Resolution {
    /// The word shown in output.
    pub fn as_str(self) -> &'static str {
        match self {
            Resolution::Exact => "exact",
            Resolution::Shape => "shape",
            Resolution::Address => "address",
            Resolution::Ambiguous => "ambiguous",
        }
    }

    /// True when the match is strong enough to apply without a warning.
    pub fn is_confident(self) -> bool {
        matches!(self, Resolution::Exact | Resolution::Shape)
    }
}

impl fmt::Display for Resolution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Anchors for one analyzed binary, searchable by any layer.
#[derive(Debug, Clone, Default)]
pub struct AnchorIndex {
    /// Sorted by `bytes`.
    by_bytes: Vec<(u64, Anchor)>,
    /// Sorted by `shape`.
    by_shape: Vec<(u64, Anchor)>,
    /// Sorted by `abs`.
    by_abs: Vec<(Addr, Anchor)>,
}

impl AnchorIndex {
    /// Build from every anchored location in a program.
    pub fn build(anchors: impl IntoIterator<Item = Anchor>) -> AnchorIndex {
        let all: Vec<Anchor> = anchors.into_iter().collect();
        let mut by_bytes: Vec<(u64, Anchor)> = all.iter().map(|a| (a.bytes, *a)).collect();
        let mut by_shape: Vec<(u64, Anchor)> = all.iter().map(|a| (a.shape, *a)).collect();
        let mut by_abs: Vec<(Addr, Anchor)> = all.iter().map(|a| (a.abs, *a)).collect();
        by_bytes.sort_unstable();
        by_shape.sort_unstable();
        by_abs.sort_unstable();
        AnchorIndex {
            by_bytes,
            by_shape,
            by_abs,
        }
    }

    /// How many anchors are indexed.
    pub fn len(&self) -> usize {
        self.by_bytes.len()
    }

    /// True when nothing is indexed.
    pub fn is_empty(&self) -> bool {
        self.by_bytes.is_empty()
    }

    /// Find where an anchor points in this binary, and say how sure that is.
    pub fn resolve(&self, want: &Anchor) -> Option<(Anchor, Resolution)> {
        // The same bytes in the same binary: unambiguous.
        if let Some(a) = lookup(&self.by_bytes, want.bytes).first() {
            return Some((**a, Resolution::Exact));
        }
        // The same shape, rebuilt. Unique means confident; several means the
        // address is doing the choosing and the caller should be told.
        let by_shape = lookup(&self.by_shape, want.shape);
        match by_shape.len() {
            0 => {}
            1 => return Some((*by_shape[0], Resolution::Shape)),
            _ => {
                let pick = by_shape
                    .iter()
                    .find(|a| a.abs == want.abs)
                    .copied()
                    .unwrap_or(by_shape[0]);
                return Some((*pick, Resolution::Ambiguous));
            }
        }
        // Nothing but the address is left.
        lookup(&self.by_abs, want.abs)
            .first()
            .map(|a| (**a, Resolution::Address))
    }
}

/// Every value with the given key in a sorted list.
fn lookup<K: Ord + Copy>(v: &[(K, Anchor)], key: K) -> Vec<&Anchor> {
    let lo = v.partition_point(|(k, _)| *k < key);
    let hi = v.partition_point(|(k, _)| *k <= key);
    v[lo..hi].iter().map(|(_, a)| a).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use r12e_arch::aarch64;

    fn insns_of(words: &[u32], base: u64) -> Vec<Insn> {
        words
            .iter()
            .enumerate()
            .filter_map(|(n, w)| aarch64::decode_word(*w, Addr(base + n as u64 * 4)))
            .collect()
    }

    fn body_of(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    #[test]
    fn shape_survives_a_relink() {
        // The same function at two addresses, with its internal branch
        // displacement unchanged. Bytes differ only where the pc-relative
        // target lands, and shape ignores targets entirely.
        let words = [0xf100_041f, 0x5400_0040, 0xd280_0000, 0xd65f_03c0];
        let a = Anchor::function(Addr(0x1000), &insns_of(&words, 0x1000), &body_of(&words));
        let b = Anchor::function(Addr(0x9000), &insns_of(&words, 0x9000), &body_of(&words));
        assert_eq!(a.shape, b.shape);
        assert_ne!(a.abs, b.abs);
    }

    #[test]
    fn shape_changes_when_the_code_changes() {
        let one = [0xd280_0000u32, 0xd65f_03c0];
        let two = [0xd280_0000u32, 0xd280_0020, 0xd65f_03c0];
        let a = Anchor::function(Addr(0x1000), &insns_of(&one, 0x1000), &body_of(&one));
        let b = Anchor::function(Addr(0x1000), &insns_of(&two, 0x1000), &body_of(&two));
        assert_ne!(a.shape, b.shape);
    }

    #[test]
    fn exact_bytes_win_over_shape() {
        let words = [0xd280_0000u32, 0xd65f_03c0];
        let here = Anchor::function(Addr(0x1000), &insns_of(&words, 0x1000), &body_of(&words));
        let elsewhere = Anchor::function(Addr(0x9000), &insns_of(&words, 0x9000), &body_of(&words));
        let ix = AnchorIndex::build([here, elsewhere]);
        let (found, how) = ix.resolve(&here).unwrap();
        assert_eq!(how, Resolution::Exact);
        assert_eq!(found.abs, Addr(0x1000));
    }

    #[test]
    fn a_shared_shape_is_reported_as_ambiguous() {
        // Two identical functions at different addresses with different bytes:
        // shape alone cannot choose, so the answer says so.
        let mut a = Anchor::function(Addr(0x1000), &[], b"aaaa");
        let mut b = Anchor::function(Addr(0x2000), &[], b"bbbb");
        a.shape = 0x1234;
        b.shape = 0x1234;
        let ix = AnchorIndex::build([a, b]);
        let want = Anchor { bytes: 0xdead, ..a };
        let (_, how) = ix.resolve(&want).unwrap();
        assert_eq!(how, Resolution::Ambiguous);
        assert!(!how.is_confident());
    }

    #[test]
    fn the_address_is_the_last_resort() {
        let a = Anchor::function(Addr(0x1000), &[], b"aaaa");
        let ix = AnchorIndex::build([a]);
        let want = Anchor {
            shape: 0xdead,
            bytes: 0xbeef,
            ..a
        };
        let (found, how) = ix.resolve(&want).unwrap();
        assert_eq!(how, Resolution::Address);
        assert_eq!(found.abs, Addr(0x1000));
        assert!(!how.is_confident());
    }

    #[test]
    fn nothing_matches_nothing() {
        let ix = AnchorIndex::build([]);
        assert!(ix.resolve(&Anchor::function(Addr(1), &[], b"x")).is_none());
    }

    #[test]
    fn the_fingerprint_is_platform_fixed() {
        // A literal, so a change in the fold is a test failure rather than a
        // silent invalidation of every annotation file in existence.
        let mut h = Fnv::new();
        h.slice(b"r12e");
        assert_eq!(h.finish(), 0x0dd9_d620_bdbc_a6ed);
    }
}
