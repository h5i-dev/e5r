//! Addresses and ranges. 64-bit throughout, arithmetic always checked:
//! hostile files contain headers that wrap the address space.

use std::fmt;

use serde::{Deserialize, Serialize};

/// A virtual address. Displays as `0x` hex.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Addr(pub u64);

impl Addr {
    /// Address zero. Not null: firmware puts code there.
    pub const ZERO: Addr = Addr(0);
    /// The highest representable address.
    pub const MAX: Addr = Addr(u64::MAX);

    #[inline]
    /// An address at `v`.
    pub const fn new(v: u64) -> Self {
        Addr(v)
    }

    #[inline]
    /// The raw 64-bit value.
    pub const fn get(self) -> u64 {
        self.0
    }

    /// Add an offset, or `None` if the sum does not fit in 64 bits.
    #[inline]
    pub const fn checked_add(self, n: u64) -> Option<Addr> {
        match self.0.checked_add(n) {
            Some(v) => Some(Addr(v)),
            None => None,
        }
    }

    /// Subtract an offset, or `None` if the result would be negative.
    #[inline]
    pub const fn checked_sub(self, n: u64) -> Option<Addr> {
        match self.0.checked_sub(n) {
            Some(v) => Some(Addr(v)),
            None => None,
        }
    }

    /// Add a signed displacement, wrapping like the CPU does.
    #[inline]
    pub const fn wrapping_offset(self, delta: i64) -> Addr {
        Addr(self.0.wrapping_add(delta as u64))
    }

    /// Distance from `self` to `other`, or `None` if `other` is below `self`.
    #[inline]
    pub const fn distance_to(self, other: Addr) -> Option<u64> {
        other.0.checked_sub(self.0)
    }

    /// Round down to a multiple of `align`. `align` must be a power of two.
    #[inline]
    pub const fn align_down(self, align: u64) -> Addr {
        debug_assert!(align.is_power_of_two());
        Addr(self.0 & !(align - 1))
    }

    /// Round up to a multiple of `align`, or `None` on overflow.
    #[inline]
    pub fn align_up(self, align: u64) -> Option<Addr> {
        debug_assert!(align.is_power_of_two());
        self.0
            .checked_add(align - 1)
            .map(|v| Addr(v & !(align - 1)))
    }
}

impl fmt::Debug for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0)
    }
}

impl fmt::Display for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0)
    }
}

impl fmt::LowerHex for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl From<u64> for Addr {
    fn from(v: u64) -> Self {
        Addr(v)
    }
}

/// Half-open `start..end`. Cannot be built inverted, so callers never check.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AddrRange {
    start: Addr,
    end: Addr,
}

impl AddrRange {
    /// Build from a start and an end, or `None` if `end < start`.
    #[inline]
    pub const fn new(start: Addr, end: Addr) -> Option<AddrRange> {
        if end.0 < start.0 {
            None
        } else {
            Some(AddrRange { start, end })
        }
    }

    /// Build from a start and a length, or `None` if the end would overflow.
    #[inline]
    pub const fn sized(start: Addr, len: u64) -> Option<AddrRange> {
        match start.checked_add(len) {
            Some(end) => Some(AddrRange { start, end }),
            None => None,
        }
    }

    /// An empty range at `at`.
    #[inline]
    pub const fn empty_at(at: Addr) -> AddrRange {
        AddrRange { start: at, end: at }
    }

    #[inline]
    /// The first address in the range.
    pub const fn start(self) -> Addr {
        self.start
    }

    #[inline]
    /// One past the last address in the range.
    pub const fn end(self) -> Addr {
        self.end
    }

    #[inline]
    /// How many addresses the range covers.
    pub const fn len(self) -> u64 {
        self.end.0 - self.start.0
    }

    #[inline]
    /// True when the range covers no addresses.
    pub const fn is_empty(self) -> bool {
        self.start.0 == self.end.0
    }

    #[inline]
    /// True when `a` falls inside the range.
    pub const fn contains(self, a: Addr) -> bool {
        a.0 >= self.start.0 && a.0 < self.end.0
    }

    #[inline]
    /// True when `other` lies entirely inside this range.
    pub const fn contains_range(self, other: AddrRange) -> bool {
        other.start.0 >= self.start.0 && other.end.0 <= self.end.0
    }

    /// True when the ranges share an address. Empty ranges overlap nothing.
    #[inline]
    pub const fn overlaps(self, other: AddrRange) -> bool {
        !self.is_empty()
            && !other.is_empty()
            && self.start.0 < other.end.0
            && other.start.0 < self.end.0
    }

    /// The shared part of two ranges, or `None` when they are disjoint.
    #[inline]
    pub fn intersect(self, other: AddrRange) -> Option<AddrRange> {
        let start = Addr(self.start.0.max(other.start.0));
        let end = Addr(self.end.0.min(other.end.0));
        if start.0 < end.0 {
            Some(AddrRange { start, end })
        } else {
            None
        }
    }

    /// Iterate the addresses in the range.
    pub fn iter(self) -> impl Iterator<Item = Addr> {
        (self.start.0..self.end.0).map(Addr)
    }
}

impl fmt::Debug for AddrRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}..{:#x}", self.start.0, self.end.0)
    }
}

impl fmt::Display for AddrRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}..{:#x}", self.start.0, self.end.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_add_refuses_to_wrap() {
        assert_eq!(Addr::MAX.checked_add(1), None);
        assert_eq!(Addr(0x1000).checked_add(0x10), Some(Addr(0x1010)));
    }

    #[test]
    fn wrapping_offset_follows_the_machine() {
        // A backward branch from the bottom of the address space is what the
        // CPU computes, so it is what we report.
        assert_eq!(Addr(4).wrapping_offset(-8), Addr(u64::MAX - 3));
        assert_eq!(Addr(0x1000).wrapping_offset(-0x10), Addr(0xff0));
    }

    #[test]
    fn inverted_ranges_cannot_be_built() {
        assert!(AddrRange::new(Addr(0x20), Addr(0x10)).is_none());
        assert!(AddrRange::new(Addr(0x10), Addr(0x10)).is_some());
    }

    #[test]
    fn sized_range_refuses_to_wrap() {
        // The hostile-section-header case: a start near the top plus a length
        // that carries past the end of the address space.
        assert!(AddrRange::sized(Addr(u64::MAX - 0x10), 0x20).is_none());
        assert_eq!(
            AddrRange::sized(Addr(0x1000), 0x100).map(|r| r.end()),
            Some(Addr(0x1100))
        );
    }

    #[test]
    fn empty_ranges_overlap_nothing() {
        let empty = AddrRange::empty_at(Addr(0x1000));
        let covering = AddrRange::sized(Addr(0), 0x2000).unwrap();
        assert!(!empty.overlaps(empty));
        assert!(!covering.overlaps(empty));
        assert!(covering.contains_range(empty));
    }

    #[test]
    fn intersect_is_symmetric() {
        let a = AddrRange::sized(Addr(0x1000), 0x100).unwrap();
        let b = AddrRange::sized(Addr(0x1080), 0x100).unwrap();
        let want = AddrRange::sized(Addr(0x1080), 0x80).unwrap();
        assert_eq!(a.intersect(b), Some(want));
        assert_eq!(b.intersect(a), Some(want));
        let c = AddrRange::sized(Addr(0x4000), 0x10).unwrap();
        assert_eq!(a.intersect(c), None);
    }

    #[test]
    fn alignment() {
        assert_eq!(Addr(0x1234).align_down(0x1000), Addr(0x1000));
        assert_eq!(Addr(0x1234).align_up(0x1000), Some(Addr(0x2000)));
        assert_eq!(Addr(0x2000).align_up(0x1000), Some(Addr(0x2000)));
        assert_eq!(Addr::MAX.align_up(0x1000), None);
    }
}
