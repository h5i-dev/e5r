//! What bytes live at what addresses. A loader's job ends here; everything
//! above reads through this and never learns the container format.
//!
//! Two things it has to get right: `.bss` is mapped with no file bytes and must
//! read as zeros rather than as a neighbour's data, and segments overlap on
//! hostile input, resolved last-inserted-wins so the result is deterministic.

use serde::{Deserialize, Serialize};

use crate::addr::{Addr, AddrRange};
use crate::error::{Error, Result};

/// Access permissions on a mapped range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Perms {
    /// The program may read these bytes.
    pub read: bool,
    /// The program may write these bytes.
    pub write: bool,
    /// The program may execute these bytes.
    pub exec: bool,
}

impl Perms {
    /// Read only.
    pub const R: Perms = Perms {
        read: true,
        write: false,
        exec: false,
    };
    /// Read and write.
    pub const RW: Perms = Perms {
        read: true,
        write: true,
        exec: false,
    };
    /// Read and execute.
    pub const RX: Perms = Perms {
        read: true,
        write: false,
        exec: true,
    };
    /// All three.
    pub const RWX: Perms = Perms {
        read: true,
        write: true,
        exec: true,
    };

    /// Build a permission set from three flags.
    pub fn new(read: bool, write: bool, exec: bool) -> Perms {
        Perms { read, write, exec }
    }

    /// The `rwx` string.
    pub fn as_str(self) -> &'static str {
        match (self.read, self.write, self.exec) {
            (false, false, false) => "---",
            (true, false, false) => "r--",
            (false, true, false) => "-w-",
            (false, false, true) => "--x",
            (true, true, false) => "rw-",
            (true, false, true) => "r-x",
            (false, true, true) => "-wx",
            (true, true, true) => "rwx",
        }
    }
}

impl std::fmt::Display for Perms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One mapped range of the address space.
#[derive(Debug, Clone)]
pub struct Segment {
    /// Where it lives in memory.
    pub range: AddrRange,
    /// What the program may do with it.
    pub perms: Perms,
    /// Container's name for it, empty when it has none (ELF program headers).
    pub name: String,
    /// Offset in the file the bytes came from, for reporting and for patching.
    pub file_offset: u64,
    /// File bytes. Shorter than `range.len()` when the tail is zero-filled.
    data: Vec<u8>,
}

impl Segment {
    /// Overwrite bytes in the segment. Returns false when the write would
    /// leave the part that is backed by the file.
    pub fn patch(&mut self, at: Addr, bytes: &[u8]) -> bool {
        let Some(offset) = at.get().checked_sub(self.range.start().get()) else {
            return false;
        };
        let Ok(offset) = usize::try_from(offset) else {
            return false;
        };
        let Some(slot) = self.data.get_mut(offset..offset + bytes.len()) else {
            return false;
        };
        slot.copy_from_slice(bytes);
        true
    }

    /// A segment backed by file bytes.
    pub fn new(
        range: AddrRange,
        perms: Perms,
        name: impl Into<String>,
        file_offset: u64,
        data: Vec<u8>,
    ) -> Result<Segment> {
        if data.len() as u64 > range.len() {
            return Err(Error::inconsistent(format!(
                "segment {name} at {range} holds {:#x} file bytes but spans only {:#x}",
                data.len(),
                range.len(),
                name = name.into()
            )));
        }
        Ok(Segment {
            range,
            perms,
            name: name.into(),
            file_offset,
            data,
        })
    }

    /// All zeros, no file bytes. `.bss`.
    pub fn zeroed(range: AddrRange, perms: Perms, name: impl Into<String>) -> Segment {
        Segment {
            range,
            perms,
            name: name.into(),
            file_offset: 0,
            data: Vec::new(),
        }
    }

    /// Bytes backed by the file; the rest read as zero.
    pub fn file_len(&self) -> u64 {
        self.data.len() as u64
    }

    /// True when part of this segment is zero-filled rather than file-backed.
    pub fn has_zero_fill(&self) -> bool {
        self.file_len() < self.range.len()
    }

    /// Read `len` bytes, zero-filling the tail. `None` if not fully inside.
    pub fn read(&self, addr: Addr, len: u64) -> Option<Vec<u8>> {
        let want = AddrRange::sized(addr, len)?;
        if !self.range.contains_range(want) {
            return None;
        }
        let off = self.range.start().distance_to(addr)? as usize;
        let len = len as usize;
        let mut out = vec![0u8; len];
        if off < self.data.len() {
            let take = len.min(self.data.len() - off);
            out[..take].copy_from_slice(&self.data[off..off + take]);
        }
        Some(out)
    }

    /// Borrow file-backed bytes. `None` if any would come from the zero tail.
    pub fn slice(&self, addr: Addr, len: u64) -> Option<&[u8]> {
        let off = self.range.start().distance_to(addr)?;
        let end = off.checked_add(len)?;
        if end > self.data.len() as u64 {
            return None;
        }
        Some(&self.data[off as usize..end as usize])
    }

    /// All file-backed bytes from `addr` to the end of the segment.
    pub fn slice_to_end(&self, addr: Addr) -> Option<&[u8]> {
        let off = self.range.start().distance_to(addr)?;
        if off >= self.data.len() as u64 {
            return None;
        }
        Some(&self.data[off as usize..])
    }
}

/// Every mapped range in one program, searchable by address.
#[derive(Debug, Clone, Default)]
pub struct MemoryMap {
    /// Sorted by start address. Kept sorted by [`MemoryMap::add`] so lookup can
    /// binary search.
    segments: Vec<Segment>,
}

impl MemoryMap {
    /// An empty map.
    pub fn new() -> MemoryMap {
        MemoryMap::default()
    }

    /// Insert, keeping the list sorted. Overlaps are allowed: hostile files
    /// have them and refusing would refuse the interesting binaries.
    pub fn add(&mut self, seg: Segment) {
        let at = self
            .segments
            .partition_point(|s| s.range.start() <= seg.range.start());
        self.segments.insert(at, seg);
    }

    /// Every segment, sorted by start address.
    /// Overwrite bytes wherever they are mapped, for a relocation the loader
    /// has to apply itself.
    pub fn patch(&mut self, at: Addr, bytes: &[u8]) -> bool {
        self.segments
            .iter_mut()
            .find(|s| s.range.contains(at))
            .is_some_and(|s| s.patch(at, bytes))
    }

    /// The segments, in address order.
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }

    /// True when nothing is mapped.
    pub fn is_empty(&self) -> bool {
        self.segments.is_empty()
    }

    /// Lowest to highest mapped address.
    pub fn bounds(&self) -> Option<AddrRange> {
        let lo = self.segments.first()?.range.start();
        let hi = self
            .segments
            .iter()
            .map(|s| s.range.end())
            .max()
            .unwrap_or(lo);
        AddrRange::new(lo, hi)
    }

    /// The segment containing `addr`, or `None`.
    pub fn segment_at(&self, addr: Addr) -> Option<&Segment> {
        // Candidates all start at or before addr; scan back from the partition
        // point. Overlaps are rare, so this stays effectively O(log n).
        let end = self.segments.partition_point(|s| s.range.start() <= addr);
        self.segments[..end]
            .iter()
            .rev()
            .find(|s| s.range.contains(addr))
    }

    /// True when the address is mapped at all.
    pub fn is_mapped(&self, addr: Addr) -> bool {
        self.segment_at(addr).is_some()
    }

    /// True when the address is mapped and executable.
    pub fn is_executable(&self, addr: Addr) -> bool {
        self.segment_at(addr).is_some_and(|s| s.perms.exec)
    }

    /// True when the address is mapped and writable.
    pub fn is_writable(&self, addr: Addr) -> bool {
        self.segment_at(addr).is_some_and(|s| s.perms.write)
    }

    /// Read `len` bytes, zero-filling unbacked parts.
    pub fn read(&self, addr: Addr, len: u64) -> Result<Vec<u8>> {
        self.segment_at(addr)
            .and_then(|s| s.read(addr, len))
            .ok_or(Error::Unmapped { addr })
    }

    /// Borrow file-backed bytes without copying, for a decoder's hot path.
    pub fn slice(&self, addr: Addr, len: u64) -> Option<&[u8]> {
        self.segment_at(addr)?.slice(addr, len)
    }

    /// Up to `max` bytes, however many are actually there. A decoder wants a
    /// truncated instruction at a section end, not an error.
    pub fn decode_window(&self, addr: Addr, max: u64) -> Option<&[u8]> {
        let s = self.segment_at(addr)?;
        let all = s.slice_to_end(addr)?;
        Some(&all[..all.len().min(max as usize)])
    }

    /// Read a pointer-sized value.
    pub fn read_ptr(&self, addr: Addr, bytes: u64, little_endian: bool) -> Result<u64> {
        let b = self.read(addr, bytes)?;
        let mut v: u64 = 0;
        if little_endian {
            for (i, byte) in b.iter().enumerate() {
                v |= (*byte as u64) << (8 * i);
            }
        } else {
            for byte in b.iter() {
                v = (v << 8) | *byte as u64;
            }
        }
        Ok(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seg(start: u64, len: u64, data: &[u8], perms: Perms, name: &str) -> Segment {
        Segment::new(
            AddrRange::sized(Addr(start), len).unwrap(),
            perms,
            name,
            0,
            data.to_vec(),
        )
        .unwrap()
    }

    #[test]
    fn bss_reads_as_zero_not_as_the_next_segment() {
        // The bug this prevents: .data and .bss are adjacent in memory and
        // their file bytes are not, so a naive implementation returns .data's
        // neighbour bytes for a .bss read.
        let mut m = MemoryMap::new();
        m.add(seg(0x1000, 0x10, &[0xaa; 0x10], Perms::RW, ".data"));
        m.add(Segment::zeroed(
            AddrRange::sized(Addr(0x1010), 0x20).unwrap(),
            Perms::RW,
            ".bss",
        ));
        assert_eq!(m.read(Addr(0x1010), 8).unwrap(), vec![0u8; 8]);
        assert_eq!(m.read(Addr(0x1000), 4).unwrap(), vec![0xaa; 4]);
    }

    #[test]
    fn a_segment_that_is_part_file_part_zero_splits_correctly() {
        let mut m = MemoryMap::new();
        // Memory size 0x10, file size 4: the classic ELF PT_LOAD with .bss.
        m.add(seg(0x2000, 0x10, &[1, 2, 3, 4], Perms::RW, "load"));
        assert_eq!(
            m.read(Addr(0x2000), 8).unwrap(),
            vec![1, 2, 3, 4, 0, 0, 0, 0]
        );
        // Borrowing refuses to reach into the zero tail, so a decoder cannot
        // silently decode zeros as instructions.
        assert!(m.slice(Addr(0x2000), 8).is_none());
        assert_eq!(m.slice(Addr(0x2000), 4).unwrap(), &[1, 2, 3, 4]);
    }

    #[test]
    fn segment_declaring_more_file_bytes_than_it_spans_is_rejected() {
        let r = Segment::new(
            AddrRange::sized(Addr(0x1000), 4).unwrap(),
            Perms::R,
            "liar",
            0,
            vec![0; 64],
        );
        assert!(r.is_err());
    }

    #[test]
    fn lookup_finds_the_right_segment_among_many() {
        let mut m = MemoryMap::new();
        for i in 0..64u64 {
            m.add(seg(
                0x1000 + i * 0x100,
                0x80,
                &[i as u8; 0x80],
                Perms::R,
                "s",
            ));
        }
        assert_eq!(m.read(Addr(0x1000 + 40 * 0x100), 1).unwrap(), vec![40]);
        // The 0x80 gap between each pair is genuinely unmapped.
        assert!(!m.is_mapped(Addr(0x1000 + 40 * 0x100 + 0x90)));
    }

    #[test]
    fn unmapped_reads_are_errors_not_zeros() {
        let m = MemoryMap::new();
        assert!(matches!(
            m.read(Addr(0x1000), 1),
            Err(Error::Unmapped { .. })
        ));
    }

    #[test]
    fn decode_window_truncates_at_the_end_of_a_section() {
        let mut m = MemoryMap::new();
        m.add(seg(
            0x1000,
            4,
            &[0x90, 0x90, 0x90, 0x90],
            Perms::RX,
            ".text",
        ));
        // Asking for 15 bytes at the last byte yields the one byte there is,
        // which is what a decoder needs to report a truncated instruction.
        assert_eq!(m.decode_window(Addr(0x1003), 15).unwrap().len(), 1);
        assert_eq!(m.decode_window(Addr(0x1000), 15).unwrap().len(), 4);
    }

    #[test]
    fn permissions_are_queryable_by_address() {
        let mut m = MemoryMap::new();
        m.add(seg(0x1000, 0x10, &[0; 0x10], Perms::RX, ".text"));
        m.add(seg(0x2000, 0x10, &[0; 0x10], Perms::RW, ".data"));
        assert!(m.is_executable(Addr(0x1004)));
        assert!(!m.is_executable(Addr(0x2004)));
        assert!(m.is_writable(Addr(0x2004)));
        assert!(!m.is_writable(Addr(0x1004)));
    }

    #[test]
    fn read_ptr_respects_byte_order() {
        let mut m = MemoryMap::new();
        m.add(seg(
            0x1000,
            8,
            &[0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0],
            Perms::R,
            "d",
        ));
        assert_eq!(m.read_ptr(Addr(0x1000), 4, true).unwrap(), 0x1234_5678);
        assert_eq!(m.read_ptr(Addr(0x1000), 4, false).unwrap(), 0x7856_3412);
    }
}
