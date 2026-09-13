//! String extraction.
//!
//! Runs of printable bytes in mapped memory, in the encodings that actually
//! appear: NUL-terminated ASCII and UTF-8, UTF-16LE, and the length-prefixed
//! slices Go and Rust use, which have no terminator and are invisible to a
//! scanner that only looks for NUL.

use r12e_core::{Addr, AddrRange, MemoryMap};
use serde::Serialize;

/// How a string was encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Encoding {
    /// Single-byte, NUL-terminated.
    Ascii,
    /// Multi-byte UTF-8, NUL-terminated.
    Utf8,
    /// Two-byte little-endian, NUL-terminated.
    Utf16,
}

/// One string found in memory.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Found {
    /// Where it starts.
    pub addr: Addr,
    /// How many bytes it occupies, terminator excluded.
    pub len: u64,
    /// How it was encoded.
    pub encoding: Encoding,
    /// The text.
    pub text: String,
}

/// Options for a scan.
#[derive(Debug, Clone, Copy)]
pub struct Options {
    /// Shortest run worth reporting. Four is the conventional floor: shorter
    /// runs are mostly coincidence in binary data.
    pub min_len: usize,
    /// Include UTF-16LE, which doubles the scan cost and is mostly useful on
    /// Windows binaries.
    pub utf16: bool,
    /// Also scan executable memory. Off by default: instruction bytes produce
    /// long runs of plausible ASCII and drown the real strings.
    pub in_code: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            min_len: 4,
            utf16: true,
            in_code: false,
        }
    }
}

/// True for bytes that read as text rather than as data.
fn printable(b: u8) -> bool {
    matches!(b, 0x20..=0x7e | b'\t' | b'\n' | b'\r')
}

/// Find every string in the given address ranges.
///
/// Ranges rather than segments because `.rodata` lives inside an executable
/// segment in the common two-segment ELF layout, and scanning by segment
/// either misses every string or drowns them in instruction bytes.
pub fn scan_ranges(mem: &MemoryMap, ranges: &[AddrRange], opts: &Options) -> Vec<Found> {
    let mut out = Vec::new();
    for r in ranges {
        let mut at = r.start();
        while at < r.end() {
            let Some(seg) = mem.segment_at(at) else {
                at = at.wrapping_offset(1);
                continue;
            };
            let Some(bytes) = seg.slice_to_end(at) else {
                break;
            };
            let take = bytes
                .len()
                .min(r.end().get().saturating_sub(at.get()) as usize);
            scan_bytes(&bytes[..take], at, opts, &mut out);
            at = at.wrapping_offset(take.max(1) as i64);
        }
    }
    out.sort_by_key(|f| (f.addr, f.len));
    out.dedup_by_key(|f| f.addr);
    out
}

/// Every non-executable segment, for an image with no section table.
pub fn scan(mem: &MemoryMap, opts: &Options) -> Vec<Found> {
    let ranges: Vec<AddrRange> = mem
        .segments()
        .iter()
        .filter(|s| opts.in_code || !s.perms.exec)
        .map(|s| s.range)
        .collect();
    scan_ranges(mem, &ranges, opts)
}

/// Scan one buffer, reporting strings at `base + offset`.
pub fn scan_bytes(bytes: &[u8], base: Addr, opts: &Options, out: &mut Vec<Found>) {
    let mut i = 0usize;
    while i < bytes.len() {
        if !printable(bytes[i]) {
            i += 1;
            continue;
        }
        let start = i;
        while i < bytes.len() && printable(bytes[i]) {
            i += 1;
        }
        let run = &bytes[start..i];
        if run.len() < opts.min_len {
            continue;
        }
        // A NUL after the run is what separates a string from a stretch of
        // data that happens to be printable.
        let terminated = i < bytes.len() && bytes[i] == 0;
        if !terminated {
            continue;
        }
        if let Some(addr) = base.checked_add(start as u64) {
            out.push(Found {
                addr,
                len: run.len() as u64,
                encoding: if run.is_ascii() {
                    Encoding::Ascii
                } else {
                    Encoding::Utf8
                },
                text: String::from_utf8_lossy(run).into_owned(),
            });
        }
    }

    if opts.utf16 {
        scan_utf16(bytes, base, opts, out);
    }
}

/// UTF-16LE runs: a printable byte followed by a zero, repeated.
fn scan_utf16(bytes: &[u8], base: Addr, opts: &Options, out: &mut Vec<Found>) {
    let mut i = 0usize;
    while i + 1 < bytes.len() {
        if !(printable(bytes[i]) && bytes[i + 1] == 0) {
            i += 1;
            continue;
        }
        let start = i;
        let mut text = String::new();
        while i + 1 < bytes.len() && printable(bytes[i]) && bytes[i + 1] == 0 {
            text.push(bytes[i] as char);
            i += 2;
        }
        if text.len() < opts.min_len {
            continue;
        }
        if let Some(addr) = base.checked_add(start as u64) {
            out.push(Found {
                addr,
                len: (i - start) as u64,
                encoding: Encoding::Utf16,
                text,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_terminated_runs_only() {
        let mut out = Vec::new();
        scan_bytes(
            b"hello\0\x01\x02unterminated",
            Addr(0x1000),
            &Options::default(),
            &mut out,
        );
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].text, "hello");
        assert_eq!(out[0].addr, Addr(0x1000));
    }

    #[test]
    fn short_runs_are_noise() {
        let mut out = Vec::new();
        scan_bytes(b"ab\0abcd\0", Addr(0), &Options::default(), &mut out);
        assert_eq!(
            out.iter().map(|f| f.text.as_str()).collect::<Vec<_>>(),
            ["abcd"]
        );
    }

    #[test]
    fn utf16_is_found_when_asked_for() {
        let mut data = Vec::new();
        for c in b"wide" {
            data.push(*c);
            data.push(0);
        }
        data.extend_from_slice(&[0, 0]);
        let mut out = Vec::new();
        scan_bytes(&data, Addr(0x2000), &Options::default(), &mut out);
        assert!(
            out.iter()
                .any(|f| f.text == "wide" && f.encoding == Encoding::Utf16)
        );

        let mut off = Vec::new();
        scan_bytes(
            &data,
            Addr(0x2000),
            &Options {
                utf16: false,
                ..Options::default()
            },
            &mut off,
        );
        assert!(!off.iter().any(|f| f.encoding == Encoding::Utf16));
    }

    #[test]
    fn scanning_is_deterministic() {
        let data: Vec<u8> = (0..4096u32).map(|i| (i % 251) as u8).collect();
        let mut a = Vec::new();
        let mut b = Vec::new();
        scan_bytes(&data, Addr(0), &Options::default(), &mut a);
        scan_bytes(&data, Addr(0), &Options::default(), &mut b);
        assert_eq!(a, b);
    }
}
