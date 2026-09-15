//! zlib (RFC 1950) and DEFLATE (RFC 1951) compression.
//!
//! The other half of `inflate.rs`, and written for the same reason: a `.sla`
//! payload is a zlib stream, so writing one at all needs a compressor, and the
//! workspace does not take a dependency for something both RFCs specify.
//!
//! Two block strategies, because they answer different questions:
//!
//! * [`Level::Stored`] emits type 0 blocks. The output is larger than the
//!   input by five bytes per 64 KB and is trivially correct, which makes it
//!   the control when something downstream looks wrong.
//! * [`Level::Fixed`] runs LZ77 with a hash chain and codes the result with
//!   the fixed Huffman tables of RFC 1951 section 3.2.6. No dynamic tables:
//!   they would buy perhaps another 15% and they are the part of DEFLATE with
//!   the most ways to be subtly wrong, so the size is spent rather than the
//!   risk taken. `docs/sla-format.md` records what this costs against the
//!   reference compiler's output.
//!
//! Neither reproduces zlib's own bit stream, and nothing here tries to: a
//! `.sla` is compared after decompression, because the compressed form is not
//! part of the format's meaning.

/// Which DEFLATE block type to emit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Level {
    /// Type 0 blocks: no compression, no matching, no Huffman coding.
    Stored,
    /// Type 1 blocks: LZ77 with the fixed Huffman tables.
    #[default]
    Fixed,
}

/// RFC 1950 section 9. Runs over the uncompressed bytes.
#[must_use]
pub fn adler32(data: &[u8]) -> u32 {
    const MOD: u32 = 65521;
    let (mut a, mut b) = (1u32, 0u32);
    // 5552 is the most bytes that can be summed before `b` can overflow 32
    // bits, so the modulo runs once a chunk rather than once a byte.
    for chunk in data.chunks(5552) {
        for &byte in chunk {
            a += u32::from(byte);
            b += a;
        }
        a %= MOD;
        b %= MOD;
    }
    (b << 16) | a
}

/// Compress to a zlib stream: the two-byte header, the DEFLATE data, and the
/// Adler-32 of the input.
#[must_use]
pub fn deflate_zlib(data: &[u8], level: Level) -> Vec<u8> {
    let mut out = Vec::with_capacity(data.len() / 2 + 64);
    // CMF: deflate, 32 KB window. FLG: no preset dictionary, and the check
    // bits chosen so the pair is a multiple of 31. 0x789c is what every file
    // in the corpus starts with, so our files start the same way.
    out.push(0x78);
    out.push(0x9c);
    match level {
        Level::Stored => stored_blocks(&mut out, data),
        Level::Fixed => fixed_blocks(&mut out, data),
    }
    out.extend_from_slice(&adler32(data).to_be_bytes());
    out
}

/// Raw DEFLATE with no zlib wrapper, for callers that supply their own.
#[must_use]
pub fn deflate(data: &[u8], level: Level) -> Vec<u8> {
    let mut out = Vec::new();
    match level {
        Level::Stored => stored_blocks(&mut out, data),
        Level::Fixed => fixed_blocks(&mut out, data),
    }
    out
}

fn stored_blocks(out: &mut Vec<u8>, data: &[u8]) {
    // A stored block's length field is sixteen bits, and an empty input still
    // needs one block so the stream has a final block to end on.
    let mut chunks = data.chunks(0xffff).peekable();
    if chunks.peek().is_none() {
        out.push(1);
        out.extend_from_slice(&0u16.to_le_bytes());
        out.extend_from_slice(&(!0u16).to_le_bytes());
        return;
    }
    while let Some(chunk) = chunks.next() {
        let last = chunks.peek().is_none();
        out.push(u8::from(last));
        let len = chunk.len() as u16;
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(&(!len).to_le_bytes());
        out.extend_from_slice(chunk);
    }
}

/// Bit output, least significant bit first within a byte, which is how
/// DEFLATE packs. Huffman codes go in most significant bit first and
/// everything else least significant bit first; the two writers below keep
/// that distinction where it belongs rather than at every call site.
struct BitWriter<'a> {
    out: &'a mut Vec<u8>,
    bits: u32,
    n: u32,
}

impl BitWriter<'_> {
    /// `n` bits of `v`, least significant first.
    fn put(&mut self, v: u32, n: u32) {
        self.bits |= (v & ((1u32 << n) - 1)) << self.n;
        self.n += n;
        while self.n >= 8 {
            self.out.push(self.bits as u8);
            self.bits >>= 8;
            self.n -= 8;
        }
    }

    /// A Huffman code: `n` bits of `code`, most significant first.
    fn put_code(&mut self, code: u32, n: u32) {
        let mut rev = 0u32;
        for i in 0..n {
            rev |= ((code >> (n - 1 - i)) & 1) << i;
        }
        self.put(rev, n);
    }

    fn flush(&mut self) {
        if self.n > 0 {
            self.out.push(self.bits as u8);
            self.bits = 0;
            self.n = 0;
        }
    }
}

/// The fixed literal/length code of RFC 1951 section 3.2.6.
fn fixed_lit(sym: u32) -> (u32, u32) {
    match sym {
        0..=143 => (0x30 + sym, 8),
        144..=255 => (0x190 + sym - 144, 9),
        256..=279 => (sym - 256, 7),
        _ => (0xc0 + sym - 280, 8),
    }
}

/// Length code, base and extra bits, for a match length of 3..=258.
fn length_code(len: u32) -> (u32, u32, u32) {
    const BASE: [u32; 29] = [
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
        131, 163, 195, 227, 258,
    ];
    const EXTRA: [u32; 29] = [
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
    ];
    let mut i = 28;
    while i > 0 && BASE[i] > len {
        i -= 1;
    }
    (257 + i as u32, EXTRA[i], len - BASE[i])
}

/// Distance code, base and extra bits, for a distance of 1..=32768.
fn distance_code(dist: u32) -> (u32, u32, u32) {
    const BASE: [u32; 30] = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
        2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
    ];
    const EXTRA: [u32; 30] = [
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
        13, 13,
    ];
    let mut i = 29;
    while i > 0 && BASE[i] > dist {
        i -= 1;
    }
    (i as u32, EXTRA[i], dist - BASE[i])
}

const WINDOW: usize = 32768;
const MIN_MATCH: usize = 3;
const MAX_MATCH: usize = 258;
const HASH_BITS: u32 = 15;
const HASH_SIZE: usize = 1 << HASH_BITS;
/// How many candidates at one hash to try. Bounds the worst case on input
/// with long runs of the same three bytes, which a `.sla` symbol table has
/// plenty of, at a small cost in ratio.
const MAX_CHAIN: usize = 128;

fn hash3(a: u8, b: u8, c: u8) -> usize {
    // Any spreading function will do; this is the usual multiply-shift.
    let v = (u32::from(a) << 16) | (u32::from(b) << 8) | u32::from(c);
    ((v.wrapping_mul(0x9e37_79b1)) >> (32 - HASH_BITS)) as usize
}

/// Longest match for the string at `pos`, searching the chain. Returns the
/// length and the distance back.
fn best_match(
    data: &[u8],
    pos: usize,
    head: &[u32],
    prev: &[u32],
    nice: usize,
) -> Option<(usize, usize)> {
    if pos + MIN_MATCH > data.len() {
        return None;
    }
    let limit = (data.len() - pos).min(MAX_MATCH);
    let h = hash3(data[pos], data[pos + 1], data[pos + 2]);
    let mut cand = head[h];
    let floor = pos.saturating_sub(WINDOW);
    let mut best = (0usize, 0usize);
    let mut tries = 0;
    while cand != u32::MAX {
        let c = cand as usize;
        if c < floor || c >= pos {
            break;
        }
        // Nothing can beat a match that already reaches the cap.
        if best.0 >= limit {
            break;
        }
        // Only the byte past the current best can extend it, so check it
        // first and skip the whole compare when it cannot.
        if best.0 == 0 || data[c + best.0] == data[pos + best.0] {
            let mut n = 0;
            while n < limit && data[c + n] == data[pos + n] {
                n += 1;
            }
            if n > best.0 {
                best = (n, pos - c);
                if n >= nice {
                    break;
                }
            }
        }
        tries += 1;
        if tries >= MAX_CHAIN {
            break;
        }
        cand = prev[c];
    }
    (best.0 >= MIN_MATCH).then_some(best)
}

fn fixed_blocks(out: &mut Vec<u8>, data: &[u8]) {
    let mut w = BitWriter { out, bits: 0, n: 0 };
    // One block for the whole input. Splitting would only help if the fixed
    // tables were being re-chosen, and they are not.
    w.put(1, 1); // BFINAL
    w.put(1, 2); // BTYPE = fixed Huffman

    let mut head = vec![u32::MAX; HASH_SIZE];
    let mut prev = vec![u32::MAX; data.len()];
    let mut pos = 0usize;

    let insert = |head: &mut Vec<u32>, prev: &mut Vec<u32>, at: usize| {
        if at + MIN_MATCH <= data.len() {
            let h = hash3(data[at], data[at + 1], data[at + 2]);
            prev[at] = head[h];
            head[h] = at as u32;
        }
    };

    let emit_literal = |w: &mut BitWriter, b: u8| {
        let (code, n) = fixed_lit(u32::from(b));
        w.put_code(code, n);
    };

    while pos < data.len() {
        let m = best_match(data, pos, &head, &prev, 32);
        // Lazy matching: a match one byte later that is strictly longer is
        // worth the extra literal, which is the cheapest large win DEFLATE
        // has and costs one extra search per position.
        let m = match m {
            Some((len, dist)) if len < MAX_MATCH => {
                let next = best_match(data, pos + 1, &head, &prev, 32);
                match next {
                    Some((len2, _)) if len2 > len => None,
                    _ => Some((len, dist)),
                }
            }
            other => other,
        };

        match m {
            Some((len, dist)) => {
                let (lc, lextra, lval) = length_code(len as u32);
                let (code, n) = fixed_lit(lc);
                w.put_code(code, n);
                if lextra > 0 {
                    w.put(lval, lextra);
                }
                let (dc, dextra, dval) = distance_code(dist as u32);
                w.put_code(dc, 5);
                if dextra > 0 {
                    w.put(dval, dextra);
                }
                for i in 0..len {
                    insert(&mut head, &mut prev, pos + i);
                }
                pos += len;
            }
            None => {
                emit_literal(&mut w, data[pos]);
                insert(&mut head, &mut prev, pos);
                pos += 1;
            }
        }
    }

    let (code, n) = fixed_lit(256); // end of block
    w.put_code(code, n);
    w.flush();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inflate::inflate_zlib;

    fn round(data: &[u8], level: Level) {
        let z = deflate_zlib(data, level);
        let back = inflate_zlib(&z, 1 << 24).expect("our own inflate reads it");
        assert_eq!(back, data, "level {level:?}");
    }

    #[test]
    fn adler_matches_the_rfc_example() {
        // RFC 1950 defines the initial value as 1, so the empty string is 1.
        assert_eq!(adler32(b""), 1);
        assert_eq!(adler32(b"a"), 0x0062_0062);
        assert_eq!(adler32(b"Wikipedia"), 0x11E6_0398);
    }

    #[test]
    fn stored_round_trips() {
        round(b"", Level::Stored);
        round(b"x", Level::Stored);
        round(&vec![0xab; 200_000], Level::Stored);
    }

    #[test]
    fn fixed_round_trips() {
        round(b"", Level::Fixed);
        round(b"x", Level::Fixed);
        round(b"the quick brown fox jumps over the lazy dog", Level::Fixed);
        round(&vec![0xab; 200_000], Level::Fixed);
    }

    #[test]
    fn fixed_round_trips_over_every_byte_value() {
        // The 8- and 9-bit halves of the fixed literal table are a place a
        // writer can be wrong for only some inputs, so cover all 256.
        let data: Vec<u8> = (0..=255u8).cycle().take(10_000).collect();
        round(&data, Level::Fixed);
    }

    #[test]
    fn fixed_round_trips_over_long_matches() {
        // Exercises the top of the length table and distances past 16 KB.
        let mut data: Vec<u8> = (0..60_000u32).map(|i| (i * 7) as u8).collect();
        let tail = data[0..20_000].to_vec();
        data.extend_from_slice(&tail);
        round(&data, Level::Fixed);
    }

    #[test]
    fn fixed_actually_compresses() {
        let data: Vec<u8> = b"sleigh ".iter().copied().cycle().take(100_000).collect();
        let z = deflate_zlib(&data, Level::Fixed);
        assert!(z.len() < data.len() / 20, "got {} bytes", z.len());
    }

    #[test]
    fn random_shapes_survive() {
        // A cheap deterministic generator: no dependency, and the point is
        // coverage of the matcher's corner cases rather than randomness.
        let mut state = 0x1234_5678u32;
        for case in 0..40 {
            let n = 1 + case * 97;
            let data: Vec<u8> = (0..n)
                .map(|_| {
                    state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                    // Small alphabet, so matches are common.
                    (state >> 24) as u8 % (1 + (case % 7) as u8)
                })
                .collect();
            round(&data, Level::Fixed);
        }
    }
}
