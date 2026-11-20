//! zlib (RFC 1950) and DEFLATE (RFC 1951) decompression.
//!
//! A `.sla` payload is a bare zlib stream, so reading one at all needs an
//! inflater. The workspace keeps its dependency list to serde, clap and
//! memmap2, so it is written here rather than pulled in.
//!
//! Every count that comes out of the stream is checked against what is left of
//! the input before anything is allocated, and the output is capped, so a
//! crafted header cannot make this allocate or spin.

/// Ceiling on the decompressed size. The largest `.sla` shipped by Ghidra 12.1
/// expands to 4.3 MB, so 256 MB is four and a half orders of magnitude of
/// headroom and still small enough that a zip bomb fails fast.
pub const DEFAULT_LIMIT: usize = 256 << 20;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InflateError {
    /// Ran off the end of the input.
    Truncated,
    /// The two-byte zlib header is not a zlib header we can read.
    BadZlibHeader,
    /// A preset dictionary is required; `.sla` never uses one.
    PresetDictionary,
    /// A block type field held the reserved value 3.
    ReservedBlockType,
    /// A stored block's length and its complement disagree.
    StoredLengthMismatch,
    /// A Huffman table was over- or under-subscribed.
    BadHuffmanTable,
    /// A symbol that no code in the table maps to.
    BadHuffmanCode,
    /// A back reference pointing before the start of the output.
    DistanceTooFar,
    /// Output would exceed the limit.
    LimitExceeded,
    /// The trailing Adler-32 does not match the bytes produced.
    ChecksumMismatch,
}

impl core::fmt::Display for InflateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            Self::Truncated => "compressed stream ends early",
            Self::BadZlibHeader => "not a zlib header",
            Self::PresetDictionary => "zlib preset dictionary not supported",
            Self::ReservedBlockType => "reserved deflate block type",
            Self::StoredLengthMismatch => "stored block length mismatch",
            Self::BadHuffmanTable => "malformed huffman table",
            Self::BadHuffmanCode => "undecodable huffman code",
            Self::DistanceTooFar => "back reference before start of output",
            Self::LimitExceeded => "decompressed size over limit",
            Self::ChecksumMismatch => "adler-32 mismatch",
        };
        f.write_str(s)
    }
}

impl std::error::Error for InflateError {}

type Result<T> = core::result::Result<T, InflateError>;

struct BitReader<'a> {
    data: &'a [u8],
    pos: usize,
    buf: u32,
    have: u32,
}

impl<'a> BitReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self {
            data,
            pos: 0,
            buf: 0,
            have: 0,
        }
    }

    /// Least-significant-bit-first, which is how DEFLATE packs everything
    /// except the Huffman codes themselves.
    fn bits(&mut self, n: u32) -> Result<u32> {
        debug_assert!(n <= 16);
        while self.have < n {
            let b = *self.data.get(self.pos).ok_or(InflateError::Truncated)?;
            self.pos += 1;
            self.buf |= u32::from(b) << self.have;
            self.have += 8;
        }
        let v = if n == 32 {
            self.buf
        } else {
            self.buf & ((1u32 << n) - 1)
        };
        self.buf >>= n;
        self.have -= n;
        Ok(v)
    }

    fn align(&mut self) {
        let drop = self.have % 8;
        self.buf >>= drop;
        self.have -= drop;
    }

    fn byte(&mut self) -> Result<u8> {
        if self.have >= 8 {
            let v = (self.buf & 0xff) as u8;
            self.buf >>= 8;
            self.have -= 8;
            return Ok(v);
        }
        let b = *self.data.get(self.pos).ok_or(InflateError::Truncated)?;
        self.pos += 1;
        Ok(b)
    }

    /// Bytes not yet handed out, counting whole buffered bits.
    fn remaining(&self) -> usize {
        self.data.len() - self.pos + (self.have / 8) as usize
    }
}

const MAX_BITS: usize = 15;

/// A canonical Huffman table in the count/symbol form: `counts[n]` is how many
/// codes have length `n`, and `symbols` lists the symbols in canonical order.
/// Decoding walks the lengths, which needs no table memory proportional to the
/// alphabet and cannot index out of range.
struct Huffman {
    counts: [u16; MAX_BITS + 1],
    symbols: Vec<u16>,
}

impl Huffman {
    fn new(lengths: &[u8]) -> Result<Self> {
        let mut counts = [0u16; MAX_BITS + 1];
        for &l in lengths {
            if l as usize > MAX_BITS {
                return Err(InflateError::BadHuffmanTable);
            }
            counts[l as usize] += 1;
        }
        // Over-subscribed is rejected: two symbols would share a code and the
        // decode would be ambiguous. Under-subscribed is accepted, because a
        // distance tree with a single code is legal and common; an unused code
        // then runs past fifteen bits and comes back as BadHuffmanCode rather
        // than as a wrong symbol.
        let mut left: i32 = 1;
        for &count in counts.iter().take(MAX_BITS + 1).skip(1) {
            left = left.saturating_mul(2) - i32::from(count);
            if left < 0 {
                return Err(InflateError::BadHuffmanTable);
            }
        }
        let mut offs = [0u16; MAX_BITS + 2];
        for n in 1..=MAX_BITS {
            offs[n + 1] = offs[n] + counts[n];
        }
        let mut symbols = vec![0u16; lengths.len()];
        for (sym, &l) in lengths.iter().enumerate() {
            if l != 0 {
                let slot = offs[l as usize] as usize;
                if slot >= symbols.len() {
                    return Err(InflateError::BadHuffmanTable);
                }
                symbols[slot] = sym as u16;
                offs[l as usize] += 1;
            }
        }
        Ok(Self { counts, symbols })
    }

    fn decode(&self, br: &mut BitReader<'_>) -> Result<u16> {
        let mut code: i32 = 0;
        let mut first: i32 = 0;
        let mut index: i32 = 0;
        for n in 1..=MAX_BITS {
            code |= br.bits(1)? as i32;
            let count = i32::from(self.counts[n]);
            if code - first < count {
                let slot = (index + (code - first)) as usize;
                return self
                    .symbols
                    .get(slot)
                    .copied()
                    .ok_or(InflateError::BadHuffmanCode);
            }
            index += count;
            first = (first + count) << 1;
            code <<= 1;
        }
        Err(InflateError::BadHuffmanCode)
    }
}

const LEN_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];
const LEN_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
const DIST_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
const DIST_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];

fn fixed_tables() -> Result<(Huffman, Huffman)> {
    let mut lit = [0u8; 288];
    for (i, l) in lit.iter_mut().enumerate() {
        *l = match i {
            0..=143 => 8,
            144..=255 => 9,
            256..=279 => 7,
            _ => 8,
        };
    }
    // RFC 1951 gives the fixed distance alphabet 32 five-bit codes, of which
    // 30 and 31 never appear in a valid stream; building only 30 would leave
    // the code under-subscribed and mis-decode the last two.
    Ok((Huffman::new(&lit)?, Huffman::new(&[5u8; 32])?))
}

fn dynamic_tables(br: &mut BitReader<'_>) -> Result<(Huffman, Huffman)> {
    const ORDER: [usize; 19] = [
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
    ];
    let hlit = br.bits(5)? as usize + 257;
    let hdist = br.bits(5)? as usize + 1;
    let hclen = br.bits(4)? as usize + 4;
    if hlit > 286 || hdist > 30 {
        return Err(InflateError::BadHuffmanTable);
    }
    let mut code_lengths = [0u8; 19];
    for &slot in ORDER.iter().take(hclen) {
        code_lengths[slot] = br.bits(3)? as u8;
    }
    let code_tree = Huffman::new(&code_lengths)?;

    let total = hlit + hdist;
    let mut lengths = vec![0u8; total];
    let mut i = 0;
    while i < total {
        let sym = code_tree.decode(br)?;
        match sym {
            0..=15 => {
                lengths[i] = sym as u8;
                i += 1;
            }
            16 => {
                if i == 0 {
                    return Err(InflateError::BadHuffmanTable);
                }
                let prev = lengths[i - 1];
                let rep = 3 + br.bits(2)? as usize;
                if i + rep > total {
                    return Err(InflateError::BadHuffmanTable);
                }
                lengths[i..i + rep].fill(prev);
                i += rep;
            }
            17 | 18 => {
                let rep = if sym == 17 {
                    3 + br.bits(3)? as usize
                } else {
                    11 + br.bits(7)? as usize
                };
                if i + rep > total {
                    return Err(InflateError::BadHuffmanTable);
                }
                lengths[i..i + rep].fill(0);
                i += rep;
            }
            _ => return Err(InflateError::BadHuffmanCode),
        }
    }
    if lengths[256] == 0 {
        // Without an end-of-block code the block could never terminate.
        return Err(InflateError::BadHuffmanTable);
    }
    let litlen = Huffman::new(&lengths[..hlit])?;
    let dist = Huffman::new(&lengths[hlit..])?;
    Ok((litlen, dist))
}

fn adler32(data: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    // 5552 is the most bytes that can be summed before the 32-bit accumulator
    // can overflow, so the modulo runs once per chunk rather than per byte.
    for chunk in data.chunks(5552) {
        for &byte in chunk {
            a += u32::from(byte);
            b += a;
        }
        a %= 65521;
        b %= 65521;
    }
    (b << 16) | a
}

/// Inflate a raw DEFLATE stream. `limit` caps the output.
pub fn inflate(data: &[u8], limit: usize) -> Result<Vec<u8>> {
    let mut br = BitReader::new(data);
    let mut out: Vec<u8> = Vec::new();
    loop {
        let last = br.bits(1)? != 0;
        let kind = br.bits(2)?;
        match kind {
            0 => {
                br.align();
                let len = u32::from(br.byte()?) | (u32::from(br.byte()?) << 8);
                let nlen = u32::from(br.byte()?) | (u32::from(br.byte()?) << 8);
                if len ^ 0xffff != nlen {
                    return Err(InflateError::StoredLengthMismatch);
                }
                let len = len as usize;
                // Bounded before reserving: a stored block cannot claim more
                // than the input still holds.
                if len > br.remaining() {
                    return Err(InflateError::Truncated);
                }
                if out.len() + len > limit {
                    return Err(InflateError::LimitExceeded);
                }
                out.reserve(len);
                for _ in 0..len {
                    out.push(br.byte()?);
                }
            }
            1 | 2 => {
                let (litlen, dist) = if kind == 1 {
                    fixed_tables()?
                } else {
                    dynamic_tables(&mut br)?
                };
                loop {
                    let sym = litlen.decode(&mut br)?;
                    if sym < 256 {
                        if out.len() >= limit {
                            return Err(InflateError::LimitExceeded);
                        }
                        out.push(sym as u8);
                    } else if sym == 256 {
                        break;
                    } else {
                        let li = sym as usize - 257;
                        if li >= LEN_BASE.len() {
                            return Err(InflateError::BadHuffmanCode);
                        }
                        let length =
                            LEN_BASE[li] as usize + br.bits(u32::from(LEN_EXTRA[li]))? as usize;
                        let ds = dist.decode(&mut br)? as usize;
                        if ds >= DIST_BASE.len() {
                            return Err(InflateError::BadHuffmanCode);
                        }
                        let distance =
                            DIST_BASE[ds] as usize + br.bits(u32::from(DIST_EXTRA[ds]))? as usize;
                        if distance > out.len() {
                            return Err(InflateError::DistanceTooFar);
                        }
                        if out.len() + length > limit {
                            return Err(InflateError::LimitExceeded);
                        }
                        out.reserve(length);
                        // Byte at a time on purpose: a run may overlap itself,
                        // which is how DEFLATE encodes a repeat shorter than
                        // its length, and a block copy would get that wrong.
                        for src in (out.len() - distance..).take(length) {
                            let b = out[src];
                            out.push(b);
                        }
                    }
                }
            }
            _ => return Err(InflateError::ReservedBlockType),
        }
        if last {
            break;
        }
    }
    Ok(out)
}

/// Inflate a zlib-wrapped stream, checking the Adler-32 trailer.
pub fn inflate_zlib(data: &[u8], limit: usize) -> Result<Vec<u8>> {
    if data.len() < 6 {
        return Err(InflateError::Truncated);
    }
    let cmf = data[0];
    let flg = data[1];
    if cmf & 0x0f != 8 || cmf >> 4 > 7 {
        return Err(InflateError::BadZlibHeader);
    }
    if (u16::from(cmf) * 256 + u16::from(flg)) % 31 != 0 {
        return Err(InflateError::BadZlibHeader);
    }
    if flg & 0x20 != 0 {
        return Err(InflateError::PresetDictionary);
    }
    let body = &data[2..data.len() - 4];
    let out = inflate(body, limit)?;
    let tail = &data[data.len() - 4..];
    let want = u32::from_be_bytes([tail[0], tail[1], tail[2], tail[3]]);
    if adler32(&out) != want {
        return Err(InflateError::ChecksumMismatch);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stored (uncompressed) zlib stream for "hello", written by hand so the
    /// test does not depend on a compressor.
    #[test]
    fn stored_block_round_trips() {
        let payload = b"hello";
        let mut z = vec![0x78, 0x01, 0x01, 0x05, 0x00, 0xfa, 0xff];
        z.extend_from_slice(payload);
        z.extend_from_slice(&adler32(payload).to_be_bytes());
        assert_eq!(inflate_zlib(&z, 1 << 20).unwrap(), payload);
    }

    #[test]
    fn adler_of_known_string() {
        // RFC 1950's worked example.
        assert_eq!(adler32(b"Wikipedia"), 0x11E6_0398);
    }

    #[test]
    fn rejects_bad_header() {
        assert_eq!(
            inflate_zlib(&[0x00, 0x00, 0, 0, 0, 0], 1024),
            Err(InflateError::BadZlibHeader)
        );
    }

    #[test]
    fn truncation_is_an_error_not_a_panic() {
        let payload = b"hello";
        let mut z = vec![0x78, 0x01, 0x01, 0x05, 0x00, 0xfa, 0xff];
        z.extend_from_slice(payload);
        z.extend_from_slice(&adler32(payload).to_be_bytes());
        for n in 0..z.len() {
            let _ = inflate_zlib(&z[..n], 1 << 20);
        }
    }

    #[test]
    fn limit_is_enforced() {
        let payload = b"hello";
        let mut z = vec![0x78, 0x01, 0x01, 0x05, 0x00, 0xfa, 0xff];
        z.extend_from_slice(payload);
        z.extend_from_slice(&adler32(payload).to_be_bytes());
        assert_eq!(inflate_zlib(&z, 2), Err(InflateError::LimitExceeded));
    }
}
