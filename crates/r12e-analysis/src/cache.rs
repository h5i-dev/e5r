//! An on-disk cache of analysis results, keyed by content and options.
//!
//! Derived data, so it lives in the user's cache directory and never beside
//! the binary: `$XDG_CACHE_HOME/r12e` when that is set, `~/.cache/r12e`
//! otherwise. Nothing here is authoritative. Two rules outrank speed:
//!
//! 1. A key that does not match is a miss. There is no partial reuse, no
//!    "close enough", and no reading of one part of an entry whose other part
//!    was written by a different build.
//! 2. A corrupt or truncated file is a miss with a warning. It is never a
//!    panic and never a wrong answer, because a cache that can lie is worse
//!    than no cache at all.
//!
//! Each part of the analysis is a separate entry under its own key, so a run
//! that asked only for functions leaves a functions entry, and a later run
//! that also wants strings reuses the first and computes the second. The key
//! of a part covers exactly the inputs that determine it: the file's content
//! hash, the format version, and the options that part reads. Thread count is
//! deliberately absent, because the answer may not depend on it (gate G5).
//!
//! # The file format
//!
//! Hand rolled rather than serde, because the decoder has to survive hostile
//! bytes and every length in it needs to be checked against what is left of
//! the file. All integers are little endian.
//!
//! ```text
//! magic       8 bytes, "R12ECACH"
//! version     u32, FORMAT_VERSION
//! part        u8, which analysis part this is
//! key         16 bytes, the part key
//! length      u64, payload bytes
//! payload     length bytes
//! checksum    u64 over everything before it
//! ```
//!
//! The payload encodings are documented on the functions that write them.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// Bumped whenever a payload encoding changes. An old entry then fails the
/// version check and is a miss, which is the point: a stale decode that
/// happens to parse is exactly the wrong answer this cache must not give.
pub const FORMAT_VERSION: u32 = 1;

const MAGIC: &[u8; 8] = b"R12ECACH";
const HEADER_LEN: usize = 8 + 4 + 1 + 16 + 8;

/// Which analysis result an entry holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part {
    /// Functions, their graphs, and the no-return set.
    Functions,
    /// The cross reference index.
    Xrefs,
    /// Extracted strings.
    Strings,
}

impl Part {
    /// The byte that identifies the part inside a file.
    fn code(self) -> u8 {
        match self {
            Part::Functions => 1,
            Part::Xrefs => 2,
            Part::Strings => 3,
        }
    }

    /// The filename prefix, so a person can see what is in the directory.
    fn name(self) -> &'static str {
        match self {
            Part::Functions => "funcs",
            Part::Xrefs => "xrefs",
            Part::Strings => "strings",
        }
    }
}

/// A 128-bit hash of a file's bytes, the first half of every part key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContentHash([u8; 16]);

impl ContentHash {
    /// Hash a whole file image.
    pub fn of(data: &[u8]) -> ContentHash {
        ContentHash(hash128(data))
    }

    /// Fold in anything else that changed what was loaded.
    ///
    /// The object cannot say what load options produced it, and a run with
    /// `.eh_frame` reading turned off finds different functions in the same
    /// bytes. A caller that varies the load must mix that variation in here,
    /// or the two loads share a key and the second gets the first's answer.
    pub fn with(self, extra: &[u8]) -> ContentHash {
        let mut buf = Vec::with_capacity(16 + extra.len());
        buf.extend_from_slice(&self.0);
        buf.extend_from_slice(extra);
        ContentHash(hash128(&buf))
    }

    /// The raw bytes, for a caller that wants to key something of its own.
    pub fn bytes(&self) -> [u8; 16] {
        self.0
    }
}

/// The key of one cache entry: content, format version and the options that
/// part depends on, mixed into 128 bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Key([u8; 16]);

impl Key {
    /// Derive a part key from the content hash and the bytes that describe the
    /// options that part reads.
    pub fn derive(content: &ContentHash, part: Part, opts: &[u8]) -> Key {
        let mut buf = Vec::with_capacity(16 + 4 + 1 + opts.len());
        buf.extend_from_slice(&content.0);
        buf.extend_from_slice(&FORMAT_VERSION.to_le_bytes());
        buf.push(part.code());
        buf.extend_from_slice(opts);
        Key(hash128(&buf))
    }

    /// Lowercase hex, which is what the filename uses.
    pub fn hex(&self) -> String {
        let mut s = String::with_capacity(32);
        for b in self.0 {
            s.push(char::from_digit((b >> 4) as u32, 16).unwrap_or('0'));
            s.push(char::from_digit((b & 0xf) as u32, 16).unwrap_or('0'));
        }
        s
    }
}

/// What a lookup found.
#[derive(Debug)]
pub enum Lookup {
    /// A payload whose key, version and checksum all matched.
    Hit(Vec<u8>),
    /// Nothing usable, and nothing wrong: no file, or a file for another key.
    Miss,
    /// A file that exists and does not hold what it claims to. The caller
    /// treats this as a miss and reports the message.
    Corrupt(String),
}

/// A directory of cache entries.
#[derive(Debug, Clone)]
pub struct Cache {
    dir: PathBuf,
}

impl Cache {
    /// The conventional location, or `None` when neither `XDG_CACHE_HOME` nor
    /// `HOME` says where it is. Does not create anything: a cache that cannot
    /// be found is a miss, not an error.
    pub fn discover() -> Option<Cache> {
        let base = match std::env::var_os("XDG_CACHE_HOME") {
            Some(v) if !v.is_empty() => PathBuf::from(v),
            _ => PathBuf::from(std::env::var_os("HOME")?).join(".cache"),
        };
        Some(Cache {
            dir: base.join("r12e").join("analysis"),
        })
    }

    /// A cache in a directory the caller names, for tests and for `--cache-dir`.
    pub fn at(dir: impl Into<PathBuf>) -> Cache {
        Cache { dir: dir.into() }
    }

    /// Where entries are written.
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// The file one entry lives in.
    fn path(&self, part: Part, key: &Key) -> PathBuf {
        self.dir.join(format!("{}-{}.bin", part.name(), key.hex()))
    }

    /// Read one entry.
    ///
    /// Every failure short of a decoded, checksummed payload is a miss. The
    /// distinction between [`Lookup::Miss`] and [`Lookup::Corrupt`] is only
    /// about whether a person should be told.
    pub fn get(&self, part: Part, key: &Key) -> Lookup {
        let path = self.path(part, key);
        let bytes = match fs::read(&path) {
            Ok(b) => b,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Lookup::Miss,
            Err(e) => return Lookup::Corrupt(format!("cache read failed for {path:?}: {e}")),
        };
        match decode_entry(&bytes, part, key) {
            Ok(Some(payload)) => Lookup::Hit(payload),
            Ok(None) => Lookup::Miss,
            Err(why) => Lookup::Corrupt(format!("ignoring damaged cache file {path:?}: {why}")),
        }
    }

    /// Write one entry, replacing whatever was there.
    ///
    /// Written to a temporary name and renamed, so a reader never sees half a
    /// file and an interrupted write leaves the previous entry intact. The
    /// temporary carries the process id because two r12e runs on the same
    /// binary are a normal thing to do.
    pub fn put(&self, part: Part, key: &Key, payload: &[u8]) -> io::Result<()> {
        fs::create_dir_all(&self.dir)?;
        let final_path = self.path(part, key);
        let tmp = self.dir.join(format!(
            "{}-{}.{}.tmp",
            part.name(),
            key.hex(),
            std::process::id()
        ));
        let mut buf = Vec::with_capacity(HEADER_LEN + payload.len() + 8);
        buf.extend_from_slice(MAGIC);
        buf.extend_from_slice(&FORMAT_VERSION.to_le_bytes());
        buf.push(part.code());
        buf.extend_from_slice(&key.0);
        buf.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        buf.extend_from_slice(payload);
        let sum = hash64(&buf);
        buf.extend_from_slice(&sum.to_le_bytes());
        match fs::write(&tmp, &buf).and_then(|()| fs::rename(&tmp, &final_path)) {
            Ok(()) => Ok(()),
            Err(e) => {
                let _ = fs::remove_file(&tmp);
                Err(e)
            }
        }
    }

    /// Delete one entry. Used when a corrupt file is found, so the next run
    /// does not report the same damage again.
    pub fn remove(&self, part: Part, key: &Key) {
        let _ = fs::remove_file(self.path(part, key));
    }
}

/// Check the header and the checksum and hand back the payload.
///
/// `Ok(None)` is a file for a different key or version, which is ordinary.
/// `Err` is a file that claims to be this entry and is not intact.
fn decode_entry(bytes: &[u8], part: Part, key: &Key) -> Result<Option<Vec<u8>>, String> {
    if bytes.len() < HEADER_LEN + 8 {
        return Err(format!("{} bytes, shorter than a header", bytes.len()));
    }
    if &bytes[..8] != MAGIC {
        return Err("bad magic".to_string());
    }
    let version = u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
    if version != FORMAT_VERSION {
        return Ok(None);
    }
    if bytes[12] != part.code() {
        return Ok(None);
    }
    if bytes[13..29] != key.0 {
        return Ok(None);
    }
    let mut len = [0u8; 8];
    len.copy_from_slice(&bytes[29..37]);
    let len = u64::from_le_bytes(len);
    // The length is attacker-controlled in the sense that matters here: a
    // damaged file can claim any size, so it is checked against what the file
    // actually holds before anything is allocated.
    let Ok(len) = usize::try_from(len) else {
        return Err("payload length does not fit in memory".to_string());
    };
    let Some(end) = HEADER_LEN.checked_add(len) else {
        return Err("payload length overflows".to_string());
    };
    if bytes.len() != end + 8 {
        return Err(format!(
            "claims {len} payload bytes, file holds {}",
            bytes.len().saturating_sub(HEADER_LEN + 8)
        ));
    }
    let mut sum = [0u8; 8];
    sum.copy_from_slice(&bytes[end..end + 8]);
    if u64::from_le_bytes(sum) != hash64(&bytes[..end]) {
        return Err("checksum mismatch".to_string());
    }
    Ok(Some(bytes[HEADER_LEN..end].to_vec()))
}

/// A 64-bit mixing hash over eight bytes at a time.
///
/// Not cryptographic and not claimed to be: it keys a local cache and detects
/// damage, and both jobs need speed over an image that can be hundreds of
/// megabytes more than they need collision resistance against an adversary.
/// The multiply-xor-shift shape is the usual one; a byte-at-a-time FNV is
/// several times slower on a file this size, which is measurable on the very
/// binaries the cache exists for.
fn hash64_seeded(data: &[u8], seed: u64) -> u64 {
    const PRIME: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut h = seed ^ (data.len() as u64).wrapping_mul(PRIME);
    let mut chunks = data.chunks_exact(8);
    for c in &mut chunks {
        let w = u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
        h ^= w.wrapping_mul(PRIME).rotate_left(31);
        h = h
            .wrapping_mul(PRIME)
            .rotate_left(27)
            .wrapping_add(0x165667b1);
    }
    let mut tail = 0u64;
    for (i, b) in chunks.remainder().iter().enumerate() {
        tail |= (*b as u64) << (i * 8);
    }
    h ^= tail.wrapping_mul(PRIME);
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 29;
    h = h.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    h ^ (h >> 32)
}

/// The checksum, and half of a key.
fn hash64(data: &[u8]) -> u64 {
    hash64_seeded(data, 0x517c_c1b7_2722_0a95)
}

/// Two independent 64-bit hashes, so an accidental collision needs both to
/// agree. A local cache does not need more than that.
fn hash128(data: &[u8]) -> [u8; 16] {
    let a = hash64_seeded(data, 0x243f_6a88_85a3_08d3);
    let b = hash64_seeded(data, 0x13198a2e03707344);
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&a.to_le_bytes());
    out[8..].copy_from_slice(&b.to_le_bytes());
    out
}

/// A little-endian writer. Every encoder in this crate builds on it.
#[derive(Debug, Default)]
pub(crate) struct Enc {
    buf: Vec<u8>,
}

impl Enc {
    /// A writer with room reserved for what the caller expects to write.
    pub(crate) fn with_capacity(n: usize) -> Enc {
        Enc {
            buf: Vec::with_capacity(n),
        }
    }

    pub(crate) fn u8(&mut self, v: u8) {
        self.buf.push(v);
    }

    pub(crate) fn u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub(crate) fn u64(&mut self, v: u64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub(crate) fn bool(&mut self, v: bool) {
        self.buf.push(v as u8);
    }

    /// A length-prefixed string.
    pub(crate) fn str(&mut self, s: &str) {
        self.u32(s.len() as u32);
        self.buf.extend_from_slice(s.as_bytes());
    }

    /// An optional string: a flag, then the string when there is one.
    pub(crate) fn opt_str(&mut self, s: Option<&str>) {
        match s {
            Some(s) => {
                self.u8(1);
                self.str(s);
            }
            None => self.u8(0),
        }
    }

    pub(crate) fn finish(self) -> Vec<u8> {
        self.buf
    }
}

/// A little-endian reader over bytes that may be damaged.
///
/// Every read is checked and returns `None` past the end, so a decoder built
/// on it propagates a short read instead of panicking. Nothing here indexes a
/// slice directly, which is the property the corruption test exists to hold.
#[derive(Debug)]
pub(crate) struct Dec<'a> {
    buf: &'a [u8],
    at: usize,
}

impl<'a> Dec<'a> {
    pub(crate) fn new(buf: &'a [u8]) -> Dec<'a> {
        Dec { buf, at: 0 }
    }

    /// Bytes not yet read, which is the ceiling on any count the file claims.
    pub(crate) fn remaining(&self) -> usize {
        self.buf.len().saturating_sub(self.at)
    }

    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        let out = self.buf.get(self.at..end)?;
        self.at = end;
        Some(out)
    }

    pub(crate) fn u8(&mut self) -> Option<u8> {
        self.take(1).map(|b| b[0])
    }

    pub(crate) fn u32(&mut self) -> Option<u32> {
        let b = self.take(4)?;
        Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    pub(crate) fn u64(&mut self) -> Option<u64> {
        let b = self.take(8)?;
        Some(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    pub(crate) fn bool(&mut self) -> Option<bool> {
        match self.u8()? {
            0 => Some(false),
            1 => Some(true),
            // Anything else is damage, not a boolean.
            _ => None,
        }
    }

    pub(crate) fn str(&mut self) -> Option<String> {
        let n = self.u32()? as usize;
        let b = self.take(n)?;
        String::from_utf8(b.to_vec()).ok()
    }

    pub(crate) fn opt_str(&mut self) -> Option<Option<String>> {
        match self.u8()? {
            0 => Some(None),
            1 => Some(Some(self.str()?)),
            _ => None,
        }
    }

    /// A count the file claims, refused when it is larger than the bytes left
    /// could possibly encode. Without this a damaged length reserves gigabytes
    /// before the read that would have failed.
    pub(crate) fn count(&mut self, min_element_bytes: usize) -> Option<usize> {
        let n = usize::try_from(self.u64()?).ok()?;
        (n.saturating_mul(min_element_bytes.max(1)) <= self.remaining()).then_some(n)
    }
}
