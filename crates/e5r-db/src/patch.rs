//! Patch sets: byte edits that carry the bytes they expect to overwrite.
//!
//! "Write 90 at 4011a2" is neither auditable nor safe: applied to a binary it
//! was not made against it corrupts the file and says nothing. Every edit here
//! records the bytes it expects to find, so the wrong binary is a reported
//! conflict instead of a wreck, and recording them is also what makes a patch
//! set invertible.
//!
//! Edits are anchored by content plus an offset, exactly as annotations are,
//! so a patch made before a relink still lands on the right instruction; the
//! result says which layer matched rather than pretending an address hit is as
//! good as a content hit. The file is sorted by content id and merges under
//! the same union rule as the annotation log.

use std::fmt;
use std::fmt::Write as _;

use e5r_core::{Addr, Error, Result};

use crate::anchor::{Anchor, AnchorIndex, Fnv, Resolution};

/// Magic on the first line.
const TAG: &str = "e5r-patches";
/// On-disk format version. A reader refuses a version it does not know.
const VERSION: u32 = 1;

/// One byte edit: where it goes, what must be there, and what to write.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    /// Where it applies, anchored by content with an offset inside.
    pub target: Anchor,
    /// What the image must hold for this to be the patch it claims to be.
    pub expect: Vec<u8>,
    /// What to write. Always as long as `expect`: a different length would
    /// move every byte after it and invalidate the rest of the patch set.
    pub replace: Vec<u8>,
    /// Who made it.
    pub who: String,
    /// Why, in one line.
    pub note: String,
}

impl Edit {
    /// An edit on an anchored location.
    pub fn new(target: Anchor, expect: Vec<u8>, replace: Vec<u8>) -> Result<Edit> {
        if expect.is_empty() {
            return Err(Error::inconsistent("a patch edit writes no bytes"));
        }
        if expect.len() != replace.len() {
            return Err(Error::inconsistent(format!(
                "edit at {} replaces {} bytes with {}; an in-place patch cannot change length",
                target.target(),
                expect.len(),
                replace.len()
            )));
        }
        Ok(Edit {
            target,
            expect,
            replace,
            who: String::new(),
            note: String::new(),
        })
    }

    /// An edit on a bare address, for a location no anchor covers.
    pub fn at(addr: Addr, expect: Vec<u8>, replace: Vec<u8>) -> Result<Edit> {
        let target = Anchor {
            shape: 0,
            bytes: 0,
            insns: 0,
            abs: addr,
            offset: 0,
        };
        Edit::new(target, expect, replace)
    }

    /// Attribute it.
    pub fn by(self, who: &str) -> Edit {
        Edit {
            who: who.to_string(),
            ..self
        }
    }

    /// Explain it.
    pub fn noted(self, note: &str) -> Edit {
        Edit {
            note: note.to_string(),
            ..self
        }
    }

    /// The address recorded when the edit was made.
    pub fn addr(&self) -> Addr {
        self.target.target()
    }

    /// The same edit backwards.
    pub fn inverse(&self) -> Edit {
        Edit {
            target: self.target,
            expect: self.replace.clone(),
            replace: self.expect.clone(),
            who: self.who.clone(),
            note: self.note.clone(),
        }
    }

    /// Content id: the sort key that scatters new lines through the file.
    pub fn id(&self) -> u64 {
        let mut h = Fnv::new();
        let (shape, bytes, insns, offset) = self.target.identity();
        h.u64(shape);
        h.u64(bytes);
        h.u64(insns as u64);
        h.u64(offset as u64);
        h.u64(self.target.abs.get());
        // Domain separators, so the fields cannot run into each other.
        h.byte(0xff);
        h.slice(&self.expect);
        h.byte(0xfe);
        h.slice(&self.replace);
        h.byte(0xfd);
        h.slice(self.who.as_bytes());
        h.byte(0xfc);
        h.slice(self.note.as_bytes());
        h.finish()
    }

    /// True when the edit carries a content anchor rather than an address
    /// alone; a zeroed anchor would match whatever happened to hash to zero.
    fn is_anchored(&self) -> bool {
        self.target.shape != 0 || self.target.bytes != 0
    }
}

/// One edit placed on an image, before anything is written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    /// Which edit, by index into the patch set.
    pub edit: usize,
    /// Where it lands in this image.
    pub addr: Addr,
    /// What is there now.
    pub before: Vec<u8>,
    /// What would be there after.
    pub after: Vec<u8>,
    /// How the location was found.
    pub resolution: Resolution,
}

/// What applying a patch set did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Applied {
    /// Every change made, in address order.
    pub changes: Vec<Change>,
    /// How many bytes were written.
    pub bytes: usize,
}

impl Applied {
    /// True when every edit landed on a match stronger than the address.
    pub fn is_confident(&self) -> bool {
        self.changes.iter().all(|c| c.resolution.is_confident())
    }
}

/// Why a patch set would not apply. Nothing is ever written when one is
/// returned: the whole set lands or none of it does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conflict {
    /// The image does not hold what the edit was made against.
    Mismatch {
        /// Which edit, by index into the patch set.
        edit: usize,
        /// Where it was checked.
        addr: Addr,
        /// What the patch expected there.
        expected: Vec<u8>,
        /// What is actually there.
        found: Vec<u8>,
    },
    /// The edit lands outside the image it was given.
    OutOfRange {
        /// Which edit.
        edit: usize,
        /// Where it wanted to write.
        addr: Addr,
        /// How many bytes.
        len: usize,
        /// How big the image is.
        image: usize,
    },
    /// Two edits write the same byte, so the result would depend on order.
    Overlap {
        /// The earlier edit.
        first: usize,
        /// The one that runs into it.
        second: usize,
        /// Where they meet.
        addr: Addr,
    },
}

impl fmt::Display for Conflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Conflict::Mismatch {
                edit,
                addr,
                expected,
                found,
            } => write!(
                f,
                "edit {edit} at {addr} expected {} but found {}; this patch was made against a \
                 different binary",
                hex(expected),
                hex(found)
            ),
            Conflict::OutOfRange {
                edit,
                addr,
                len,
                image,
            } => write!(
                f,
                "edit {edit} writes {len} bytes at {addr}, which is outside the {image}-byte image"
            ),
            Conflict::Overlap {
                first,
                second,
                addr,
            } => write!(f, "edits {first} and {second} both write {addr}"),
        }
    }
}

impl std::error::Error for Conflict {}

/// A named set of edits, applied and reverted as a unit.
#[derive(Debug, Clone, Default)]
pub struct Patch {
    /// Sorted by content id, which is the on-disk order.
    edits: Vec<Edit>,
    /// What the set is called.
    pub name: String,
    /// The binary it was made against, as a hex digest, when known.
    pub binary: Option<String>,
}

impl Patch {
    /// An empty set.
    pub fn new(name: &str) -> Patch {
        Patch {
            edits: Vec::new(),
            name: name.to_string(),
            binary: None,
        }
    }

    /// How many edits it holds.
    pub fn len(&self) -> usize {
        self.edits.len()
    }

    /// True when it holds none.
    pub fn is_empty(&self) -> bool {
        self.edits.is_empty()
    }

    /// Every edit, in file order.
    pub fn edits(&self) -> &[Edit] {
        &self.edits
    }

    /// Add an edit, keeping the file order. A duplicate is dropped, because
    /// the same edit twice would be an overlap with itself.
    pub fn push(&mut self, edit: Edit) {
        let id = edit.id();
        let at = self.edits.partition_point(|e| e.id() < id);
        if self.edits.get(at) == Some(&edit) {
            return;
        }
        self.edits.insert(at, edit);
    }

    /// Capture an edit from the image, so `expect` cannot be typed wrong.
    ///
    /// `base` is the address the first byte of `image` is loaded at.
    pub fn record(
        &mut self,
        target: Anchor,
        image: &[u8],
        base: Addr,
        replace: Vec<u8>,
    ) -> Result<()> {
        let addr = target.target();
        let off = base
            .distance_to(addr)
            .and_then(|d| usize::try_from(d).ok())
            .ok_or(Error::Unmapped { addr })?;
        let end = off
            .checked_add(replace.len())
            .filter(|e| *e <= image.len())
            .ok_or(Error::OutOfBounds {
                what: "patch edit",
                offset: off as u64,
                len: replace.len() as u64,
                available: image.len() as u64,
            })?;
        self.push(Edit::new(target, image[off..end].to_vec(), replace)?);
        Ok(())
    }

    /// What would change, without writing anything.
    ///
    /// `base` is the address the first byte of `image` is loaded at, and
    /// `index` anchors the edits against this image; without one every edit
    /// falls back to the address it was recorded at.
    pub fn preview(
        &self,
        image: &[u8],
        base: Addr,
        index: Option<&AnchorIndex>,
    ) -> std::result::Result<Vec<Change>, Conflict> {
        let mut changes: Vec<Change> = Vec::with_capacity(self.edits.len());
        for (n, e) in self.edits.iter().enumerate() {
            let (addr, resolution) = place(e, index);
            let out_of_range = || Conflict::OutOfRange {
                edit: n,
                addr,
                len: e.expect.len(),
                image: image.len(),
            };
            let off = base
                .distance_to(addr)
                .and_then(|d| usize::try_from(d).ok())
                .ok_or_else(out_of_range)?;
            let end = off
                .checked_add(e.expect.len())
                .filter(|end| *end <= image.len())
                .ok_or_else(out_of_range)?;
            let found = &image[off..end];
            if found != e.expect {
                return Err(Conflict::Mismatch {
                    edit: n,
                    addr,
                    expected: e.expect.clone(),
                    found: found.to_vec(),
                });
            }
            changes.push(Change {
                edit: n,
                addr,
                before: found.to_vec(),
                after: e.replace.clone(),
                resolution,
            });
        }
        changes.sort_by_key(|c| (c.addr, c.edit));
        for w in changes.windows(2) {
            let end = w[0].addr.get().saturating_add(w[0].before.len() as u64);
            if end > w[1].addr.get() {
                return Err(Conflict::Overlap {
                    first: w[0].edit,
                    second: w[1].edit,
                    addr: w[1].addr,
                });
            }
        }
        Ok(changes)
    }

    /// Apply every edit, or none of them.
    pub fn apply(
        &self,
        image: &mut [u8],
        base: Addr,
        index: Option<&AnchorIndex>,
    ) -> std::result::Result<Applied, Conflict> {
        let changes = self.preview(image, base, index)?;
        let mut bytes = 0;
        for c in &changes {
            // The preview proved the range and the expected bytes, so this
            // cannot be the write that discovers a problem half way through.
            let off = base.distance_to(c.addr).unwrap_or(0) as usize;
            image[off..off + c.after.len()].copy_from_slice(&c.after);
            bytes += c.after.len();
        }
        Ok(Applied { changes, bytes })
    }

    /// The patch set that undoes this one.
    ///
    /// The anchors are kept as they are: against an image this patch has
    /// already been applied to their byte fingerprint no longer matches, so
    /// the inverse resolves by shape or by address, which is exactly what the
    /// resolution in the result reports.
    pub fn revert(&self) -> Patch {
        let mut out = Patch::new(&self.name);
        out.binary = self.binary.clone();
        for e in &self.edits {
            out.push(e.inverse());
        }
        out
    }

    /// Merge another set in. The result does not depend on which side is
    /// `other`, so two branches converge.
    pub fn merge(&mut self, other: &Patch) {
        for e in &other.edits {
            self.push(e.clone());
        }
    }

    /// Serialize, sorted by content id so new lines scatter through the file.
    pub fn to_text(&self) -> String {
        let mut s = String::with_capacity(128 + self.edits.len() * 96);
        let _ = writeln!(s, "{TAG} {VERSION}");
        let _ = writeln!(s, "name {}", quote(&self.name));
        if let Some(b) = &self.binary {
            let _ = writeln!(s, "binary {b}");
        }
        let _ = writeln!(
            s,
            "# One edit per line, sorted by content id. Every edit records the bytes it"
        );
        let _ = writeln!(
            s,
            "# expects to overwrite, so applying to the wrong binary fails instead of"
        );
        let _ = writeln!(
            s,
            "# corrupting it. Order does not affect the result, so the union of two"
        );
        let _ = writeln!(s, "# branches is the correct merge:");
        let _ = writeln!(s, "#     *.e5r-patch merge=union");
        for e in &self.edits {
            let _ = writeln!(
                s,
                "edit shape={:016x} bytes={:016x} insns={} abs={:x} off={} expect={} replace={} \
                 by={} note={}",
                e.target.shape,
                e.target.bytes,
                e.target.insns,
                e.target.abs.get(),
                e.target.offset,
                hex(&e.expect),
                hex(&e.replace),
                quote(&e.who),
                quote(&e.note),
            );
        }
        s
    }

    /// Parse a serialized patch set.
    pub fn from_text(text: &str) -> Result<Patch> {
        let mut lines = text.lines();
        let header = lines.next().unwrap_or_default();
        let mut parts = header.split_whitespace();
        if parts.next() != Some(TAG) {
            return Err(Error::NotRecognized {
                expected: "e5r patch set",
            });
        }
        let version: u32 = parts
            .next()
            .and_then(|v| v.parse().ok())
            .ok_or(Error::BadField {
                field: "format version",
                value: 0,
                reason: "is missing from the header line",
            })?;
        if version > VERSION {
            return Err(Error::unsupported(format!(
                "patch format version {version}; this build knows {VERSION}"
            )));
        }

        let mut patch = Patch::new("");
        for (n, line) in lines.enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("name ") {
                patch.name = unquote(rest.trim()).ok_or_else(|| malformed(n, line))?;
                continue;
            }
            if let Some(rest) = line.strip_prefix("binary ") {
                patch.binary = Some(rest.trim().to_string());
                continue;
            }
            patch.push(parse_edit(line).ok_or_else(|| malformed(n, line))?);
        }
        Ok(patch)
    }
}

/// Where an edit lands in this image, and on what evidence.
fn place(e: &Edit, index: Option<&AnchorIndex>) -> (Addr, Resolution) {
    if e.is_anchored() {
        if let Some((found, how)) = index.and_then(|ix| ix.resolve(&e.target)) {
            return (found.target().wrapping_offset(e.target.offset as i64), how);
        }
    }
    (e.addr(), Resolution::Address)
}

fn malformed(n: usize, line: &str) -> Error {
    Error::inconsistent(format!("patch line {} is malformed: {line:?}", n + 2))
}

fn parse_edit(line: &str) -> Option<Edit> {
    let rest = line.strip_prefix("edit ")?;
    // The two free-text fields are quoted and last; the head is bare tokens,
    // so the first ` by="` in the line is the one that ends it.
    let head_end = rest.find(" by=\"")?;
    let (head, tail) = rest.split_at(head_end);
    let who_q = &tail[4..];
    let end = find_quote_end(who_q)?;
    let who = unquote(&who_q[..=end])?;
    let note = unquote(who_q[end + 1..].strip_prefix(" note=")?)?;

    let mut shape = None;
    let mut bytes = None;
    let mut insns = None;
    let mut abs = None;
    let mut offset = 0u32;
    let mut expect = None;
    let mut replace = None;
    for field in head.split_whitespace() {
        let (key, v) = field.split_once('=')?;
        match key {
            "shape" => shape = u64::from_str_radix(v, 16).ok(),
            "bytes" => bytes = u64::from_str_radix(v, 16).ok(),
            "insns" => insns = v.parse().ok(),
            "abs" => abs = u64::from_str_radix(v, 16).ok(),
            "off" => offset = v.parse().ok()?,
            "expect" => expect = unhex(v),
            "replace" => replace = unhex(v),
            _ => return None,
        }
    }
    let target = Anchor {
        shape: shape?,
        bytes: bytes?,
        insns: insns?,
        abs: Addr(abs?),
        offset,
    };
    Some(
        Edit::new(target, expect?, replace?)
            .ok()?
            .by(&who)
            .noted(&note),
    )
}

/// Lowercase hex, the form a hex editor shows.
fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for byte in b {
        let _ = write!(s, "{byte:02x}");
    }
    s
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if s.is_empty() || s.len() % 2 != 0 {
        return None;
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok())
        .collect()
}

/// Quote a value so it survives a round trip through a whitespace-split line.
fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn unquote(s: &str) -> Option<String> {
    let body = s.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            '"' => out.push('"'),
            '\\' => out.push('\\'),
            other => out.push(other),
        }
    }
    Some(out)
}

/// Index of the closing quote of a quoted value starting at index 0.
fn find_quote_end(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    let mut i = 1;
    while i < b.len() {
        match b[i] {
            b'\\' => i += 2,
            b'"' => return Some(i),
            _ => i += 1,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn anchor(shape: u64, bytes: u64, abs: u64) -> Anchor {
        Anchor {
            shape,
            bytes,
            insns: 4,
            abs: Addr(abs),
            offset: 0,
        }
    }

    fn edit(abs: u64, expect: &[u8], replace: &[u8]) -> Edit {
        Edit::new(
            anchor(abs ^ 0x51, abs ^ 0x77, abs),
            expect.to_vec(),
            replace.to_vec(),
        )
        .unwrap()
    }

    #[test]
    fn an_edit_cannot_change_the_length_of_the_image() {
        assert!(Edit::at(Addr(0x1000), vec![0x90], vec![0x90, 0x90]).is_err());
        assert!(Edit::at(Addr(0x1000), vec![], vec![]).is_err());
    }

    #[test]
    fn applying_to_the_wrong_bytes_changes_nothing() {
        let mut patch = Patch::new("nop the check");
        patch.push(edit(0x1000, &[0x74, 0x0c], &[0x90, 0x90]));
        patch.push(edit(0x1010, &[0xcc], &[0x90]));
        let mut image = vec![0u8; 0x20];
        image[0] = 0x74;
        image[1] = 0x0c;
        // One edit does not match, so neither is written.
        let e = patch.apply(&mut image, Addr(0x1000), None).unwrap_err();
        assert!(
            matches!(
                e,
                Conflict::Mismatch {
                    addr: Addr(0x1010),
                    ..
                }
            ),
            "{e}"
        );
        assert_eq!(image[0..2], [0x74, 0x0c]);
    }

    #[test]
    fn applying_then_reverting_restores_the_image() {
        let mut image: Vec<u8> = (0..64u8).collect();
        let original = image.clone();
        let mut patch = Patch::new("p");
        patch.push(edit(0x1004, &[4, 5, 6], &[0x90, 0x90, 0x90]));
        patch.push(edit(0x1020, &[32], &[0xcc]));
        let applied = patch.apply(&mut image, Addr(0x1000), None).unwrap();
        assert_eq!(applied.bytes, 4);
        assert_ne!(image, original);
        patch
            .revert()
            .apply(&mut image, Addr(0x1000), None)
            .unwrap();
        assert_eq!(image, original);
    }

    #[test]
    fn a_preview_writes_nothing() {
        let image: Vec<u8> = (0..16u8).collect();
        let mut patch = Patch::new("p");
        patch.push(edit(0x1002, &[2], &[0xff]));
        let changes = patch.preview(&image, Addr(0x1000), None).unwrap();
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].addr, Addr(0x1002));
        assert_eq!(changes[0].before, vec![2]);
        assert_eq!(changes[0].after, vec![0xff]);
        assert_eq!(image[2], 2);
    }

    #[test]
    fn overlapping_edits_are_refused_rather_than_ordered() {
        let mut image = vec![0u8; 16];
        let mut patch = Patch::new("p");
        patch.push(edit(0x1000, &[0, 0, 0, 0], &[1, 1, 1, 1]));
        patch.push(edit(0x1002, &[0, 0], &[2, 2]));
        let e = patch.apply(&mut image, Addr(0x1000), None).unwrap_err();
        assert!(matches!(e, Conflict::Overlap { .. }), "{e}");
        assert_eq!(image, vec![0u8; 16]);
    }

    #[test]
    fn an_edit_outside_the_image_is_a_conflict() {
        let mut image = vec![0u8; 4];
        let mut patch = Patch::new("p");
        patch.push(edit(0x2000, &[0], &[1]));
        let e = patch.apply(&mut image, Addr(0x1000), None).unwrap_err();
        assert!(matches!(e, Conflict::OutOfRange { .. }), "{e}");
    }

    #[test]
    fn the_text_form_round_trips() {
        let mut patch = Patch::new("skip the \"licence\" check");
        patch.binary = Some("fnv:1234".into());
        patch.push(
            edit(0x1000, &[0x74, 0x0c], &[0x90, 0x90])
                .by("alice")
                .noted("a note with spaces\nand a newline"),
        );
        patch.push(edit(0x1010, &[0xcc], &[0x90]).by("bob"));
        let text = patch.to_text();
        let back = Patch::from_text(&text).unwrap();
        assert_eq!(back.edits, patch.edits);
        assert_eq!(back.name, patch.name);
        assert_eq!(back.binary, patch.binary);
        assert_eq!(back.to_text(), text);
    }

    #[test]
    fn a_newer_format_version_is_refused_rather_than_guessed_at() {
        assert!(Patch::from_text(&format!("{TAG} 99\n")).is_err());
        assert!(Patch::from_text("something else\n").is_err());
        let e = Patch::from_text(&format!("{TAG} 1\nedit shape=zz\n"))
            .unwrap_err()
            .to_string();
        assert!(e.contains("line 2"), "{e}");
    }

    #[test]
    fn on_disk_order_is_by_content_so_appends_scatter() {
        let mut patch = Patch::new("p");
        for i in 0..64u64 {
            patch.push(edit(0x1000 + i * 8, &[i as u8], &[0x90]));
        }
        let ids: Vec<u64> = patch.edits().iter().map(|e| e.id()).collect();
        let mut sorted = ids.clone();
        sorted.sort_unstable();
        assert_eq!(ids, sorted);
    }

    #[test]
    fn merging_two_branches_converges() {
        let mut left = Patch::new("p");
        left.push(edit(0x1000, &[1], &[0x90]));
        let mut right = Patch::new("p");
        right.push(edit(0x2000, &[2], &[0x90]));
        let mut a = left.clone();
        a.merge(&right);
        let mut b = right.clone();
        b.merge(&left);
        assert_eq!(a.to_text(), b.to_text());
        assert_eq!(a.len(), 2);
        // The same edit from both sides is one edit, not two.
        a.merge(&left);
        assert_eq!(a.len(), 2);
    }

    #[test]
    fn an_address_only_edit_ignores_the_index() {
        // A zeroed anchor is not a fingerprint, so it must not be looked up.
        let a = anchor(0, 0, 0x1000);
        let ix = AnchorIndex::build([a]);
        let e = Edit::at(Addr(0x1004), vec![4], vec![0x90]).unwrap();
        let mut patch = Patch::new("p");
        patch.push(e);
        let image: Vec<u8> = (0..16u8).collect();
        let changes = patch.preview(&image, Addr(0x1000), Some(&ix)).unwrap();
        assert_eq!(changes[0].addr, Addr(0x1004));
        assert_eq!(changes[0].resolution, Resolution::Address);
    }

    #[test]
    fn recording_captures_what_is_there() {
        let image: Vec<u8> = (0..16u8).collect();
        let mut patch = Patch::new("p");
        patch
            .record(anchor(1, 2, 0x1004), &image, Addr(0x1000), vec![0x90])
            .unwrap();
        assert_eq!(patch.edits()[0].expect, vec![4]);
        assert!(
            patch
                .record(anchor(1, 2, 0x9000), &image, Addr(0x1000), vec![0x90])
                .is_err()
        );
    }
}
