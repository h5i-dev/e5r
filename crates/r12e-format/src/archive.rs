//! `ar` archives: a container of containers.
//!
//! A `.a` is a directory, not an image. It has no architecture, no entry point
//! and no memory map, so it cannot become an [`Object`]; what it has is a list
//! of members, each of which is a container in its own right, and a symbol
//! index mapping a name to the member that defines it. That index is the thing
//! worth having: "which object in `libc.a` defines `memcpy`" is a question the
//! archive answers directly and a linker asks constantly.
//!
//! So [`open`] is separate from [`crate::load`] rather than folded into it, and
//! [`crate::load`] refuses an archive with a message saying to open it as one.
//! The alternative, picking a member and pretending it was the file, would make
//! every later answer silently about the wrong bytes.
//!
//! Three dialects share the 60-byte header and disagree about names: GNU spells
//! a long name as an offset into a `//` member, BSD stores it in the member's
//! own data behind a `#1/` marker, and a plain archive has neither. All three
//! are read here, because the flavour is a property of the `ar` that wrote the
//! file and not of the platform it targets.

use r12e_core::{Caps, Error, Reader, Result};

use crate::{LoadOptions, Object};

/// The global header an archive starts with.
const MAGIC: &[u8; 8] = b"!<arch>\n";

/// GNU's thin archive: members name external files and carry no bytes here.
const THIN_MAGIC: &[u8; 8] = b"!<thin>\n";

/// One member header: sixteen bytes of name, five ASCII numbers, a two-byte
/// terminator. Fixed width, which is what makes the walk bounded.
const HEADER_LEN: u64 = 60;

/// Longest member name accepted from a long-name table, so an unterminated
/// table cannot become one enormous name.
const MAX_NAME: u64 = 1 << 12;

/// Which dialect wrote the archive. They differ only in how a long name and
/// the symbol index are spelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flavor {
    /// Names end in `/`, long ones live in a `//` member, index member is `/`.
    Gnu,
    /// Long names sit in the member data behind `#1/`, index is `__.SYMDEF`.
    Bsd,
    /// Neither marker appeared, which a short-named archive is allowed to do.
    Plain,
}

impl Flavor {
    /// The name used in output and JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Flavor::Gnu => "gnu",
            Flavor::Bsd => "bsd",
            Flavor::Plain => "plain",
        }
    }
}

impl std::fmt::Display for Flavor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One archive member: a name and the bytes a caller can hand to [`crate::load`].
#[derive(Clone)]
pub struct Member<'a> {
    /// The member name with its dialect's decoration removed.
    pub name: String,
    /// File offset of the member's 60-byte header, which is what the symbol
    /// index points at.
    pub header_offset: u64,
    /// File offset of the member's first data byte.
    pub offset: u64,
    /// Size of the data, after any BSD long name in front of it.
    pub size: u64,
    /// Modification time, seconds since the epoch, zero when unset.
    pub mtime: u64,
    /// Owner, zero when unset.
    pub uid: u32,
    /// Group, zero when unset.
    pub gid: u32,
    /// Permission bits, as an octal field in the header.
    pub mode: u32,
    /// True for a member whose bytes are not in this file: a thin archive
    /// records the name and the size and leaves the content on disk.
    pub thin: bool,
    data: &'a [u8],
}

impl<'a> Member<'a> {
    /// The member's bytes, empty for a thin archive's external member.
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// True when this member is bookkeeping rather than an object: the symbol
    /// index or the long-name table.
    pub fn is_special(&self) -> bool {
        matches!(self.name.as_str(), "/" | "//" | "/SYM64/") || self.name.starts_with("__.SYMDEF")
    }
}

impl std::fmt::Debug for Member<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The bytes are omitted on purpose: a debug print of a member is a
        // debug print of an object file.
        f.debug_struct("Member")
            .field("name", &self.name)
            .field("offset", &self.offset)
            .field("size", &self.size)
            .field("thin", &self.thin)
            .finish()
    }
}

/// One entry of the symbol index: a name and the member that defines it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexEntry {
    /// The symbol, as the index spells it, still mangled.
    pub name: String,
    /// Header offset the index recorded, kept even when it matched no member
    /// so a broken index is visible rather than dropped.
    pub header_offset: u64,
    /// Index into [`Archive::members`], absent when the offset named none.
    pub member: Option<usize>,
}

/// A parsed archive.
#[derive(Debug, Clone)]
pub struct Archive<'a> {
    /// Which dialect wrote it.
    pub flavor: Flavor,
    /// True when the members' bytes live in separate files.
    pub thin: bool,
    /// Members in file order, bookkeeping members included, so an offset in
    /// the symbol index resolves to the same numbering `ar t` prints minus the
    /// special entries.
    pub members: Vec<Member<'a>>,
    /// The symbol index, in index order. Empty when the archive has none,
    /// which is legal and means a linker has to scan every member.
    pub index: Vec<IndexEntry>,
    /// Problems that did not stop the parse. A damaged archive still lists the
    /// members before the damage.
    pub warnings: Vec<String>,
}

impl<'a> Archive<'a> {
    /// The first member with this name.
    pub fn member(&self, name: &str) -> Option<&Member<'a>> {
        self.members.iter().find(|m| m.name == name)
    }

    /// Members that are objects rather than bookkeeping, with their index. A
    /// thin archive's members are listed too: they are objects, they are just
    /// not in this file, and [`Archive::load_member`] says so.
    pub fn objects(&self) -> impl Iterator<Item = (usize, &Member<'a>)> {
        self.members
            .iter()
            .enumerate()
            .filter(|(_, m)| !m.is_special())
    }

    /// Every member the symbol index says defines `symbol`. A well-formed
    /// archive names one; a plural answer is itself worth reporting.
    pub fn definers(&self, symbol: &str) -> Vec<usize> {
        let mut out: Vec<usize> = self
            .index
            .iter()
            .filter(|e| e.name == symbol)
            .filter_map(|e| e.member)
            .collect();
        out.dedup();
        out
    }

    /// Symbols the index attributes to one member.
    pub fn symbols_of(&self, member: usize) -> Vec<&str> {
        self.index
            .iter()
            .filter(|e| e.member == Some(member))
            .map(|e| e.name.as_str())
            .collect()
    }

    /// Load one member through the ordinary container probe.
    pub fn load_member(&self, member: usize, opts: &LoadOptions) -> Result<Object> {
        let m = self.members.get(member).ok_or(Error::BadField {
            field: "archive member index",
            value: member as u64,
            reason: "is past the end of the member list",
        })?;
        if m.thin {
            return Err(Error::unsupported(format!(
                "thin archive member {}: its bytes are in a separate file",
                m.name
            )));
        }
        crate::load(m.data, opts)
    }
}

/// True when the bytes begin with either archive magic.
pub fn is_archive(data: &[u8]) -> bool {
    data.len() >= 8 && (&data[..8] == MAGIC || &data[..8] == THIN_MAGIC)
}

/// The error [`crate::load`] returns for an archive, so a `.a` reaching the
/// single-object path says what it is instead of "not a recognized container".
pub fn refuse_in_load(data: &[u8]) -> Result<()> {
    if is_archive(data) {
        return Err(Error::unsupported(
            "an `ar` archive, which holds objects rather than being one; open it with \
             archive::open and load a member",
        ));
    }
    Ok(())
}

/// Parse an archive with the default caps.
pub fn open(data: &[u8]) -> Result<Archive<'_>> {
    open_with(data, &Caps::default())
}

/// A member as the walk found it, before names are resolved. The name field is
/// kept raw because resolving it needs the `//` member, which may come later.
struct Raw<'a> {
    name_field: [u8; 16],
    header_offset: u64,
    offset: u64,
    size: u64,
    mtime: u64,
    uid: u32,
    gid: u32,
    mode: u32,
    thin: bool,
    data: &'a [u8],
}

/// Parse an archive, bounding every count against `caps`.
pub fn open_with<'a>(data: &'a [u8], caps: &Caps) -> Result<Archive<'a>> {
    if !is_archive(data) {
        return Err(Error::NotRecognized {
            expected: "ar archive",
        });
    }
    let thin = data[..8] == *THIN_MAGIC;
    let r = Reader::le(data);
    let end = data.len() as u64;
    let mut warnings = Vec::new();
    let mut raws: Vec<Raw<'a>> = Vec::new();
    let mut pos = 8u64;

    // Every member costs a 60-byte header, so the file length already bounds
    // this loop; the cap turns a merely huge archive into a typed error.
    while pos + HEADER_LEN <= end {
        caps.check("archive members", raws.len() as u64 + 1, caps.sections)?;
        let mut h = r.slice_at("member header", pos, HEADER_LEN)?;
        let name_field: [u8; 16] = h.array("member name")?;
        let mtime = ascii_num(h.bytes("member mtime", 12)?, 10).unwrap_or(0);
        let uid = ascii_num(h.bytes("member uid", 6)?, 10).unwrap_or(0) as u32;
        let gid = ascii_num(h.bytes("member gid", 6)?, 10).unwrap_or(0) as u32;
        let mode = ascii_num(h.bytes("member mode", 8)?, 8).unwrap_or(0) as u32;
        let size = ascii_num(h.bytes("member size", 10)?, 10);
        let terminator = h.bytes("member header terminator", 2)?;
        if terminator != b"`\n" {
            warnings.push(format!(
                "member header at {pos:#x} does not end in the `\\n terminator; stopping there"
            ));
            break;
        }
        let Some(size) = size else {
            warnings.push(format!(
                "member header at {pos:#x} has an unreadable size field; stopping there"
            ));
            break;
        };
        let body = pos + HEADER_LEN;
        // A thin archive still stores its index and long-name table inline;
        // only the members that name external files have no bytes.
        let inline = !thin || is_bookkeeping(&name_field);
        let stored = if inline { size } else { 0 };
        let data_slice = match r.bytes_at("member data", body, stored) {
            Ok(b) => b,
            Err(_) => {
                warnings.push(format!(
                    "member at {pos:#x} claims {size} bytes, which runs past the end of the file"
                ));
                break;
            }
        };
        raws.push(Raw {
            name_field,
            header_offset: pos,
            offset: body,
            size: stored,
            mtime,
            uid,
            gid,
            mode,
            thin: !inline,
            data: data_slice,
        });
        // Members are two-byte aligned, the padding being a newline.
        pos = body + stored + (stored & 1);
    }

    if pos < end && pos + HEADER_LEN > end && end - pos > 1 {
        warnings.push(format!(
            "{} trailing bytes after the last member are too few for a header",
            end - pos
        ));
    }

    let long_names = raws
        .iter()
        .find(|m| trim_field(&m.name_field) == b"//")
        .map(|m| m.data)
        .unwrap_or(&[]);

    let mut flavor = Flavor::Plain;
    let mut members: Vec<Member<'a>> = Vec::with_capacity(raws.len());
    for raw in &raws {
        let (mut name, skip) =
            resolve_name(&raw.name_field, long_names, &mut flavor, &mut warnings);
        // A BSD long name is stored inside the member data and counted in the
        // member size, so the name is read from there and both move past it.
        let skip = skip.min(raw.size);
        if skip > 0 {
            let mut bytes = &raw.data[..skip as usize];
            // Padded to a multiple of eight with NULs, which are not the name.
            while let Some((&0, rest)) = bytes.split_last() {
                bytes = rest;
            }
            name = text(bytes);
        }
        members.push(Member {
            name,
            header_offset: raw.header_offset,
            offset: raw.offset + skip,
            size: raw.size - skip,
            mtime: raw.mtime,
            uid: raw.uid,
            gid: raw.gid,
            mode: raw.mode,
            thin: raw.thin,
            data: &raw.data[skip as usize..],
        });
    }

    let index = read_index(&members, caps, &mut warnings)?;
    Ok(Archive {
        flavor,
        thin,
        members,
        index,
        warnings,
    })
}

/// True for the name fields that hold the archive's own tables.
fn is_bookkeeping(field: &[u8; 16]) -> bool {
    let t = trim_field(field);
    t == b"/" || t == b"//" || t == b"/SYM64/" || t.starts_with(b"__.SYMDEF")
}

/// Drop the trailing spaces the fixed-width header pads with.
fn trim_field(field: &[u8]) -> &[u8] {
    let mut end = field.len();
    while end > 0 && (field[end - 1] == b' ' || field[end - 1] == 0) {
        end -= 1;
    }
    &field[..end]
}

/// An ASCII number in a fixed-width field. Blank means unset, not zero-length
/// garbage, and a non-digit stops the parse rather than being skipped.
fn ascii_num(field: &[u8], radix: u32) -> Option<u64> {
    let t = trim_field(field);
    let first = t.iter().position(|&b| b != b' ')?;
    let t = &t[first..];
    let mut out: u64 = 0;
    for &b in t {
        let d = (b as char).to_digit(radix)?;
        out = out.checked_mul(radix as u64)?.checked_add(d as u64)?;
    }
    Some(out)
}

/// Resolve a raw name field, returning the name and how many data bytes the
/// name itself occupied.
fn resolve_name(
    field: &[u8; 16],
    long_names: &[u8],
    flavor: &mut Flavor,
    warnings: &mut Vec<String>,
) -> (String, u64) {
    let t = trim_field(field);
    if t == b"/" || t == b"//" || t == b"/SYM64/" {
        *flavor = Flavor::Gnu;
        return (text(t), 0);
    }
    if t.starts_with(b"__.SYMDEF") {
        *flavor = Flavor::Bsd;
        return (text(t), 0);
    }
    // GNU terminates a name with a slash so a trailing space can be part of
    // it. A thin archive writes both the slash and the long-name reference,
    // as `/17            /`, so the terminator comes off before anything else
    // is read.
    let t = if t.ends_with(b"/") {
        *flavor = Flavor::Gnu;
        trim_field(&t[..t.len() - 1])
    } else {
        t
    };
    // BSD: `#1/N` says the next N data bytes are the name.
    if let Some(rest) = t.strip_prefix(b"#1/") {
        if let Some(n) = ascii_num(rest, 10) {
            *flavor = Flavor::Bsd;
            return (String::new(), n.min(MAX_NAME));
        }
    }
    // GNU: `/N` is an offset into the `//` member.
    if let Some(rest) = t.strip_prefix(b"/") {
        if let Some(off) = ascii_num(rest, 10) {
            *flavor = Flavor::Gnu;
            return match long_name_at(long_names, off) {
                Some(n) => (n, 0),
                None => {
                    warnings.push(format!(
                        "member name points at offset {off} of the long-name table, which \
                         is {} bytes",
                        long_names.len()
                    ));
                    (format!("/{off}"), 0)
                }
            };
        }
    }
    (text(t), 0)
}

/// A name from the `//` member, terminated by `/\n` or a NUL.
fn long_name_at(table: &[u8], offset: u64) -> Option<String> {
    let start = usize::try_from(offset).ok()?;
    if start >= table.len() {
        return None;
    }
    let limit = (start + MAX_NAME as usize).min(table.len());
    let slice = &table[start..limit];
    let n = slice
        .iter()
        .position(|&b| b == b'/' || b == 0 || b == b'\n')
        .unwrap_or(slice.len());
    Some(text(&slice[..n]))
}

/// Bytes to a name. Archive names are not required to be UTF-8 and a lossy
/// name is better than refusing the member.
fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// Read whichever symbol index the archive carries, resolving each recorded
/// header offset to a member.
fn read_index(
    members: &[Member<'_>],
    caps: &Caps,
    warnings: &mut Vec<String>,
) -> Result<Vec<IndexEntry>> {
    let mut raw: Vec<(String, u64)> = Vec::new();
    for m in members {
        match m.name.as_str() {
            "/" => raw = gnu_index(m.data, false, caps, warnings)?,
            "/SYM64/" => raw = gnu_index(m.data, true, caps, warnings)?,
            n if n.starts_with("__.SYMDEF") => {
                raw = bsd_index(m.data, n.ends_with("_64"), caps, warnings)?
            }
            _ => continue,
        }
        break;
    }
    let mut out = Vec::with_capacity(raw.len());
    for (name, header_offset) in raw {
        let member = members
            .iter()
            .position(|m| m.header_offset == header_offset);
        if member.is_none() {
            warnings.push(format!(
                "symbol {name} is indexed at member offset {header_offset:#x}, where no \
                 member header starts"
            ));
        }
        out.push(IndexEntry {
            name,
            header_offset,
            member,
        });
    }
    Ok(out)
}

/// GNU's index: a big-endian count, that many member offsets, then that many
/// NUL-terminated names. `/SYM64/` is the same shape at eight bytes wide.
fn gnu_index(
    data: &[u8],
    wide: bool,
    caps: &Caps,
    warnings: &mut Vec<String>,
) -> Result<Vec<(String, u64)>> {
    let r = Reader::new(data, r12e_core::Endian::Big);
    let mut c = r;
    let count = c.uword("archive index count", wide)?;
    caps.check("archive index symbols", count, caps.symbols)?;
    // The declared count is not trusted for the allocation: the offsets are
    // fixed width and have to fit in what is left of the member.
    let width = if wide { 8 } else { 4 };
    let fits = (c.remaining() as u64) / width;
    let n = count.min(fits);
    if n < count {
        warnings.push(format!(
            "archive index claims {count} symbols, which is more than the {} bytes of the \
             index member hold",
            data.len()
        ));
    }
    let mut offsets = Vec::with_capacity(n as usize);
    for _ in 0..n {
        offsets.push(c.uword("archive index offset", wide)?);
    }
    let strings_at = c.pos();
    let mut out = Vec::with_capacity(n as usize);
    let mut at = strings_at;
    for off in offsets {
        let Ok(name) = r.cstr_at("archive index name", at, caps.string_len) else {
            warnings.push("archive index string table ends before its names do".into());
            break;
        };
        at += name.len() as u64 + 1;
        out.push((text(name), off));
    }
    Ok(out)
}

/// BSD's `__.SYMDEF`: a byte length, that many eight-byte ranlib pairs of
/// (string offset, member offset), a second byte length, then the strings.
///
/// The file is written in the producing host's byte order with nothing to say
/// which, so the order is chosen by whichever reading of the first length
/// fits inside the member.
fn bsd_index(
    data: &[u8],
    wide: bool,
    caps: &Caps,
    warnings: &mut Vec<String>,
) -> Result<Vec<(String, u64)>> {
    let width = if wide { 8 } else { 4 };
    let endian = bsd_endian(data, wide).ok_or(Error::BadField {
        field: "__.SYMDEF ranlib byte count",
        value: data.len() as u64,
        reason: "does not fit the member in either byte order",
    })?;
    let r = Reader::new(data, endian);
    let mut c = r;
    let ranlib_bytes = c.uword("__.SYMDEF ranlib bytes", wide)?;
    let entry = width * 2;
    let count = ranlib_bytes / entry;
    caps.check("archive index symbols", count, caps.symbols)?;
    let fits = (c.remaining() as u64) / entry;
    let n = count.min(fits);
    if n < count {
        warnings.push(format!(
            "__.SYMDEF claims {count} entries, which is more than the member holds"
        ));
    }
    let mut pairs = Vec::with_capacity(n as usize);
    for _ in 0..n {
        let name_off = c.uword("__.SYMDEF name offset", wide)?;
        let member_off = c.uword("__.SYMDEF member offset", wide)?;
        pairs.push((name_off, member_off));
    }
    // Whatever the count said, the string table starts after the declared
    // ranlib bytes, so a clamped read still finds the names.
    c.seek(
        "__.SYMDEF string table",
        width + ranlib_bytes.min(fits * entry),
    )?;
    let _string_bytes = c.uword("__.SYMDEF string bytes", wide)?;
    let strings_at = c.pos();
    let mut out = Vec::with_capacity(pairs.len());
    for (name_off, member_off) in pairs {
        let at = strings_at.saturating_add(name_off);
        match r.cstr_at("__.SYMDEF name", at, caps.string_len) {
            Ok(name) => out.push((text(name), member_off)),
            Err(_) => {
                warnings.push(format!(
                    "__.SYMDEF name offset {name_off} is outside its string table"
                ));
            }
        }
    }
    Ok(out)
}

/// Pick the byte order whose reading of the leading length fits the member.
fn bsd_endian(data: &[u8], wide: bool) -> Option<r12e_core::Endian> {
    let avail = data.len() as u64;
    for endian in [r12e_core::Endian::Little, r12e_core::Endian::Big] {
        let mut c = Reader::new(data, endian);
        if let Ok(n) = c.uword("__.SYMDEF ranlib bytes", wide) {
            if n <= avail.saturating_sub(if wide { 16 } else { 8 }) {
                return Some(endian);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a minimal GNU archive in memory, so the parser is exercised
    /// without a toolchain present.
    fn push_member(out: &mut Vec<u8>, name: &str, body: &[u8]) {
        let h = format!(
            "{name:<16}{:<12}{:<6}{:<6}{:<8}{:<10}`\n",
            0,
            0,
            0,
            "644",
            body.len()
        );
        out.extend_from_slice(h.as_bytes());
        out.extend_from_slice(body);
        if body.len() % 2 == 1 {
            out.push(b'\n');
        }
    }

    fn gnu_archive() -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        push_member(&mut out, "one.o/", b"hello");
        push_member(&mut out, "two.o/", b"world!");
        out
    }

    #[test]
    fn members_and_padding() {
        let bytes = gnu_archive();
        let a = open(&bytes).unwrap();
        assert_eq!(a.flavor, Flavor::Gnu);
        let names: Vec<&str> = a.members.iter().map(|m| m.name.as_str()).collect();
        assert_eq!(names, ["one.o", "two.o"]);
        assert_eq!(a.members[0].data(), b"hello");
        // The odd-sized first member is padded, so the second still parses.
        assert_eq!(a.members[1].data(), b"world!");
        assert!(a.warnings.is_empty(), "{:?}", a.warnings);
    }

    #[test]
    fn not_an_archive_is_not_recognized() {
        assert!(
            open(b"not an archive at all")
                .unwrap_err()
                .is_not_recognized()
        );
        assert!(open(b"").unwrap_err().is_not_recognized());
        assert!(refuse_in_load(b"\x7fELF").is_ok());
        assert!(refuse_in_load(MAGIC).is_err());
    }

    #[test]
    fn a_lying_size_stops_the_walk() {
        let mut a = gnu_archive();
        // Overwrite the first member's size field with something enormous.
        let at = 8 + 16 + 12 + 6 + 6 + 8;
        a[at..at + 10].copy_from_slice(b"4294967295");
        let parsed = open(&a).unwrap();
        assert!(parsed.members.is_empty());
        assert!(!parsed.warnings.is_empty());
    }

    #[test]
    fn every_truncation_returns() {
        let full = gnu_archive();
        for n in 0..full.len() {
            let _ = open(&full[..n]);
        }
    }

    /// An archive holding nothing but a symbol index whose count is `claimed`.
    fn lying_index(claimed: u32) -> Vec<u8> {
        let mut body = Vec::new();
        body.extend_from_slice(&claimed.to_be_bytes());
        body.extend_from_slice(&8u32.to_be_bytes());
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        push_member(&mut out, "/", &body);
        out
    }

    #[test]
    fn an_index_count_past_the_member_is_clamped() {
        let bytes = lying_index(1000);
        let a = open(&bytes).unwrap();
        // One offset fits and its name does not, so nothing is claimed.
        assert!(a.index.is_empty());
        assert!(!a.warnings.is_empty());
    }

    /// A BSD archive: `#1/N` long names and a `__.SYMDEF` index, which no
    /// GNU `ar` on this machine can produce.
    fn bsd_archive() -> Vec<u8> {
        let long = b"a-name-longer-than-sixteen.o\0\0\0\0";
        let body = b"body";
        // The index member comes first, so the object's header offset is the
        // magic plus the index header plus the index body.
        let names = b"first\0second\0";
        let mut index = Vec::new();
        index.extend_from_slice(&16u32.to_le_bytes());
        for name_off in [0u32, 6] {
            index.extend_from_slice(&name_off.to_le_bytes());
            index.extend_from_slice(&0u32.to_le_bytes());
        }
        index.extend_from_slice(&(names.len() as u32).to_le_bytes());
        index.extend_from_slice(names);
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        push_member(&mut out, "__.SYMDEF", &index);
        // The object's header starts wherever the index member ended, padding
        // included, so the offsets are filled in once that is known.
        let member_at = (out.len() as u32).to_le_bytes();
        let pairs_at = 8 + HEADER_LEN as usize + 4;
        out[pairs_at + 4..pairs_at + 8].copy_from_slice(&member_at);
        out[pairs_at + 12..pairs_at + 16].copy_from_slice(&member_at);
        let mut data = long.to_vec();
        data.extend_from_slice(body);
        push_member(&mut out, "#1/32", &data);
        out
    }

    #[test]
    fn bsd_names_and_symdef() {
        let bytes = bsd_archive();
        let a = open(&bytes).unwrap();
        assert_eq!(a.flavor, Flavor::Bsd);
        assert!(a.warnings.is_empty(), "{:?}", a.warnings);
        let obj: Vec<&Member<'_>> = a.objects().map(|(_, m)| m).collect();
        assert_eq!(obj.len(), 1);
        assert_eq!(obj[0].name, "a-name-longer-than-sixteen.o");
        // The name came out of the data, so the data starts after it.
        assert_eq!(obj[0].data(), b"body");
        let names: Vec<&str> = a.index.iter().map(|e| e.name.as_str()).collect();
        assert_eq!(names, ["first", "second"]);
        assert!(a.index.iter().all(|e| e.member == Some(1)));
        assert_eq!(a.definers("second"), vec![1]);
    }

    #[test]
    fn an_index_count_past_the_cap_is_an_error() {
        let bytes = lying_index(u32::MAX);
        assert!(matches!(
            open(&bytes),
            Err(Error::CapExceeded {
                what: "archive index symbols",
                ..
            })
        ));
    }
}
