//! Runtime metadata: what a language's own runtime has to find at run time.
//!
//! A stripped Go binary still carries `pclntab`, because every traceback and
//! every `runtime.Caller` reads it; an Objective-C binary still carries its
//! class and method lists, because `objc_msgSend` dispatches through them.
//! Metadata the program itself needs cannot be stripped, which is what makes
//! it the best evidence a stripped binary offers.
//!
//! Rust is the poor relation: it records nothing for reflection. What it does
//! leave behind is a `core::panic::Location` for every bounds check and every
//! `unwrap`, naming the source file, line and column, and those are worth
//! recovering even though they name no function.
//!
//! Nothing here trusts a count. Every table is clamped to the bytes it sits in
//! before one entry is read, the rule `dwarf.rs` follows, because these tables
//! are found by scanning and a scan lands on hostile bytes by construction.

use std::collections::BTreeMap;

use e5r_core::{Addr, Bits, Endian, Error, Evidence, Provenance, Reader, Result};

use crate::{FunctionHint, Object};

/// Longest name any of these tables may spell. A table whose string has no
/// terminator would otherwise walk the rest of the image.
pub(crate) const MAX_NAME: u64 = 1 << 12;

/// Tables to attempt before giving up. A file can be full of bytes that look
/// like a `pclntab` magic, and each one costs a header validation.
const MAX_CANDIDATES: u32 = 64;

/// What the three readers found, and what they could not read.
#[derive(Debug, Clone, Default)]
pub struct Metadata {
    /// Function entries recovered, with the evidence of the reader that found
    /// them.
    pub hints: Vec<FunctionHint>,
    /// Go's `pclntab`, when the image had one.
    pub go: Option<GoPclntab>,
    /// Rust panic locations, sorted by the address of the record.
    pub panics: Vec<PanicSite>,
    /// Objective-C classes, in class-list order.
    pub classes: Vec<ObjcClass>,
    /// Swift reflection metadata, when the image carried any.
    pub swift: Option<crate::swift::SwiftMetadata>,
    /// Facts for the object's metadata map.
    pub notes: BTreeMap<String, String>,
    /// What could not be read. Reported rather than guessed at.
    pub warnings: Vec<String>,
}

/// Run all three readers over a loaded image.
pub fn read(obj: &Object) -> Metadata {
    let mut out = Metadata::default();

    if let Some(go) = go_pclntab(obj) {
        out.notes
            .insert("go.pclntab".into(), go.version.as_str().into());
        out.notes
            .insert("go.functions".into(), go.functions.len().to_string());
        if let Some(v) = &go.build_version {
            out.notes.insert("go.version".into(), v.clone());
        }
        if let Some(m) = &go.module_info {
            out.notes.insert("go.modinfo".into(), m.clone());
        }
        out.warnings.extend(go.warnings.iter().cloned());
        out.hints.extend(go.hints());
        out.go = Some(go);
    }

    out.panics = rust_panic_sites(obj);
    if !out.panics.is_empty() {
        out.notes
            .insert("rust.panic_sites".into(), out.panics.len().to_string());
        let mut files: Vec<&str> = out.panics.iter().map(|p| p.file.as_str()).collect();
        files.sort_unstable();
        files.dedup();
        out.notes
            .insert("rust.source_files".into(), files.len().to_string());
    }

    let swift = crate::swift::read(obj);
    if !swift.is_empty() {
        out.notes
            .insert("swift.types".into(), swift.types.len().to_string());
        let fields: usize = swift.field_descriptors.iter().map(|d| d.fields.len()).sum();
        out.notes.insert("swift.fields".into(), fields.to_string());
        out.notes.insert(
            "swift.conformances".into(),
            swift.conformances.len().to_string(),
        );
        out.hints.extend(swift.hints());
        out.warnings.extend(swift.warnings.iter().cloned());
        out.swift = Some(swift);
    } else {
        out.warnings.extend(swift.warnings);
    }

    out.classes = objc_classes(obj);
    if !out.classes.is_empty() {
        let methods: usize = out.classes.iter().map(|c| c.methods.len()).sum();
        out.notes
            .insert("objc.classes".into(), out.classes.len().to_string());
        out.notes.insert("objc.methods".into(), methods.to_string());
        for c in &out.classes {
            out.hints.extend(c.hints());
        }
    }

    out
}

/// Run the readers and fold what they found into the object.
///
/// One call so a loader gains all three at once; the readers are public on
/// their own for a caller that wants just one.
pub fn apply(obj: &mut Object) {
    let found = read(obj);
    obj.function_hints.extend(found.hints);
    obj.metadata.extend(found.notes);
    obj.warnings.extend(found.warnings);
}

/// Which `pclntab` layout a binary carries. The header changed shape at Go
/// 1.16, again at 1.18, and the magic changed again at 1.20 without the shape
/// following, so the version is what the magic says and nothing more.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GoVersion {
    /// Go 1.2 through 1.15: a bare count followed by the function table.
    V12,
    /// Go 1.16 and 1.17: the sub-tables moved behind offsets in the header.
    V116,
    /// Go 1.18 and 1.19: entries became 32-bit offsets from `textStart`.
    V118,
    /// Go 1.20 and later: the 1.18 layout under a new magic.
    V120,
}

impl GoVersion {
    /// The version a magic word announces.
    fn from_magic(m: u32) -> Option<GoVersion> {
        match m {
            0xffff_fffb => Some(GoVersion::V12),
            0xffff_fffa => Some(GoVersion::V116),
            0xffff_fff0 => Some(GoVersion::V118),
            0xffff_fff1 => Some(GoVersion::V120),
            _ => None,
        }
    }

    /// The releases this layout covers, for reporting.
    pub fn as_str(self) -> &'static str {
        match self {
            GoVersion::V12 => "go1.2-1.15",
            GoVersion::V116 => "go1.16-1.17",
            GoVersion::V118 => "go1.18-1.19",
            GoVersion::V120 => "go1.20+",
        }
    }

    /// True once entries are 32-bit offsets from `textStart` rather than
    /// whole pointers.
    fn offset_entries(self) -> bool {
        matches!(self, GoVersion::V118 | GoVersion::V120)
    }
}

/// One function the table names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GoFunc {
    /// Entry address.
    pub addr: Addr,
    /// Where the next entry begins, which the table gives for every function
    /// including the last.
    pub end: Addr,
    /// Name as the table spells it, still in Go's `pkg.Func` form.
    pub name: String,
}

/// A parsed `pclntab`.
#[derive(Debug, Clone)]
pub struct GoPclntab {
    /// Layout the magic announced.
    pub version: GoVersion,
    /// Pointer width the header declares, which need not match the container.
    pub ptr_size: u64,
    /// Base that 1.18+ entry offsets are measured from.
    pub text_start: Addr,
    /// Every function, in table order, which is address order.
    pub functions: Vec<GoFunc>,
    /// `runtime.buildVersion`, when the build info blob was readable.
    pub build_version: Option<String>,
    /// The module line of the build info, trimmed of its sentinels.
    pub module_info: Option<String>,
    /// What could not be read.
    pub warnings: Vec<String>,
}

impl GoPclntab {
    /// One hint per function. The table is generated by the linker from its
    /// own symbol table, so this is as strong as a symbol table.
    pub fn hints(&self) -> Vec<FunctionHint> {
        self.functions
            .iter()
            .map(|f| FunctionHint {
                addr: f.addr,
                size: f.addr.distance_to(f.end).filter(|n| *n > 0),
                name: Some(f.name.clone()),
                provenance: Provenance::new(Evidence::GoPclntab),
            })
            .collect()
    }
}

/// Find and read the `pclntab` of a loaded image.
///
/// The section Go names is tried first; a stripped or PIE build that has lost
/// it is found by scanning read-only data for the magic, which is what every
/// Go-aware tool does.
pub fn go_pclntab(obj: &Object) -> Option<GoPclntab> {
    let text = obj
        .sections
        .iter()
        .find(|s| s.exec && !s.range.is_empty())
        .map(|s| s.range.start());

    let mut attempts = 0u32;
    for (_, bytes) in scan_regions(obj, "gopclntab") {
        let mut off = 0usize;
        while let Some(window) = bytes.get(off..off + 8) {
            if looks_like_pclntab(window) {
                attempts += 1;
                let body = bytes.get(off..).unwrap_or_default();
                if let Ok(mut t) = parse_pclntab(body, text) {
                    read_build_info(obj, &mut t);
                    return Some(t);
                }
                if attempts >= MAX_CANDIDATES {
                    return None;
                }
            }
            // Go aligns the table to a pointer pair wherever it puts it.
            off += 8;
        }
    }
    None
}

/// A cheap gate before the full parse: magic, the two reserved zero bytes, and
/// the two sizes, in either byte order.
fn looks_like_pclntab(head: &[u8]) -> bool {
    let Some(m) = head.get(..4) else {
        return false;
    };
    let le = u32::from_le_bytes([m[0], m[1], m[2], m[3]]);
    let be = u32::from_be_bytes([m[0], m[1], m[2], m[3]]);
    if GoVersion::from_magic(le).is_none() && GoVersion::from_magic(be).is_none() {
        return false;
    }
    head.get(4) == Some(&0)
        && head.get(5) == Some(&0)
        && matches!(head.get(6), Some(1 | 2 | 4))
        && matches!(head.get(7), Some(4 | 8))
}

/// Parse a table from its magic onwards.
///
/// `text_start` matters only from 1.18, where entries became offsets from it,
/// and only when the header declares none of its own. Earlier layouts store
/// whole addresses and ignore it.
pub fn parse_pclntab(body: &[u8], text_start: Option<Addr>) -> Result<GoPclntab> {
    let head = Reader::le(body).array::<8>("pclntab header")?;
    let le = u32::from_le_bytes([head[0], head[1], head[2], head[3]]);
    let be = u32::from_be_bytes([head[0], head[1], head[2], head[3]]);
    let (version, endian) = match (GoVersion::from_magic(le), GoVersion::from_magic(be)) {
        (Some(v), _) => (v, Endian::Little),
        (_, Some(v)) => (v, Endian::Big),
        _ => {
            return Err(Error::NotRecognized {
                expected: "Go pclntab",
            });
        }
    };
    if head[4] != 0 || head[5] != 0 {
        return Err(Error::BadField {
            field: "pclntab reserved bytes",
            value: u64::from(head[4]) << 8 | u64::from(head[5]),
            reason: "is not zero, so this magic is a coincidence",
        });
    }
    if !matches!(head[6], 1 | 2 | 4) {
        return Err(Error::BadField {
            field: "pclntab quantum",
            value: head[6] as u64,
            reason: "is not an instruction size any Go target uses",
        });
    }
    let ptr_size = match head[7] {
        4 => 4u64,
        8 => 8u64,
        other => {
            return Err(Error::BadField {
                field: "pclntab pointer size",
                value: other as u64,
                reason: "is neither 4 nor 8",
            });
        }
    };

    let r = Reader::new(body, endian);
    let header_field = |i: u64| -> Result<u64> {
        let mut c = r;
        c.seek("pclntab header field", 8 + i * ptr_size)?;
        c.uword("pclntab header field", ptr_size == 8)
    };

    let mut warnings = Vec::new();
    let declared = header_field(0)?;
    // The sub-table offsets sit in a fixed order that shifted by one slot when
    // 1.18 added `textStart` ahead of them.
    let (name_at, functab_at, text) = match version {
        GoVersion::V12 => (0u64, 8 + ptr_size, text_start.unwrap_or(Addr::ZERO)),
        GoVersion::V116 => (
            header_field(2)?,
            header_field(6)?,
            text_start.unwrap_or(Addr::ZERO),
        ),
        GoVersion::V118 | GoVersion::V120 => {
            let declared_text = header_field(2)?;
            let text = match (declared_text, text_start) {
                (0, Some(t)) => t,
                (v, _) => Addr(v),
            };
            (header_field(3)?, header_field(7)?, text)
        }
    };

    // A table cannot declare more entries than it has bytes: the function
    // table is `nfunc` pairs plus one sentinel giving the end of the last
    // function, so the room left after its offset decides the count.
    let field = if version.offset_entries() {
        4
    } else {
        ptr_size
    };
    let slots = (body.len() as u64).saturating_sub(functab_at) / field;
    let room = slots.saturating_sub(1) / 2;
    if declared > room {
        warnings.push(format!(
            "pclntab declares {declared} functions but has room for {room}"
        ));
    }
    let nfunc = declared.min(room);

    let entry = |i: u64| -> Result<Addr> {
        let mut c = r;
        c.seek("functab entry", functab_at + 2 * i * field)?;
        let v = c.uword("functab entry", field == 8)?;
        Ok(if version.offset_entries() {
            Addr(text.get().wrapping_add(v))
        } else {
            Addr(v)
        })
    };

    // The `_func` record opens with the entry PC, pointer-sized until 1.18 and
    // a 32-bit offset after, and the name offset follows it.
    let name_field = if version.offset_entries() {
        4
    } else {
        ptr_size
    };
    let mut functions = Vec::new();
    let mut skipped = 0u64;
    for i in 0..nfunc {
        let addr = entry(i)?;
        let end = entry(i + 1)?;
        let mut c = r;
        c.seek("functab offset", functab_at + (2 * i + 1) * field)?;
        // The `_func` offset is measured from the whole table before 1.16 and
        // from the function table itself after it.
        let func_base = if version == GoVersion::V12 {
            0
        } else {
            functab_at
        };
        let func_at = func_base.wrapping_add(c.uword("functab offset", field == 8)?);
        let mut f = r;
        if f.seek("_func", func_at.wrapping_add(name_field)).is_err() {
            skipped += 1;
            continue;
        }
        let name_off = match f.u32("_func nameoff") {
            Ok(v) => v as u64,
            Err(_) => {
                skipped += 1;
                continue;
            }
        };
        match r
            .cstr_at("funcname", name_at.wrapping_add(name_off), MAX_NAME)
            .ok()
            .filter(|b| plausible_name(b))
            .and_then(|b| std::str::from_utf8(b).ok())
        {
            Some(name) => functions.push(GoFunc {
                addr,
                end,
                name: name.to_string(),
            }),
            None => skipped += 1,
        }
    }
    if skipped != 0 {
        warnings.push(format!("pclntab: {skipped} entries have no readable name"));
    }
    if functions.is_empty() && nfunc != 0 {
        return Err(Error::BadField {
            field: "pclntab function table",
            value: nfunc,
            reason: "names no function that can be read, so this is not a table",
        });
    }

    Ok(GoPclntab {
        version,
        ptr_size,
        text_start: text,
        functions,
        build_version: None,
        module_info: None,
        warnings,
    })
}

/// True for a name a linker would emit: printable, and real UTF-8 because Go
/// package paths and generic instantiations are not all ASCII.
fn plausible_name(b: &[u8]) -> bool {
    !b.is_empty() && b.iter().all(|&c| c >= 0x20 && c != 0x7f) && std::str::from_utf8(b).is_ok()
}

/// The build info blob, which is a fixed magic rather than a symbol, so it
/// survives stripping the way the table does.
const BUILD_INFO_MAGIC: &[u8] = b"\xff Go buildinf:";

/// Fill in the Go version and module info from the build info blob.
fn read_build_info(obj: &Object, t: &mut GoPclntab) {
    let img = Image::new(obj);
    for (start, bytes) in scan_regions(obj, "go.buildinfo") {
        let mut off = 0usize;
        while let Some(window) = bytes.get(off..off + 32) {
            if window.starts_with(BUILD_INFO_MAGIC) {
                let at = match start.checked_add(off as u64) {
                    Some(a) => a,
                    None => break,
                };
                if let Some((v, m)) = parse_build_info(&img, at, window) {
                    t.build_version = Some(v);
                    t.module_info = m;
                    return;
                }
            }
            // The linker aligns the blob, and nothing else claims the magic.
            off += 16;
        }
    }
}

/// Read the version and module strings out of one build info blob.
///
/// Go 1.18 moved both inline behind a flag bit; before that the blob held two
/// pointers to string headers that only a mapped image can follow.
fn parse_build_info(img: &Image<'_>, at: Addr, head: &[u8]) -> Option<(String, Option<String>)> {
    let ptr_size = *head.get(14)? as u64;
    let flags = *head.get(15)?;
    if !matches!(ptr_size, 4 | 8) {
        return None;
    }
    if flags & 0x2 != 0 {
        let seg = img.obj.memory.segment_at(at)?;
        let body = seg.slice_to_end(at.checked_add(32)?)?;
        let (version, rest) = varint_bytes(body)?;
        let module = varint_bytes(rest).map(|(m, _)| m).unwrap_or_default();
        return Some((
            std::str::from_utf8(version).ok()?.to_string(),
            trim_module(module),
        ));
    }
    // Big-endian is flagged in the same byte the inline format reuses.
    let endian = if flags & 0x1 != 0 {
        Endian::Big
    } else {
        Endian::Little
    };
    // Both fields point at a string header, which is a pointer and a length.
    let read_string = |slot: Addr| -> Option<&[u8]> {
        let header = img.word_with(slot, ptr_size, endian)?;
        let data = Addr(img.word_with(Addr(header), ptr_size, endian)?);
        let len = img.word_with(Addr(header).checked_add(ptr_size)?, ptr_size, endian)?;
        img.obj.memory.slice(data, len.min(MAX_NAME))
    };
    let version = std::str::from_utf8(read_string(at.checked_add(16)?)?).ok()?;
    let module = read_string(at.checked_add(16 + ptr_size)?).unwrap_or_default();
    Some((version.to_string(), trim_module(module)))
}

/// A uvarint length followed by that many bytes, as the inline blob stores it.
fn varint_bytes(body: &[u8]) -> Option<(&[u8], &[u8])> {
    let mut len = 0u64;
    let mut shift = 0u32;
    for (i, &b) in body.iter().take(10).enumerate() {
        len |= u64::from(b & 0x7f) << shift;
        shift += 7;
        if b & 0x80 == 0 {
            let rest = body.get(i + 1..)?;
            let text = rest.get(..usize::try_from(len.min(MAX_NAME)).ok()?)?;
            return Some((text, rest.get(text.len()..)?));
        }
    }
    None
}

/// Strip the 16-byte binary sentinels Go wraps the module info in. They are
/// not text, so this has to happen before anything reads the blob as UTF-8.
fn trim_module(m: &[u8]) -> Option<String> {
    let inner = m.get(16..m.len().checked_sub(16)?)?;
    std::str::from_utf8(inner)
        .ok()
        .filter(|s| !s.is_empty())
        .map(str::to_string)
}

/// One `core::panic::Location` record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PanicSite {
    /// Where the record sits. This is the address a panicking call passes to
    /// the runtime, so a reference to it from code is what ties the file and
    /// line to an instruction.
    pub addr: Addr,
    /// Source file, as the compiler spelled it.
    pub file: String,
    /// Line, counted from one.
    pub line: u32,
    /// Column, counted from one.
    pub column: u32,
}

/// Every `core::panic::Location` the image carries, by address.
///
/// The confidence rule: a record counts only when its pointer lands in mapped
/// non-executable memory, the string there is exactly the declared length, is
/// printable throughout, and ends in `.rs`, and the line and column are inside
/// the ranges a real source file has. The `.rs` requirement is what makes a
/// false positive essentially impossible, and a wrong file name is worse than
/// no file name.
pub fn rust_panic_sites(obj: &Object) -> Vec<PanicSite> {
    let img = Image::new(obj);
    let ptr_size = img.ptr_size();
    let record = ptr_size * 2 + 8;
    let Some(bounds) = obj.memory.bounds() else {
        return Vec::new();
    };
    let mut out: Vec<PanicSite> = Vec::new();

    for (start, bytes) in scan_regions(obj, ".rodata") {
        let mut off = 0u64;
        // One pass at pointer alignment: the record is a static, so the linker
        // never places it anywhere else.
        while off + record <= bytes.len() as u64 {
            let at = match start.checked_add(off) {
                Some(a) => a,
                None => break,
            };
            off += ptr_size;
            let Some(mut c) = img.at(at, record) else {
                continue;
            };
            let Ok(ptr) = c.uword("Location::file", ptr_size == 8) else {
                continue;
            };
            if ptr == 0 || !bounds.contains(Addr(ptr)) {
                continue;
            }
            let Ok(len) = c.uword("Location::file length", ptr_size == 8) else {
                continue;
            };
            if !(4..=MAX_NAME).contains(&len) {
                continue;
            }
            let (Ok(line), Ok(column)) = (c.u32("Location::line"), c.u32("Location::col")) else {
                continue;
            };
            if !(1..=1_000_000).contains(&line) || !(1..=10_000).contains(&column) {
                continue;
            }
            // Section flags, not segment flags: a linker is free to put
            // `.rodata` in the same executable `LOAD` as `.text`, and on this
            // machine's aarch64 toolchain it does.
            if obj.section_at(Addr(ptr)).is_some_and(|s| s.exec) {
                continue;
            }
            let Some(file) = img.text(Addr(ptr), len) else {
                continue;
            };
            if !file.ends_with(".rs") || !file.bytes().all(|b| (0x20..0x7f).contains(&b)) {
                continue;
            }
            out.push(PanicSite {
                addr: at,
                file: file.to_string(),
                line,
                column,
            });
        }
    }
    out.sort_by_key(|p| p.addr);
    out.dedup();
    out
}

/// One method a class list names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjcMethod {
    /// Selector.
    pub selector: String,
    /// Type encoding, empty when it could not be read.
    pub types: String,
    /// The implementation.
    pub imp: Addr,
    /// True for a class method, which the convention spells with a `+`.
    pub class_method: bool,
}

/// One class the image declares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjcClass {
    /// Name, as the runtime would see it.
    pub name: String,
    /// Where the class object is.
    pub addr: Addr,
    /// Instance and class methods together; each says which it is.
    pub methods: Vec<ObjcMethod>,
}

impl ObjcClass {
    /// One hint per implementation, named the way a backtrace spells it.
    pub fn hints(&self) -> Vec<FunctionHint> {
        self.methods
            .iter()
            .map(|m| FunctionHint {
                addr: m.imp,
                size: None,
                name: Some(format!(
                    "{}[{} {}]",
                    if m.class_method { '+' } else { '-' },
                    self.name,
                    m.selector
                )),
                provenance: Provenance::new(Evidence::ObjcMetadata),
            })
            .collect()
    }
}

// class_ro_t flags, and the two shapes a method list comes in.
const RO_META: u32 = 1;
const METHOD_LIST_SMALL: u32 = 0x8000_0000;
const METHOD_ENTSIZE: u32 = 0x0000_fffc;
/// The class's `data` field carries flag bits in its low three.
const CLASS_DATA_MASK: u64 = !0x7u64;

/// Every Objective-C class the image declares, with its methods.
///
/// Only the modern 64-bit ABI is read. A 32-bit image uses the original ABI,
/// whose structures share neither field order nor names with this one, and
/// guessing between them would be worse than reporting nothing.
pub fn objc_classes(obj: &Object) -> Vec<ObjcClass> {
    if obj.bits != Bits::Bits64 {
        return Vec::new();
    }
    let img = Image::new(obj);
    let mut out = Vec::new();
    for sec in obj
        .sections
        .iter()
        .filter(|s| s.name.ends_with("__objc_classlist"))
    {
        let Some(bytes) = obj.memory.slice(sec.range.start(), sec.file_size) else {
            continue;
        };
        // The list is an array of pointers, so its own length bounds it.
        let count = bytes.len() as u64 / 8;
        for i in 0..count {
            let Some(slot) = sec.range.start().checked_add(i * 8) else {
                break;
            };
            let Some(class) = img.ptr(slot).filter(|p| *p != Addr::ZERO) else {
                continue;
            };
            if let Some(c) = objc_class_at(&img, class) {
                out.push(c);
            }
        }
    }
    out
}

/// Read one class object and the metaclass its `isa` points at.
fn objc_class_at(img: &Image<'_>, at: Addr) -> Option<ObjcClass> {
    let (name, mut methods) = objc_class_half(img, at, false)?;
    // The metaclass holds the `+` methods, and pointing at itself is how a
    // hostile file would ask for an endless walk; one level is all there is.
    if let Some(meta) = img.ptr(at).filter(|m| *m != at && *m != Addr::ZERO) {
        if let Some((_, more)) = objc_class_half(img, meta, true) {
            methods.extend(more);
        }
    }
    methods.retain(|m| m.imp != Addr::ZERO);
    Some(ObjcClass {
        name,
        addr: at,
        methods,
    })
}

/// The name and method list of one class object, class or metaclass.
fn objc_class_half(
    img: &Image<'_>,
    at: Addr,
    class_method: bool,
) -> Option<(String, Vec<ObjcMethod>)> {
    // objc_class: isa, superclass, cache, vtable, data.
    let data = Addr(img.ptr(at.checked_add(32)?)?.get() & CLASS_DATA_MASK);
    if data == Addr::ZERO {
        return None;
    }
    // class_ro_t: flags, instanceStart, instanceSize, reserved, ivarLayout,
    // name, baseMethods.
    let flags = img.u32(data)?;
    if (flags & RO_META != 0) != class_method {
        return None;
    }
    let name = img
        .cstr(img.ptr(data.checked_add(24)?)?, MAX_NAME)?
        .to_string();
    let methods = match img.ptr(data.checked_add(32)?) {
        Some(list) if list != Addr::ZERO => objc_methods(img, list, class_method),
        _ => Vec::new(),
    };
    Some((name, methods))
}

/// Read one `method_list_t`.
fn objc_methods(img: &Image<'_>, at: Addr, class_method: bool) -> Vec<ObjcMethod> {
    let Some((entsize, declared)) = img.u32(at).zip(img.u32(at.checked_add(4).unwrap_or(at)))
    else {
        return Vec::new();
    };
    let small = entsize & METHOD_LIST_SMALL != 0;
    let step = u64::from(entsize & METHOD_ENTSIZE);
    if step < 12 {
        return Vec::new();
    }
    // A list cannot declare more methods than the bytes after it hold.
    let room = img.remaining(at).saturating_sub(8) / step;
    let count = u64::from(declared).min(room);
    let mut out = Vec::new();
    for i in 0..count {
        let Some(entry) = at.checked_add(8 + i * step) else {
            break;
        };
        let m = if small {
            objc_small_method(img, entry, class_method)
        } else {
            objc_big_method(img, entry, class_method)
        };
        if let Some(m) = m {
            out.push(m);
        }
    }
    out
}

/// A method whose three fields are whole pointers.
fn objc_big_method(img: &Image<'_>, at: Addr, class_method: bool) -> Option<ObjcMethod> {
    let selector = img.cstr(img.ptr(at)?, MAX_NAME)?.to_string();
    let types = img
        .ptr(at.checked_add(8)?)
        .and_then(|p| img.cstr(p, MAX_NAME))
        .unwrap_or_default()
        .to_string();
    Some(ObjcMethod {
        selector,
        types,
        imp: img.ptr(at.checked_add(16)?)?,
        class_method,
    })
}

/// A method whose fields are 32-bit displacements from their own address, as
/// arm64e and recent toolchains emit. The selector field reaches a selector
/// reference rather than the string, so it needs one more hop.
fn objc_small_method(img: &Image<'_>, at: Addr, class_method: bool) -> Option<ObjcMethod> {
    let rel = |slot: u64| -> Option<Addr> {
        let d = img.u32(at.checked_add(slot)?)? as i32;
        Some(at.checked_add(slot)?.wrapping_offset(d as i64))
    };
    let name_at = rel(0)?;
    let selector = img
        .ptr(name_at)
        .and_then(|p| img.cstr(p, MAX_NAME))
        .or_else(|| img.cstr(name_at, MAX_NAME))?
        .to_string();
    let types = rel(4)
        .and_then(|p| img.cstr(p, MAX_NAME))
        .unwrap_or_default()
        .to_string();
    Some(ObjcMethod {
        selector,
        types,
        imp: rel(8)?,
        class_method,
    })
}

/// Where a scan may look, with the section most likely to hold what is wanted
/// first so a large image is not walked to find a table that announces itself.
///
/// A file whose section headers were removed has no sections at all, and that
/// is exactly the file a scan exists for, so the segments stand in.
fn scan_regions<'a>(obj: &'a Object, prefer: &str) -> Vec<(Addr, &'a [u8])> {
    let mut regions: Vec<(bool, Addr, &[u8])> = data_sections(obj)
        .filter_map(|s| {
            Some((
                !s.name.ends_with(prefer),
                s.range.start(),
                obj.memory.slice(s.range.start(), s.file_size)?,
            ))
        })
        .collect();
    if regions.is_empty() {
        return obj
            .memory
            .segments()
            .iter()
            .filter_map(|s| Some((s.range.start(), s.slice(s.range.start(), s.file_len())?)))
            .collect();
    }
    regions.sort_by_key(|(unnamed, _, _)| *unnamed);
    regions.into_iter().map(|(_, a, b)| (a, b)).collect()
}

/// Sections worth scanning: mapped, not code, and carrying real bytes. Debug
/// sections are excluded because they are large and hold no runtime metadata.
fn data_sections(obj: &Object) -> impl Iterator<Item = &crate::Section> {
    obj.sections.iter().filter(|s| {
        !s.exec
            && s.file_size >= 32
            && !s.range.is_empty()
            && !s.name.starts_with(".debug")
            && !s.name.starts_with(".zdebug")
    })
}

/// Address-keyed reads over a loaded image.
///
/// All three readers chase pointers, and all three must treat an unmapped one
/// as absence rather than an error, so the whole helper returns `Option`.
pub(crate) struct Image<'a> {
    obj: &'a Object,
    wide: bool,
}

impl<'a> Image<'a> {
    pub(crate) fn new(obj: &'a Object) -> Image<'a> {
        Image {
            obj,
            wide: obj.bits == Bits::Bits64,
        }
    }

    /// The image these reads are against.
    pub(crate) fn obj(&self) -> &'a Object {
        self.obj
    }

    pub(crate) fn ptr_size(&self) -> u64 {
        if self.wide { 8 } else { 4 }
    }

    fn at(&self, addr: Addr, len: u64) -> Option<Reader<'a>> {
        Some(Reader::new(
            self.obj.memory.slice(addr, len)?,
            self.obj.endian,
        ))
    }

    pub(crate) fn u16(&self, addr: Addr) -> Option<u16> {
        self.at(addr, 2)?.u16("field").ok()
    }

    pub(crate) fn u32(&self, addr: Addr) -> Option<u32> {
        self.at(addr, 4)?.u32("field").ok()
    }

    /// Bytes from `addr` to the end of its segment, for a record whose length
    /// is only known once it has been walked.
    pub(crate) fn to_end(&self, addr: Addr) -> Option<&'a [u8]> {
        self.obj.memory.segment_at(addr)?.slice_to_end(addr)
    }

    pub(crate) fn ptr(&self, addr: Addr) -> Option<Addr> {
        let v = self.at(addr, self.ptr_size())?;
        let mut c = v;
        Some(Addr(c.uword("pointer", self.wide).ok()?))
    }

    /// A word of a width and order the caller chooses, which the build info
    /// blob needs because it declares both itself.
    fn word_with(&self, addr: Addr, size: u64, endian: Endian) -> Option<u64> {
        let bytes = self.obj.memory.slice(addr, size)?;
        let mut c = Reader::new(bytes, endian);
        c.uword("build info word", size == 8).ok()
    }

    /// Bytes from `addr` to the end of its segment, for a table whose length
    /// is what bounds the entries in it.
    fn remaining(&self, addr: Addr) -> u64 {
        self.obj
            .memory
            .segment_at(addr)
            .and_then(|s| s.slice_to_end(addr))
            .map_or(0, |b| b.len() as u64)
    }

    /// A NUL-terminated string, bounded so an unterminated run cannot walk the
    /// image.
    pub(crate) fn cstr(&self, addr: Addr, max: u64) -> Option<&'a str> {
        let seg = self.obj.memory.segment_at(addr)?;
        let bytes = seg.slice_to_end(addr)?;
        let n = bytes
            .iter()
            .take(usize::try_from(max).ok()?)
            .position(|&b| b == 0)?;
        let s = std::str::from_utf8(bytes.get(..n)?).ok()?;
        (!s.is_empty() && s.bytes().all(|b| b >= 0x20 && b != 0x7f)).then_some(s)
    }

    /// Exactly `len` bytes as text, for a Rust `str` which carries its length
    /// instead of a terminator.
    fn text(&self, addr: Addr, len: u64) -> Option<&'a str> {
        std::str::from_utf8(self.obj.memory.slice(addr, len)?).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_table_that_is_all_magic_and_nothing_else_is_refused() {
        let body = vec![0xf1, 0xff, 0xff, 0xff, 0, 0, 4, 8];
        assert!(parse_pclntab(&body, None).is_err());
    }

    #[test]
    fn a_declared_count_cannot_exceed_the_bytes() {
        // nfunc of u64::MAX with 64 bytes behind it must not allocate, loop or
        // read past the end.
        let mut body = vec![0xf1, 0xff, 0xff, 0xff, 0, 0, 1, 8];
        body.extend_from_slice(&u64::MAX.to_le_bytes());
        body.extend_from_slice(&[0u8; 56]);
        assert!(parse_pclntab(&body, None).is_err());
    }

    #[test]
    fn garbage_never_panics() {
        for seed in 0u32..512 {
            let body: Vec<u8> = (0..256u32)
                .map(|i| (i.wrapping_mul(2654435761).wrapping_add(seed) >> 11) as u8)
                .collect();
            let _ = parse_pclntab(&body, None);
            let mut tagged = body.clone();
            tagged[..8].copy_from_slice(&[0xfb, 0xff, 0xff, 0xff, 0, 0, 4, 8]);
            let _ = parse_pclntab(&tagged, Some(Addr(0x1000)));
            tagged[..4].copy_from_slice(&[0xf0, 0xff, 0xff, 0xff]);
            let _ = parse_pclntab(&tagged, Some(Addr(0x1000)));
        }
    }

    #[test]
    fn a_module_line_without_its_sentinels_is_dropped() {
        assert_eq!(trim_module(&[0xffu8; 32]), None);
        assert_eq!(
            trim_module(b"0123456789abcdefpath0123456789abcdef"),
            Some("path".to_string())
        );
    }
}
