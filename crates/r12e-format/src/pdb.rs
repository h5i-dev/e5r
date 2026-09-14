//! Reading a Windows program database.
//!
//! MSVC keeps almost nothing in the image: the PE carries a GUID, an age and a
//! path, and everything the compiler knew lives in a separate file. This reads
//! that file and produces the same [`crate::dwarf::DebugInfo`] the DWARF reader
//! does, so everything downstream is told what the compiler knew in one shape
//! rather than two.
//!
//! Written from the public documentation of the format. A leaf or a symbol kind
//! this does not know is stepped over by its declared length rather than
//! guessed at, so an unfamiliar producer costs coverage and not correctness.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use r12e_core::{Addr, AddrRange, Evidence, Provenance, Reader};
use r12e_types::ctype::{Composite, Enumeration, Field, Signature, Type, TypeId, Types};

use crate::dwarf::{
    DebugFunction, DebugInfo, DebugLocal, DebugVariable, InlinedFrame, LineRow, Location,
    LocationRange,
};

/// A cursor over one stream.
///
/// Same reason the DWARF reader has one: the core reader labels every read for
/// its error messages, thousands of fields here would carry the same label, and
/// every caller turns a failure into `None` anyway. A program database is
/// little endian wherever it is written.
struct Cur<'a>(Reader<'a>);

impl<'a> Cur<'a> {
    fn new(data: &'a [u8]) -> Cur<'a> {
        Cur(Reader::le(data))
    }
    fn position(&self) -> usize {
        self.0.pos() as usize
    }
    fn len(&self) -> usize {
        self.0.len()
    }
    fn remaining(&self) -> usize {
        self.0.remaining()
    }
    fn is_empty(&self) -> bool {
        self.0.remaining() == 0
    }
    fn seek(&mut self, at: usize) -> bool {
        self.0.seek("pdb", at as u64).is_ok()
    }
    /// Step to the next four byte boundary, where the next entry of an aligned
    /// table starts. False at the end, which ends the walk that called it.
    fn align(&mut self) -> bool {
        let at = self.position().next_multiple_of(4);
        self.seek(at)
    }
    fn peek(&self) -> Option<u8> {
        self.0.data().get(self.position()).copied()
    }
    fn u8(&mut self) -> Option<u8> {
        self.0.u8("pdb").ok()
    }
    fn u16(&mut self) -> Option<u16> {
        self.0.u16("pdb").ok()
    }
    fn u32(&mut self) -> Option<u32> {
        self.0.u32("pdb").ok()
    }
    fn i32(&mut self) -> Option<i32> {
        self.0.i32("pdb").ok()
    }
    fn u64(&mut self) -> Option<u64> {
        self.0.u64("pdb").ok()
    }
    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        self.0.bytes("pdb", n as u64).ok()
    }
    fn cstr(&mut self) -> Option<String> {
        let at = self.0.pos();
        let bytes = self.0.cstr_at("pdb", at, self.0.remaining() as u64).ok()?;
        let out = String::from_utf8_lossy(bytes).into_owned();
        let _ = self.0.seek("pdb", at + bytes.len() as u64 + 1);
        Some(out)
    }
}

/// The container: fixed size blocks, and a directory saying which blocks each
/// stream is scattered across.
///
/// Public because matching and reading are separate jobs: a caller that only
/// wants to know whether this file belongs to that image should not pay for
/// the type graph.
pub struct Msf<'a> {
    data: &'a [u8],
    block_size: usize,
    streams: Vec<(usize, Vec<u32>)>,
}

impl<'a> Msf<'a> {
    /// Open a container, or `None` when these bytes are not one.
    pub fn open(data: &'a [u8]) -> Option<Msf<'a>> {
        let mut r = Cur::new(data);
        if r.bytes(MAGIC.len())? != MAGIC {
            return None;
        }
        let block_size = r.u32()? as usize;
        let _free_block_map = r.u32()?;
        let block_count = r.u32()? as usize;
        let directory_bytes = r.u32()? as usize;
        let _unknown = r.u32()?;
        let block_map = r.u32()? as usize;
        // Every offset in the file is a block number multiplied by this, so it
        // is checked before any of them are used: a power of two in the range
        // the format allows, in a file that holds the blocks it claims.
        if !(512..=0x10000).contains(&block_size) || !block_size.is_power_of_two() {
            return None;
        }
        if block_count.checked_mul(block_size)? > data.len() || directory_bytes > data.len() {
            return None;
        }
        // The directory is itself a stream, and the superblock names the one
        // place its own block list lives.
        let mut map = Cur::new(data);
        if !map.seek(block_map.checked_mul(block_size)?) {
            return None;
        }
        let mut blocks = Vec::with_capacity(directory_bytes.div_ceil(block_size));
        for _ in 0..directory_bytes.div_ceil(block_size) {
            blocks.push(map.u32()?);
        }
        let directory = gather(data, block_size, &blocks, directory_bytes)?;

        let mut d = Cur::new(&directory);
        let count = d.u32()? as usize;
        // A stream costs four bytes of size in the directory before it costs
        // anything else, so the directory cannot name more streams than a
        // quarter of its own length.
        if count > directory_bytes / 4 {
            return None;
        }
        let mut sizes = Vec::with_capacity(count);
        for _ in 0..count {
            let size = d.u32()?;
            // The all-ones size marks a stream that is not there at all.
            sizes.push(if size == u32::MAX { 0 } else { size as usize });
        }
        let mut streams = Vec::with_capacity(count);
        for size in sizes {
            // A stream cannot be longer than the file it is stored in. The
            // block list is then reserved against what is left of the
            // directory rather than against the claimed size: the blocks are
            // read through the directory's own cursor, so a lying length runs
            // out of directory, but reserving for it first would have
            // allocated four bytes per claimed block before finding out.
            if size > data.len() {
                return None;
            }
            let want = size.div_ceil(block_size);
            if want > d.remaining() / 4 {
                return None;
            }
            let mut blocks = Vec::with_capacity(want);
            for _ in 0..want {
                blocks.push(d.u32()?);
            }
            streams.push((size, blocks));
        }
        Some(Msf {
            data,
            block_size,
            streams,
        })
    }

    /// How many streams the directory names.
    pub fn count(&self) -> usize {
        self.streams.len()
    }

    /// One stream's bytes, gathered from the blocks holding them.
    pub fn stream(&self, index: usize) -> Option<Vec<u8>> {
        let (size, blocks) = self.streams.get(index)?;
        gather(self.data, self.block_size, blocks, *size)
    }
}

/// Copy a stream out of the blocks it is scattered across.
fn gather(data: &[u8], block_size: usize, blocks: &[u32], size: usize) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(size);
    for block in blocks {
        let at = (*block as usize).checked_mul(block_size)?;
        let chunk = data.get(at..at.checked_add(block_size)?)?;
        let take = block_size.min(size - out.len());
        out.extend_from_slice(&chunk[..take]);
        if out.len() == size {
            break;
        }
    }
    (out.len() == size).then_some(out)
}

/// What identifies a program database to the image that references it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Identity {
    /// The GUID the linker generated, in the order the debug directory stores
    /// it: two little endian words, then eight bytes.
    pub guid: [u8; 16],
    /// How many times the database has been written since.
    pub age: u32,
    /// The timestamp signature, which is all a database older than GUIDs has.
    pub signature: u32,
}

impl Identity {
    /// The key a symbol server is indexed by: the GUID's fields as Windows
    /// prints them, then the age.
    pub fn key(&self) -> String {
        let g = &self.guid;
        let mut out = format!(
            "{:08X}{:04X}{:04X}",
            u32::from_le_bytes([g[0], g[1], g[2], g[3]]),
            u16::from_le_bytes([g[4], g[5]]),
            u16::from_le_bytes([g[6], g[7]]),
        );
        for b in &g[8..] {
            let _ = write!(out, "{b:02X}");
        }
        let _ = write!(out, "{:X}", self.age);
        out
    }

    /// True when this is the database a debug directory asked for. Both halves
    /// matter: a rebuild keeps the GUID and bumps the age.
    pub fn matches(&self, guid: &[u8; 16], age: u32) -> bool {
        self.guid == *guid && self.age == age
    }
}

/// The identity and path a PE debug directory's CodeView record names.
///
/// This is the other half of matching: the image says which database it wants,
/// [`identity`] says what a database is, and [`Identity::matches`] decides. It
/// takes the record's bytes rather than the image so that the PE loader, which
/// already has them, needs one line to use it.
pub fn codeview_identity(record: &[u8]) -> Option<(Identity, String)> {
    let mut r = Cur::new(record);
    if r.bytes(4)? != CODEVIEW_RSDS {
        return None;
    }
    let mut out = Identity::default();
    out.guid.copy_from_slice(r.bytes(16)?);
    out.age = r.u32()?;
    Some((out, r.cstr()?))
}

/// What a program database says it is, without reading the rest of it.
///
/// Matching is what a caller needs first: symbols from the wrong build are
/// worse than no symbols, because they are confidently wrong.
pub fn identity(data: &[u8]) -> Option<Identity> {
    let msf = Msf::open(data)?;
    Some(info(&msf.stream(STREAM_INFO)?)?.0)
}

/// Stream one: the identity, and the names given to the streams that have one.
fn info(data: &[u8]) -> Option<(Identity, BTreeMap<String, u16>)> {
    let mut r = Cur::new(data);
    let version = r.u32()?;
    let signature = r.u32()?;
    let age = r.u32()?;
    let mut out = Identity {
        age,
        signature,
        ..Default::default()
    };
    // Before this version there is no GUID and no name table, only the
    // timestamp, which is still enough to reject the wrong file.
    if version < VERSION_VC70 {
        return Some((out, BTreeMap::new()));
    }
    out.guid.copy_from_slice(r.bytes(16)?);

    let names = r.u32()? as usize;
    let names = r.bytes(names)?;
    let count = r.u32()? as usize;
    let _capacity = r.u32()?;
    // Two bit vectors say which slots are in use. Their words are read through
    // the cursor, so a lying word count runs out of stream.
    for _ in 0..2 {
        let words = r.u32()? as usize;
        if words > r.remaining() / 4 {
            return Some((out, BTreeMap::new()));
        }
        r.bytes(words * 4)?;
    }
    // An entry is a name offset and a stream number, so the stream bounds how
    // many of them there can be.
    if count > r.remaining() / 8 {
        return Some((out, BTreeMap::new()));
    }
    let mut named = BTreeMap::new();
    for _ in 0..count {
        let at = r.u32()?;
        let stream = r.u32()?;
        named.insert(cstring(names, at), stream as u16);
    }
    Some((out, named))
}

/// A NUL terminated string at an offset into a buffer.
fn cstring(data: &[u8], at: u32) -> String {
    let Some(rest) = data.get(at as usize..) else {
        return String::new();
    };
    let end = rest.iter().position(|b| *b == 0).unwrap_or(rest.len());
    String::from_utf8_lossy(&rest[..end]).into_owned()
}

/// Where the DBI stream says the rest of the information lives.
#[derive(Debug, Default)]
struct Dbi {
    /// The stream holding the global symbol records.
    symbols: u16,
    /// One entry per object file that went into the link.
    modules: Vec<Module>,
    /// The linker's copy of the image's section headers, which is how a
    /// section and offset pair becomes an address without the image.
    section_headers: Option<u16>,
    /// What the image targets, which decides how a register number in a
    /// location record is read.
    machine: u16,
    /// Which module contributed each run of bytes to which section.
    contributions: Vec<RawContribution>,
}

/// One module: where its symbols and its line information are.
#[derive(Debug, Default)]
struct Module {
    stream: u16,
    symbol_bytes: u32,
    c11_bytes: u32,
    c13_bytes: u32,
    /// The object file, or the archive member, the entry names.
    name: String,
    /// The object the linker read it out of, which is the archive for a
    /// member and the same name again otherwise.
    object: String,
}

/// A section contribution before the section bases are known.
#[derive(Debug, Clone, Copy)]
struct RawContribution {
    section: u16,
    offset: u32,
    size: u32,
    characteristics: u32,
    module: u16,
}

/// One run of bytes a module put into a section.
///
/// This is the map from address back to object file, which is what says which
/// translation unit a piece of code came from when the symbol records do not.
#[derive(Debug, Clone)]
pub struct Contribution {
    /// The addresses it covers.
    pub range: AddrRange,
    /// Index into [`Pdb::modules`].
    pub module: u16,
    /// The section characteristics the linker recorded for the run.
    pub characteristics: u32,
}

/// What a module entry says about itself.
#[derive(Debug, Clone, Default)]
pub struct ModuleInfo {
    /// The object file the entry names.
    pub name: String,
    /// The archive it came out of, when it came out of one.
    pub object: String,
    /// The producer string from the module's `S_COMPILE3` record, when it has
    /// one. `* Linker *` modules carry the linker's own version here.
    pub producer: Option<String>,
}

/// What a procedure's frame record says about its stack frame.
///
/// `DebugFunction` has nowhere to put this because DWARF describes a frame
/// with an expression rather than a size, so it is reported alongside rather
/// than folded in.
#[derive(Debug, Clone, Default)]
pub struct Frame {
    /// Bytes of stack frame, not counting the return address.
    pub total_bytes: u32,
    /// Bytes of that which are padding.
    pub padding_bytes: u32,
    /// Bytes of callee saved registers inside the frame.
    pub callee_saved_bytes: u32,
    /// The exception handler the frame installs, when it installs one.
    pub exception_handler: Option<Addr>,
    /// Which register locals are addressed from, as a DWARF register number,
    /// when the encoding names one this knows.
    pub local_base: Option<u16>,
    /// The same for parameters.
    pub param_base: Option<u16>,
    /// The flag word as the record spells it.
    pub flags: u32,
}

/// Stream three: the header, then substreams laid end to end in a fixed order.
fn dbi(data: &[u8]) -> Option<Dbi> {
    let mut r = Cur::new(data);
    if r.i32()? != -1 {
        return None;
    }
    let _version = r.u32()?;
    let _age = r.u32()?;
    let _globals = r.u16()?;
    let _build = r.u16()?;
    let _publics = r.u16()?;
    let _pdb_dll = r.u16()?;
    let symbols = r.u16()?;
    let _rebuild = r.u16()?;
    // Every substream length is signed in the header; a negative one is not a
    // short substream, it is a malformed file.
    let modules = usize::try_from(r.i32()?).ok()?;
    let contributions = usize::try_from(r.i32()?).ok()?;
    let section_map = usize::try_from(r.i32()?).ok()?;
    let sources = usize::try_from(r.i32()?).ok()?;
    let type_servers = usize::try_from(r.i32()?).ok()?;
    let _mfc = r.u32()?;
    let optional = usize::try_from(r.i32()?).ok()?;
    let edit_continue = usize::try_from(r.i32()?).ok()?;
    let _flags = r.u16()?;
    let machine = r.u16()?;
    let _padding = r.u32()?;

    let start = r.position();
    let mut at = start.checked_add(modules)?;
    let modules = module_list(data.get(start..at).unwrap_or_default());
    let contributions = {
        let end = at.checked_add(contributions)?;
        let body = data.get(at..end).unwrap_or_default();
        at = end;
        contribution_list(body)
    };
    // The optional header is last, behind four more substreams whose lengths
    // are all from the file, so the walk to it is checked at every step.
    for n in [section_map, sources, type_servers, edit_continue] {
        at = at.checked_add(n)?;
    }
    let header = data.get(at..at.checked_add(optional)?).unwrap_or_default();
    let section_headers = header
        .get(DBG_SECTION_HEADERS * 2..DBG_SECTION_HEADERS * 2 + 2)
        .map(|b| u16::from_le_bytes([b[0], b[1]]))
        .filter(|n| *n != u16::MAX);
    Some(Dbi {
        symbols,
        modules,
        section_headers,
        machine,
        contributions,
    })
}

/// The section contribution substream: a version word, then fixed size
/// entries. The later version appends a field to each entry rather than
/// changing the ones in front of it.
fn contribution_list(data: &[u8]) -> Vec<RawContribution> {
    let mut r = Cur::new(data);
    let Some(version) = r.u32() else {
        return Vec::new();
    };
    let each = match version {
        SECTION_CONTRIB_V2 => CONTRIBUTION_ENTRY + 4,
        SECTION_CONTRIB_V1 => CONTRIBUTION_ENTRY,
        // An unknown version has an unknown entry size, so stepping through it
        // would be guessing at where each one ends.
        _ => return Vec::new(),
    };
    // Every entry costs `each` bytes, so the substream bounds the count.
    let mut out = Vec::with_capacity(r.remaining() / each);
    while r.remaining() >= each {
        let before = r.position();
        let (Some(section), Some(_pad), Some(offset), Some(size)) =
            (r.u16(), r.u16(), r.i32(), r.i32())
        else {
            break;
        };
        let (Some(characteristics), Some(module)) = (r.u32(), r.u16()) else {
            break;
        };
        if !r.seek(before + each) {
            break;
        }
        // A negative offset or size is not a short run, it is a malformed
        // entry, and a zero length run covers nothing worth reporting.
        let (Ok(offset), Ok(size)) = (u32::try_from(offset), u32::try_from(size)) else {
            continue;
        };
        if size == 0 {
            continue;
        }
        out.push(RawContribution {
            section,
            offset,
            size,
            characteristics,
            module,
        });
    }
    out
}

/// The modules a DBI substream lists.
fn module_list(data: &[u8]) -> Vec<Module> {
    let mut r = Cur::new(data);
    let mut out = Vec::new();
    // An entry is sixty four fixed bytes and two names, so the substream
    // bounds the count on its own and the walk cannot fail to advance.
    while r.remaining() > MODULE_ENTRY {
        let before = r.position();
        let Some(module) = one_module(&mut r) else {
            break;
        };
        out.push(module);
        if r.position() <= before || !r.align() {
            break;
        }
    }
    out
}

fn one_module(r: &mut Cur<'_>) -> Option<Module> {
    let _unused = r.u32()?;
    let _contribution = r.bytes(28)?;
    let _flags = r.u16()?;
    let stream = r.u16()?;
    let symbol_bytes = r.u32()?;
    let c11_bytes = r.u32()?;
    let c13_bytes = r.u32()?;
    let _source_files = r.u16()?;
    let _padding = r.u16()?;
    let _unused = r.u32()?;
    let _source_name = r.u32()?;
    let _pdb_path = r.u32()?;
    let name = r.cstr()?;
    let object = r.cstr()?;
    Some(Module {
        stream,
        symbol_bytes,
        c11_bytes,
        c13_bytes,
        name,
        object,
    })
}

/// Where each section starts, so a section and offset pair becomes an address.
///
/// The caller's headers win when it has them: they carry the image base, where
/// the linker's copy inside the database knows only relative addresses.
fn section_bases(sections: &[crate::Section], msf: &Msf<'_>, dbi: &Dbi) -> Vec<Addr> {
    if !sections.is_empty() {
        return sections.iter().map(|s| s.range.start()).collect();
    }
    let Some(stream) = dbi.section_headers.and_then(|n| msf.stream(n as usize)) else {
        return Vec::new();
    };
    let mut r = Cur::new(&stream);
    let mut out = Vec::new();
    // A header is forty bytes, so the stream bounds the count.
    while r.remaining() >= SECTION_HEADER {
        let (Some(_name), Some(_size), Some(rva), Some(_rest)) =
            (r.bytes(8), r.u32(), r.u32(), r.bytes(24))
        else {
            break;
        };
        out.push(Addr(rva as u64));
    }
    out
}

/// A section and offset pair as an address.
fn address(bases: &[Addr], section: u16, offset: u32) -> Option<Addr> {
    // Sections are numbered from one; zero means the symbol is in none of them.
    let base = bases.get((section as usize).checked_sub(1)?)?;
    base.checked_add(offset as u64)
}

/// A CodeView register number as the DWARF number for the same register.
///
/// The two numberings are unrelated, and [`Location::Register`] is documented
/// as a DWARF number, so a register is translated here or reported as unknown.
/// A register the tables do not cover yields `None` rather than some other
/// register: a location naming the wrong register is worse than no location.
fn dwarf_register(machine: u16, reg: u16) -> Option<u16> {
    match machine {
        MACHINE_AMD64 => amd64_register(reg),
        MACHINE_ARM64 => arm64_register(reg),
        // i386 and 32-bit ARM are readable the same way, but nothing here has
        // produced one to measure against, so they are left unmapped.
        _ => None,
    }
}

/// x86-64. The byte, word and doubleword names are the same machine register
/// at another width, and DWARF numbers the register rather than the width.
fn amd64_register(reg: u16) -> Option<u16> {
    // ax cx dx bx sp bp si di, in the System V numbering.
    const WIDE: [u16; 8] = [0, 2, 1, 3, 7, 6, 4, 5];
    // al cl dl bl ah ch dh bh, which name the same four registers twice.
    const LOW: [u16; 8] = [0, 2, 1, 3, 0, 2, 1, 3];
    // rax rbx rcx rdx rsi rdi rbp rsp r8..r15, in the order CodeView lists
    // them, which is not the order DWARF numbers them in.
    const QUAD: [u16; 16] = [0, 3, 2, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    Some(match reg {
        CV_AMD64_AL..=CV_AMD64_BH => LOW[(reg - CV_AMD64_AL) as usize],
        CV_AMD64_AX..=CV_AMD64_DI => WIDE[(reg - CV_AMD64_AX) as usize],
        CV_AMD64_EAX..=CV_AMD64_EDI => WIDE[(reg - CV_AMD64_EAX) as usize],
        CV_AMD64_RAX..=CV_AMD64_R15 => QUAD[(reg - CV_AMD64_RAX) as usize],
        _ => return None,
    })
}

/// AArch64. The vector registers are deliberately absent: the enumeration's
/// numbering for them has not been checked against a producer here, and a
/// guess would be an invention.
fn arm64_register(reg: u16) -> Option<u16> {
    Some(match reg {
        CV_ARM64_W0..=CV_ARM64_W30 => reg - CV_ARM64_W0,
        CV_ARM64_X0..=CV_ARM64_X28 => reg - CV_ARM64_X0,
        CV_ARM64_FP => 29,
        CV_ARM64_LR => 30,
        CV_ARM64_SP => 31,
        _ => return None,
    })
}

/// Type ids already built, so a graph with a cycle in it is walked once.
type Made = BTreeMap<u32, TypeId>;

/// The type records of one stream, indexed so a reference resolves on demand.
#[derive(Default)]
struct TypeTable<'a> {
    records: BTreeMap<u32, (u16, &'a [u8])>,
    /// The defining record for each tag, so a forward reference reaches the
    /// members instead of the empty shell that names them.
    definitions: BTreeMap<String, u32>,
    /// True when the stream defers to a type server, which is a separate file
    /// holding the records the modules that used it refer to.
    type_server: bool,
}

/// What a field list yielded: members for a structure, values for an enum.
#[derive(Default)]
struct FieldList {
    members: Vec<Field>,
    values: Vec<(String, i64)>,
}

impl<'a> TypeTable<'a> {
    /// Index a type or item stream. A malformed header leaves the table empty
    /// rather than failing the load, because the symbols are worth having
    /// without the types.
    fn scan(data: &'a [u8]) -> TypeTable<'a> {
        let mut out = TypeTable::default();
        let mut r = Cur::new(data);
        let (Some(_version), Some(header), Some(begin)) = (r.u32(), r.u32(), r.u32()) else {
            return out;
        };
        if (header as usize) < TPI_HEADER || !r.seek(header as usize) {
            return out;
        }
        let mut index = begin;
        while !r.is_empty() {
            let Some(length) = r.u16() else { break };
            // A record that cannot hold its own kind field cannot be stepped
            // over, so the walk stops rather than spinning on it. Every other
            // record consumes at least four bytes, which bounds how many of
            // them a stream can hold.
            if length < 2 {
                break;
            }
            let Some(body) = r.bytes(length as usize) else {
                break;
            };
            let kind = u16::from_le_bytes([body[0], body[1]]);
            let body = &body[2..];
            if kind == LF_TYPESERVER2 {
                out.type_server = true;
            }
            if let Some(tag) = tag(kind, body) {
                out.definitions.entry(tag).or_insert(index);
            }
            out.records.insert(index, (kind, body));
            let Some(next) = index.checked_add(1) else {
                break;
            };
            index = next;
        }
        out
    }

    /// The C type a type index names, built once and remembered.
    fn build(&self, index: u32, types: &mut Types, made: &mut Made, depth: u32) -> Option<TypeId> {
        if depth > 32 {
            return None;
        }
        if index < FIRST_RECORD {
            return basic(index, types);
        }
        if let Some(id) = made.get(&index) {
            return Some(*id);
        }
        let (kind, body) = *self.records.get(&index)?;
        let mut r = Cur::new(body);
        let id = match kind {
            // Qualifiers do not change the layout, and carrying them through
            // the decompiler would clutter every declaration.
            LF_MODIFIER => {
                let inner = r.u32()?;
                self.build(inner, types, made, depth + 1)?
            }
            LF_POINTER => {
                let inner = r.u32()?;
                let to = self
                    .build(inner, types, made, depth + 1)
                    .unwrap_or(Types::VOID);
                types.add(Type::Pointer(to))
            }
            LF_ARRAY => {
                let element = r.u32()?;
                let _subscript = r.u32()?;
                let bytes = numeric(&mut r)?;
                let inner = self
                    .build(element, types, made, depth + 1)
                    .unwrap_or(Types::VOID);
                // The record gives a size in bytes where C declares a count.
                let count = types
                    .size_of(inner)
                    .filter(|n| *n > 0)
                    .map(|n| bytes.max(0) as u64 / n);
                types.add(Type::Array(inner, count))
            }
            LF_STRUCTURE | LF_CLASS | LF_INTERFACE | LF_UNION => {
                let union = kind == LF_UNION;
                let _count = r.u16()?;
                let property = r.u16()?;
                let fields = r.u32()?;
                if !union {
                    let _derived = r.u32()?;
                    let _vshape = r.u32()?;
                }
                let size = numeric(&mut r)?;
                let name = r.cstr()?;
                if property & FORWARD_REFERENCE != 0 {
                    let at = self.definitions.get(&name).copied().filter(|a| *a != index);
                    if let Some(id) = at.and_then(|a| self.build(a, types, made, depth + 1)) {
                        made.insert(index, id);
                        return Some(id);
                    }
                }
                // Reserved first, so a member pointing back at this structure
                // finds it instead of recursing forever.
                let placeholder = types.reserve(&name);
                made.insert(index, placeholder);
                let mut list = FieldList::default();
                self.fields(fields, types, made, depth + 1, &mut list);
                list.members.sort_by_key(|f| f.offset);
                types.define(
                    placeholder,
                    Type::Composite(Composite {
                        name: Some(name),
                        union,
                        size: Some(size.max(0) as u64),
                        fields: list.members,
                    }),
                );
                placeholder
            }
            LF_ENUM => {
                let _count = r.u16()?;
                let property = r.u16()?;
                let underlying = r.u32()?;
                let fields = r.u32()?;
                let name = r.cstr()?;
                if property & FORWARD_REFERENCE != 0 {
                    let at = self.definitions.get(&name).copied().filter(|a| *a != index);
                    if let Some(id) = at.and_then(|a| self.build(a, types, made, depth + 1)) {
                        made.insert(index, id);
                        return Some(id);
                    }
                }
                let mut list = FieldList::default();
                self.fields(fields, types, made, depth + 1, &mut list);
                let size = self
                    .build(underlying, types, made, depth + 1)
                    .and_then(|u| types.size_of(u))
                    .unwrap_or(4) as u8;
                types.add(Type::Enum(Enumeration {
                    name: Some(name),
                    size,
                    values: list.values,
                }))
            }
            LF_PROCEDURE => {
                let returns = r.u32()?;
                let (_call, _attributes, _count) = (r.u8()?, r.u8()?, r.u16()?);
                let arguments = r.u32()?;
                let signature = self.signature(returns, arguments, types, made, depth + 1);
                types.add(Type::Function(signature))
            }
            LF_MFUNCTION => {
                let returns = r.u32()?;
                let (_class, _this) = (r.u32()?, r.u32()?);
                let (_call, _attributes, _count) = (r.u8()?, r.u8()?, r.u16()?);
                let arguments = r.u32()?;
                let signature = self.signature(returns, arguments, types, made, depth + 1);
                types.add(Type::Function(signature))
            }
            _ => return None,
        };
        made.insert(index, id);
        Some(id)
    }

    /// The signature a procedure record describes.
    fn signature(
        &self,
        returns: u32,
        arguments: u32,
        types: &mut Types,
        made: &mut Made,
        depth: u32,
    ) -> Signature {
        let mut out = Signature {
            returns: self.build(returns, types, made, depth),
            ..Default::default()
        };
        let Some((LF_ARGLIST, body)) = self.records.get(&arguments).copied() else {
            return out;
        };
        let mut r = Cur::new(body);
        let Some(count) = r.u32() else { return out };
        // A parameter costs four bytes, so the record bounds the count.
        if count as usize > r.remaining() / 4 {
            return out;
        }
        for _ in 0..count {
            let Some(index) = r.u32() else { break };
            // A variadic function ends its list with the no-type index.
            if index == T_NOTYPE {
                out.varargs = true;
                continue;
            }
            let ty = self.build(index, types, made, depth).unwrap_or(Types::VOID);
            out.parameters.push((None, ty));
        }
        out
    }

    /// Walk a field list, collecting what a structure or an enum needs from it.
    fn fields(
        &self,
        index: u32,
        types: &mut Types,
        made: &mut Made,
        depth: u32,
        out: &mut FieldList,
    ) {
        if depth > 32 {
            return;
        }
        let Some((LF_FIELDLIST, body)) = self.records.get(&index).copied() else {
            return;
        };
        let mut r = Cur::new(body);
        loop {
            // Entries are aligned by a padding leaf whose low nibble says how
            // far to step. A nibble of zero would not move, so it ends the
            // walk rather than spinning.
            while let Some(pad) = r.peek().filter(|b| *b >= LF_PAD) {
                if pad & 0x0f == 0 || !r.seek(r.position() + (pad & 0x0f) as usize) {
                    return;
                }
            }
            if r.is_empty() {
                return;
            }
            let before = r.position();
            let Some(leaf) = r.u16() else { return };
            match leaf {
                LF_MEMBER => {
                    let (Some(_attributes), Some(ty)) = (r.u16(), r.u32()) else {
                        return;
                    };
                    let (Some(offset), Some(name)) = (numeric(&mut r), r.cstr()) else {
                        return;
                    };
                    let (ty, bits) = self.member(ty, types, made, depth);
                    out.members.push(Field {
                        name,
                        ty,
                        offset: offset.max(0) as u64,
                        bits,
                    });
                }
                LF_ENUMERATE => {
                    let Some(_attributes) = r.u16() else { return };
                    let (Some(value), Some(name)) = (numeric(&mut r), r.cstr()) else {
                        return;
                    };
                    out.values.push((name, value));
                }
                // A base class occupies its offset like any other member, and
                // that is what the recovered layout has to say.
                LF_BCLASS => {
                    let (Some(_attributes), Some(ty)) = (r.u16(), r.u32()) else {
                        return;
                    };
                    let Some(offset) = numeric(&mut r) else {
                        return;
                    };
                    if let Some(id) = self.build(ty, types, made, depth + 1) {
                        out.members.push(Field {
                            name: types.name_of(id).replace(' ', "_"),
                            ty: id,
                            offset: offset.max(0) as u64,
                            bits: None,
                        });
                    }
                }
                LF_VBCLASS | LF_IVBCLASS => {
                    let (Some(_attributes), Some(_base), Some(_pointer)) =
                        (r.u16(), r.u32(), r.u32())
                    else {
                        return;
                    };
                    if numeric(&mut r).is_none() || numeric(&mut r).is_none() {
                        return;
                    }
                }
                LF_VFUNCTAB => {
                    if r.u16().is_none() || r.u32().is_none() {
                        return;
                    }
                }
                LF_STMEMBER | LF_NESTTYPE => {
                    if r.u16().is_none() || r.u32().is_none() || r.cstr().is_none() {
                        return;
                    }
                }
                LF_METHOD => {
                    if r.u16().is_none() || r.u32().is_none() || r.cstr().is_none() {
                        return;
                    }
                }
                LF_ONEMETHOD => {
                    let (Some(attributes), Some(_ty)) = (r.u16(), r.u32()) else {
                        return;
                    };
                    // A method that introduces a virtual carries its slot.
                    if matches!((attributes >> 2) & 0x7, 4 | 6) && r.u32().is_none() {
                        return;
                    }
                    if r.cstr().is_none() {
                        return;
                    }
                }
                // The list continues in another record when it outgrew this
                // one; it is a jump, so this record is finished.
                LF_INDEX => {
                    let (Some(_pad), Some(next)) = (r.u16(), r.u32()) else {
                        return;
                    };
                    self.fields(next, types, made, depth + 1, out);
                    return;
                }
                // A leaf this does not know has no declared length, so the
                // list stops here rather than reading its bytes as an entry.
                _ => return,
            }
            if r.position() <= before {
                return;
            }
        }
    }

    /// A member's type, and its width when the member is a bitfield.
    fn member(
        &self,
        index: u32,
        types: &mut Types,
        made: &mut Made,
        depth: u32,
    ) -> (TypeId, Option<u8>) {
        if let Some((LF_BITFIELD, body)) = self.records.get(&index).copied() {
            let mut r = Cur::new(body);
            if let (Some(inner), Some(width)) = (r.u32(), r.u8()) {
                let ty = self
                    .build(inner, types, made, depth + 1)
                    .unwrap_or(Types::VOID);
                return (ty, Some(width));
            }
        }
        let ty = self
            .build(index, types, made, depth + 1)
            .unwrap_or(Types::VOID);
        (ty, None)
    }

    /// The name a function identity record carries, which is how an inlined
    /// call says which function was inlined.
    fn item_name(&self, index: u32) -> Option<String> {
        let (kind, body) = self.records.get(&index).copied()?;
        if kind != LF_FUNC_ID && kind != LF_MFUNC_ID {
            return None;
        }
        let mut r = Cur::new(body);
        let (_scope, _ty) = (r.u32()?, r.u32()?);
        r.cstr()
    }

    /// The type index a function identity record points at, for the symbol
    /// records that name the item stream rather than the type stream.
    fn function_type(&self, index: u32) -> Option<u32> {
        let (kind, body) = self.records.get(&index).copied()?;
        if kind != LF_FUNC_ID && kind != LF_MFUNC_ID {
            return None;
        }
        let mut r = Cur::new(body);
        let _scope = r.u32()?;
        r.u32()
    }
}

/// The tag a record defines, or nothing when it is a forward reference or has
/// no tag at all.
fn tag(kind: u16, body: &[u8]) -> Option<String> {
    let mut r = Cur::new(body);
    let _count = r.u16()?;
    let property = r.u16()?;
    if property & FORWARD_REFERENCE != 0 {
        return None;
    }
    match kind {
        LF_STRUCTURE | LF_CLASS | LF_INTERFACE => {
            let (_fields, _derived, _vshape) = (r.u32()?, r.u32()?, r.u32()?);
            numeric(&mut r)?;
        }
        LF_UNION => {
            let _fields = r.u32()?;
            numeric(&mut r)?;
        }
        LF_ENUM => {
            let (_underlying, _fields) = (r.u32()?, r.u32()?);
        }
        _ => return None,
    }
    r.cstr()
}

/// A numeric leaf: a small value is the field itself, a large one is a tag
/// followed by the value, so nothing after one sits at a fixed offset.
fn numeric(r: &mut Cur<'_>) -> Option<i64> {
    let value = r.u16()?;
    if value < LF_NUMERIC {
        return Some(value as i64);
    }
    Some(match value {
        LF_CHAR => r.u8()? as i8 as i64,
        LF_SHORT => r.u16()? as i16 as i64,
        LF_USHORT => r.u16()? as i64,
        LF_LONG => r.u32()? as i32 as i64,
        LF_ULONG => r.u32()? as i64,
        LF_QUADWORD | LF_UQUADWORD => r.u64()? as i64,
        // A real or a complex is never a size or an offset, but it still has
        // to be stepped over for the name behind it to be read.
        LF_REAL32 => {
            r.bytes(4)?;
            0
        }
        LF_REAL64 | LF_COMPLEX32 => {
            r.bytes(8)?;
            0
        }
        LF_REAL80 => {
            r.bytes(10)?;
            0
        }
        LF_REAL128 | LF_OCTWORD | LF_UOCTWORD | LF_COMPLEX64 => {
            r.bytes(16)?;
            0
        }
        _ => return None,
    })
}

/// One of the built-in type indices, which are not records at all: the low
/// byte says what it is, and the mode above it makes it a pointer to that.
fn basic(index: u32, types: &mut Types) -> Option<TypeId> {
    if (index >> 8) & 0xf != 0 {
        let inner = basic(index & 0xff, types)?;
        return Some(types.add(Type::Pointer(inner)));
    }
    Some(match index {
        T_NOTYPE | T_VOID => Types::VOID,
        T_BOOL08 => types.add(Type::Bool),
        T_CHAR | T_RCHAR | T_INT1 => types.integer(1, true),
        T_UCHAR | T_UINT1 => types.integer(1, false),
        T_SHORT | T_INT2 => types.integer(2, true),
        T_WCHAR | T_USHORT | T_UINT2 => types.integer(2, false),
        T_LONG | T_INT4 => types.integer(4, true),
        T_ULONG | T_UINT4 => types.integer(4, false),
        T_QUAD | T_INT8 => types.integer(8, true),
        T_UQUAD | T_UINT8 => types.integer(8, false),
        T_INT16 => types.integer(16, true),
        T_UINT16 => types.integer(16, false),
        T_REAL32 => types.add(Type::Float { size: 4 }),
        T_REAL64 => types.add(Type::Float { size: 8 }),
        T_REAL80 | T_REAL128 => types.add(Type::Float { size: 16 }),
        _ => return None,
    })
}

/// Split a symbol stream into records, which every stream that holds them uses
/// the same shape for.
fn records(data: &[u8]) -> Vec<(u16, &[u8])> {
    let mut r = Cur::new(data);
    let mut out = Vec::new();
    while !r.is_empty() {
        let Some(length) = r.u16() else { break };
        // As in the type streams: a record too short to hold its own kind
        // cannot be stepped over, and every other one costs four bytes, which
        // bounds how many the stream can hold.
        if length < 2 {
            break;
        }
        let Some(body) = r.bytes(length as usize) else {
            break;
        };
        out.push((u16::from_le_bytes([body[0], body[1]]), &body[2..]));
    }
    out
}

/// What turning symbol records into entries needs to have at hand.
struct Symbols<'a> {
    tpi: &'a TypeTable<'a>,
    ipi: &'a TypeTable<'a>,
    bases: &'a [Addr],
    /// Which machine, so a register number can be translated.
    machine: u16,
    types: &'a mut Types,
    made: Made,
    functions: Vec<DebugFunction>,
    variables: Vec<DebugVariable>,
    /// Frame descriptions, keyed by the procedure they belong to.
    frames: BTreeMap<Addr, Frame>,
}

/// What one scope held, gathered before it is attached to anything.
///
/// A scope's contents cannot be written straight into the function it belongs
/// to, because an inlined call's locals belong to the frame rather than to the
/// function, and the frame is itself one of the things being collected.
#[derive(Default)]
struct Scope {
    locals: Vec<DebugLocal>,
    inlines: Vec<InlinedFrame>,
    /// Separated code the scope declared, which is body outside the main run.
    ranges: Vec<AddrRange>,
}

impl Symbols<'_> {
    /// Walk one symbol stream, whether it is a module's or the global one.
    fn walk(&mut self, data: &[u8]) {
        let records = records(data);
        let mut n = 0;
        while n < records.len() {
            let (kind, body) = records[n];
            n += 1;
            match kind {
                S_PUB32 => self.public(body),
                S_GDATA32 | S_LDATA32 => {
                    if let Some(v) = self.data(body) {
                        self.variables.push(v);
                    }
                }
                S_GPROC32 | S_LPROC32 | S_GPROC32_ID | S_LPROC32_ID => {
                    let mut found = self.procedure(kind, body);
                    // A record that could not be read still opened a scope,
                    // and its contents have to be stepped over rather than
                    // attributed to whatever procedure comes after it.
                    let mut sink = DebugFunction::default();
                    let at = found.as_ref().map(|f| f.low_pc).unwrap_or(Addr::ZERO);
                    let scope = self.scope(&records, &mut n, at, 0);
                    let f = found.as_mut().unwrap_or(&mut sink);
                    f.locals = scope.locals;
                    f.inlines = scope.inlines;
                    // Ranges are only worth listing when the body is in more
                    // than one piece; otherwise the start and size say it.
                    if !scope.ranges.is_empty() {
                        if let Some(main) = f.size.and_then(|n| AddrRange::sized(f.low_pc, n)) {
                            f.ranges.push(main);
                        }
                        f.ranges.extend(scope.ranges);
                        f.ranges.sort_by_key(|r| r.start());
                    }
                    if let Some(f) = found {
                        self.functions.push(f);
                    }
                }
                // A thunk is real code with a real name, and nothing else in
                // the file says the name belongs to that address.
                S_THUNK32 => {
                    let found = self.thunk(body);
                    let at = found.as_ref().map(|f| f.low_pc).unwrap_or(Addr::ZERO);
                    let _ = self.scope(&records, &mut n, at, 0);
                    if let Some(f) = found {
                        self.functions.push(f);
                    }
                }
                // A scope opened by something this does not model is still
                // stepped over as a scope, so its end record is consumed.
                _ if opens_scope(kind) => {
                    let _ = self.scope(&records, &mut n, Addr::ZERO, 0);
                }
                _ => {}
            }
        }
    }

    /// Consume one scope's records, up to and including the record closing it.
    ///
    /// `base` is the procedure the scope sits inside, which is what an inline
    /// site's code offsets are measured from. `depth` is how many inlined
    /// calls deep the scope already is.
    fn scope(&mut self, records: &[(u16, &[u8])], n: &mut usize, base: Addr, depth: u32) -> Scope {
        self.scope_at(records, n, base, depth, 0)
    }

    /// The same, counting how deep the recursion is. Nesting comes out of the
    /// file, so a stream that opens a scope and never closes it would descend
    /// as far as it has records; past the limit the opening records are read
    /// as plain ones and the next end record closes the scope that is open.
    fn scope_at(
        &mut self,
        records: &[(u16, &[u8])],
        n: &mut usize,
        base: Addr,
        depth: u32,
        nesting: u32,
    ) -> Scope {
        let mut out = Scope::default();
        let deep = nesting >= MAX_NESTING;
        // A local is described by the record naming it and then by however
        // many range records follow, so it is held until something else ends
        // it.
        let mut pending: Option<DebugLocal> = None;
        let mut ranges: Vec<LocationRange> = Vec::new();
        while *n < records.len() {
            let (kind, body) = records[*n];
            *n += 1;
            if !is_range_record(kind) {
                finish_local(&mut pending, &mut ranges, &mut out.locals);
            }
            match kind {
                S_END | S_INLINESITE_END | S_PROC_ID_END => break,
                S_FRAMEPROC => {
                    if let Some(frame) = self.frame(body) {
                        self.frames.insert(base, frame);
                    }
                }
                S_LOCAL => pending = self.local(body),
                k if is_range_record(k) => {
                    if pending.is_some() {
                        self.location(k, body, &mut ranges);
                    }
                }
                S_BPREL32 | S_REGREL32 => {
                    if let Some(local) = self.frame_local(kind, body) {
                        out.locals.push(local);
                    }
                }
                // A value the optimizer folded away still has a name and a
                // type, and the value itself is the only place it lives.
                S_CONSTANT => {
                    if let Some(local) = self.constant(body) {
                        out.locals.push(local);
                    }
                }
                S_INLINESITE | S_INLINESITE2 if !deep => {
                    let frame = self.inline_site(kind, body, base, depth);
                    let inner = self.scope_at(records, n, base, depth + 1, nesting + 1);
                    match frame {
                        Some(mut frame) => {
                            frame.locals = inner.locals;
                            out.inlines.push(frame);
                            // Deeper frames are kept beside this one rather
                            // than inside it, which is the shape the DWARF
                            // reader produces.
                            out.inlines.extend(inner.inlines);
                        }
                        None => out.locals.extend(inner.locals),
                    }
                    out.ranges.extend(inner.ranges);
                }
                S_SEPCODE if !deep => {
                    if let Some(range) = self.separated(body) {
                        out.ranges.push(range);
                    }
                    let inner = self.scope_at(records, n, base, depth, nesting + 1);
                    out.locals.extend(inner.locals);
                    out.inlines.extend(inner.inlines);
                    out.ranges.extend(inner.ranges);
                }
                k if opens_scope(k) && !deep => {
                    let inner = self.scope_at(records, n, base, depth, nesting + 1);
                    out.locals.extend(inner.locals);
                    out.inlines.extend(inner.inlines);
                    out.ranges.extend(inner.ranges);
                }
                _ => {}
            }
        }
        finish_local(&mut pending, &mut ranges, &mut out.locals);
        out
    }

    /// A procedure: the name, where it starts, and how long it is.
    fn procedure(&mut self, kind: u16, body: &[u8]) -> Option<DebugFunction> {
        let mut r = Cur::new(body);
        let _links = r.bytes(12)?;
        let size = r.u32()?;
        let (_debug_start, _debug_end) = (r.u32()?, r.u32()?);
        let index = r.u32()?;
        let offset = r.u32()?;
        let section = r.u16()?;
        let _flags = r.u8()?;
        let name = r.cstr()?;
        let low_pc = address(self.bases, section, offset)?;
        // The identity records index the item stream, where a function
        // identity carries the real type index.
        let index = match kind {
            S_GPROC32_ID | S_LPROC32_ID => self.ipi.function_type(index).unwrap_or(T_NOTYPE),
            _ => index,
        };
        let signature = self
            .tpi
            .build(index, self.types, &mut self.made, 0)
            .and_then(|id| match self.types.get(id) {
                Some(Type::Function(signature)) => Some(signature.clone()),
                _ => None,
            })
            .unwrap_or_default();
        Some(DebugFunction {
            name,
            low_pc,
            size: Some(size as u64),
            signature,
            ..Default::default()
        })
    }

    /// A thunk: a stub the linker generated, with its own name and extent.
    fn thunk(&mut self, body: &[u8]) -> Option<DebugFunction> {
        let mut r = Cur::new(body);
        let _links = r.bytes(12)?;
        let offset = r.u32()?;
        let section = r.u16()?;
        let length = r.u16()?;
        let _ordinal = r.u8()?;
        let name = r.cstr()?;
        Some(DebugFunction {
            name,
            low_pc: address(self.bases, section, offset)?,
            size: Some(length as u64),
            ..Default::default()
        })
    }

    /// Separated code: a piece of a function the linker put somewhere else.
    fn separated(&mut self, body: &[u8]) -> Option<AddrRange> {
        let mut r = Cur::new(body);
        let _links = r.bytes(8)?;
        let length = r.u32()?;
        let _flags = r.u32()?;
        let offset = r.u32()?;
        let _parent_offset = r.u32()?;
        let section = r.u16()?;
        AddrRange::sized(address(self.bases, section, offset)?, length as u64)
    }

    /// The frame description a procedure carries.
    fn frame(&mut self, body: &[u8]) -> Option<Frame> {
        let mut r = Cur::new(body);
        let total_bytes = r.u32()?;
        let padding_bytes = r.u32()?;
        let _padding_offset = r.u32()?;
        let callee_saved_bytes = r.u32()?;
        let handler_offset = r.u32()?;
        let handler_section = r.u16()?;
        let flags = r.u32()?;
        Some(Frame {
            total_bytes,
            padding_bytes,
            callee_saved_bytes,
            exception_handler: address(self.bases, handler_section, handler_offset),
            local_base: self.base_register((flags >> FRAME_LOCAL_BASE_SHIFT) & 3),
            param_base: self.base_register((flags >> FRAME_PARAM_BASE_SHIFT) & 3),
            flags,
        })
    }

    /// The two bit encoding a frame record uses for the register its offsets
    /// are measured from. Which register each code means depends on the
    /// machine, and zero means the frame has no base register at all.
    fn base_register(&self, code: u32) -> Option<u16> {
        match (self.machine, code) {
            (MACHINE_AMD64, 1) => Some(7),  // rsp
            (MACHINE_AMD64, 2) => Some(6),  // rbp
            (MACHINE_AMD64, 3) => Some(13), // r13
            (MACHINE_ARM64, 1) => Some(31), // sp
            (MACHINE_ARM64, 2) => Some(29), // fp
            _ => None,
        }
    }

    /// A data symbol: a variable at a fixed address.
    fn data(&mut self, body: &[u8]) -> Option<DebugVariable> {
        let mut r = Cur::new(body);
        let index = r.u32()?;
        let offset = r.u32()?;
        let section = r.u16()?;
        let name = r.cstr()?;
        let addr = address(self.bases, section, offset)?;
        let ty = self
            .tpi
            .build(index, self.types, &mut self.made, 0)
            .unwrap_or(Types::VOID);
        Some(DebugVariable { name, ty, addr })
    }

    /// A public symbol, which is a name, an address and a flag saying which of
    /// the two tables it belongs in. It carries no type at all.
    fn public(&mut self, body: &[u8]) {
        let mut r = Cur::new(body);
        let (Some(flags), Some(offset), Some(section)) = (r.u32(), r.u32(), r.u16()) else {
            return;
        };
        let (Some(name), Some(addr)) = (r.cstr(), address(self.bases, section, offset)) else {
            return;
        };
        if flags & PUBLIC_FUNCTION != 0 {
            self.functions.push(DebugFunction {
                name,
                low_pc: addr,
                ..Default::default()
            });
        } else {
            self.variables.push(DebugVariable {
                name,
                ty: Types::VOID,
                addr,
            });
        }
    }

    /// A local at a frame offset, which is how the older records spell one.
    fn frame_local(&mut self, kind: u16, body: &[u8]) -> Option<DebugLocal> {
        let mut r = Cur::new(body);
        let offset = r.i32()?;
        let index = r.u32()?;
        let register = match kind {
            S_REGREL32 => Some(r.u16()?),
            _ => None,
        };
        let name = r.cstr()?;
        let ty = self.type_of(index);
        // A frame relative record names the register itself, so it can say
        // where the value is and not only how far up the frame it sits.
        let location = match register.and_then(|n| dwarf_register(self.machine, n)) {
            Some(n) => Some(Location::RegisterOffset(n, offset as i64)),
            None if kind == S_BPREL32 => Some(Location::FrameOffset(offset as i64)),
            None => None,
        };
        Some(DebugLocal {
            name,
            ty,
            frame_offset: Some(offset as i64),
            location,
            ..Default::default()
        })
    }

    /// A constant the optimizer folded into the code it generated.
    fn constant(&mut self, body: &[u8]) -> Option<DebugLocal> {
        let mut r = Cur::new(body);
        let index = r.u32()?;
        let value = numeric(&mut r)?;
        let name = r.cstr()?;
        Some(DebugLocal {
            name,
            ty: self.type_of(index),
            location: Some(Location::Constant(value)),
            ..Default::default()
        })
    }

    /// The record naming a local, before the records saying where it lives.
    fn local(&mut self, body: &[u8]) -> Option<DebugLocal> {
        let mut r = Cur::new(body);
        let index = r.u32()?;
        let _flags = r.u16()?;
        let name = r.cstr()?;
        Some(DebugLocal {
            name,
            ty: self.type_of(index),
            ..Default::default()
        })
    }

    /// One range record: where a local lives over some run of addresses.
    fn location(&mut self, kind: u16, body: &[u8], out: &mut Vec<LocationRange>) {
        let mut r = Cur::new(body);
        let where_ = match kind {
            S_DEFRANGE_REGISTER => {
                let (Some(reg), Some(_attr)) = (r.u16(), r.u16()) else {
                    return;
                };
                match dwarf_register(self.machine, reg) {
                    Some(n) => Location::Register(n),
                    None => return,
                }
            }
            S_DEFRANGE_FRAMEPOINTER_REL => {
                let Some(offset) = r.i32() else { return };
                Location::FrameOffset(offset as i64)
            }
            S_DEFRANGE_REGISTER_REL => {
                let (Some(reg), Some(flags), Some(offset)) = (r.u16(), r.u16(), r.i32()) else {
                    return;
                };
                // The spilled-member bit says the record describes part of an
                // aggregate rather than the whole local, which nothing here
                // can express.
                if flags & DEFRANGE_SPILLED_MEMBER != 0 {
                    return;
                }
                match dwarf_register(self.machine, reg) {
                    Some(n) => Location::RegisterOffset(n, offset as i64),
                    None => return,
                }
            }
            // The full scope form has no range at all: it is where the local
            // lives for as long as the scope lasts.
            S_DEFRANGE_FRAMEPOINTER_REL_FULL_SCOPE => {
                let Some(offset) = r.i32() else { return };
                out.push(LocationRange {
                    range: AddrRange::empty_at(Addr::ZERO),
                    location: Location::FrameOffset(offset as i64),
                });
                return;
            }
            _ => return,
        };
        self.ranges_of(&mut r, where_, out);
    }

    /// The addresses a range record covers, with the gaps it lists punched
    /// out of them.
    fn ranges_of(&self, r: &mut Cur<'_>, location: Location, out: &mut Vec<LocationRange>) {
        let (Some(offset), Some(section), Some(length)) = (r.u32(), r.u16(), r.u16()) else {
            return;
        };
        let Some(start) = address(self.bases, section, offset) else {
            return;
        };
        let length = length as u64;
        // Gaps are offsets from the start of the range, in order. Anything out
        // of order ends the walk rather than producing a range running
        // backwards.
        let mut pieces = Vec::new();
        let mut at = 0u64;
        while r.remaining() >= 4 {
            let (Some(gap), Some(gap_len)) = (r.u16(), r.u16()) else {
                break;
            };
            let gap = gap as u64;
            if gap < at || gap > length {
                break;
            }
            if gap > at {
                pieces.push((at, gap - at));
            }
            at = (gap + gap_len as u64).min(length);
        }
        if at < length {
            pieces.push((at, length - at));
        }
        for (from, n) in pieces {
            let piece = start.checked_add(from).and_then(|a| AddrRange::sized(a, n));
            if let Some(range) = piece {
                out.push(LocationRange {
                    range,
                    location: location.clone(),
                });
            }
        }
    }

    /// An inlined call: which function, and which addresses it occupies.
    fn inline_site(
        &mut self,
        kind: u16,
        body: &[u8],
        base: Addr,
        depth: u32,
    ) -> Option<InlinedFrame> {
        let mut r = Cur::new(body);
        let (_parent, _end) = (r.u32()?, r.u32()?);
        let inlinee = r.u32()?;
        if kind == S_INLINESITE2 {
            let _invocations = r.u32()?;
        }
        let ranges = annotations(&mut r, base);
        Some(InlinedFrame {
            name: self.ipi.item_name(inlinee).unwrap_or_default(),
            // The item stream index takes the place DWARF gives the abstract
            // origin's offset: it is what joins this to the out-of-line copy.
            abstract_origin: Some(inlinee as u64),
            entry_pc: ranges.iter().map(|r| r.start()).min(),
            ranges,
            depth,
            ..Default::default()
        })
    }

    /// A type index as a type, remembering what was built.
    fn type_of(&mut self, index: u32) -> TypeId {
        self.tpi
            .build(index, self.types, &mut self.made, 0)
            .unwrap_or(Types::VOID)
    }
}

/// Attach the local that the records just walked described.
fn finish_local(
    pending: &mut Option<DebugLocal>,
    ranges: &mut Vec<LocationRange>,
    out: &mut Vec<DebugLocal>,
) {
    let Some(mut local) = pending.take() else {
        ranges.clear();
        return;
    };
    let found = std::mem::take(ranges);
    // A whole scope record has no addresses to attach, so it is the one
    // location rather than one entry in a list.
    if let [one] = found.as_slice() {
        if one.range.is_empty() {
            local.frame_offset = match one.location {
                Location::FrameOffset(n) => Some(n),
                _ => None,
            };
            local.location = Some(one.location.clone());
            out.push(local);
            return;
        }
    }
    // The frame offset is only stated when every range agrees on one: a local
    // that is in a register for part of the function does not have one.
    let mut offsets = found.iter().map(|r| match r.location {
        Location::FrameOffset(n) => Some(n),
        _ => None,
    });
    let first = offsets.next().flatten();
    local.frame_offset = first.filter(|n| offsets.all(|o| o == Some(*n)));
    local.locations = found;
    out.push(local);
}

/// True for the records that say where the local in front of them lives.
fn is_range_record(kind: u16) -> bool {
    (S_DEFRANGE..=S_DEFRANGE_REGISTER_REL).contains(&kind)
}

/// True for the records that open a scope, which then runs to an end record.
fn opens_scope(kind: u16) -> bool {
    matches!(
        kind,
        S_GPROC32
            | S_LPROC32
            | S_GPROC32_ID
            | S_LPROC32_ID
            | S_BLOCK32
            | S_THUNK32
            | S_SEPCODE
            | S_INLINESITE
            | S_INLINESITE2
    )
}

/// A compressed unsigned integer, as the binary annotation stream spells one:
/// the top bits of the first byte say how many bytes it occupies.
fn compressed(r: &mut Cur<'_>) -> Option<u32> {
    let b0 = r.u8()? as u32;
    if b0 & 0x80 == 0 {
        return Some(b0);
    }
    if b0 & 0xc0 == 0x80 {
        return Some(((b0 & 0x3f) << 8) | r.u8()? as u32);
    }
    if b0 & 0xe0 == 0xc0 {
        let (b1, b2, b3) = (r.u8()? as u32, r.u8()? as u32, r.u8()? as u32);
        return Some(((b0 & 0x1f) << 24) | (b1 << 16) | (b2 << 8) | b3);
    }
    // The remaining prefixes are not assigned, so the stream stops here rather
    // than being read as something else.
    None
}

/// The code ranges an inline site's binary annotations describe.
///
/// Offsets are relative to the procedure the site sits in, and start again at
/// zero for each record, including a record nested inside another site. A
/// range is emitted only when the stream said how long it is: a start with no
/// length is dropped rather than extended to somewhere it might not reach.
fn annotations(r: &mut Cur<'_>, base: Addr) -> Vec<AddrRange> {
    let mut out = Vec::new();
    let mut offset = 0u64;
    let mut open: Option<u64> = None;
    let emit = |start: u64, len: u64, out: &mut Vec<AddrRange>| {
        if let Some(range) = base
            .checked_add(start)
            .and_then(|a| AddrRange::sized(a, len))
        {
            out.push(range);
        }
    };
    while !r.is_empty() {
        let Some(op) = compressed(r) else { break };
        match op {
            BA_END => break,
            BA_CODE_OFFSET | BA_CHANGE_CODE_OFFSET => {
                let Some(delta) = compressed(r) else { break };
                offset += delta as u64;
                open = Some(offset);
            }
            BA_CHANGE_CODE_OFFSET_AND_LINE_OFFSET => {
                let Some(packed) = compressed(r) else { break };
                // The low nibble is the code delta; the rest is a line delta,
                // which nothing here records.
                offset += (packed & 0xf) as u64;
                open = Some(offset);
            }
            BA_CHANGE_CODE_LENGTH => {
                let Some(len) = compressed(r) else { break };
                if let Some(start) = open.take() {
                    emit(start, len as u64, &mut out);
                }
                offset += len as u64;
            }
            BA_CHANGE_CODE_LENGTH_AND_CODE_OFFSET => {
                let (Some(len), Some(delta)) = (compressed(r), compressed(r)) else {
                    break;
                };
                offset += delta as u64;
                emit(offset, len as u64, &mut out);
                offset += len as u64;
                open = None;
            }
            // One operand each, and none of them moves the code offset.
            BA_CHANGE_FILE
            | BA_CHANGE_LINE_OFFSET
            | BA_CHANGE_LINE_END_DELTA
            | BA_CHANGE_RANGE_KIND
            | BA_CHANGE_COLUMN_START
            | BA_CHANGE_COLUMN_END_DELTA
            | BA_CHANGE_COLUMN_END => {
                if compressed(r).is_none() {
                    break;
                }
            }
            // Changing the section the offsets are measured in is something
            // this does not model, so the walk stops rather than placing the
            // rest of the ranges in the wrong section.
            _ => break,
        }
    }
    out
}

/// The line rows one module's debug subsections carry.
fn lines(c13: &[u8], names: &[u8], bases: &[Addr], out: &mut Vec<LineRow>) {
    let files = checksums(c13, names);
    let mut r = Cur::new(c13);
    // Every subsection costs its eight byte header, so the walk advances.
    while !r.is_empty() {
        let (Some(kind), Some(length)) = (r.u32(), r.u32()) else {
            break;
        };
        let Some(body) = r.bytes(length as usize) else {
            break;
        };
        if kind == DEBUG_S_LINES {
            line_block(body, &files, bases, out);
        }
        if !r.align() {
            break;
        }
    }
}

/// The file names the checksum subsection lists, keyed by the offset the line
/// blocks refer to them by.
fn checksums(c13: &[u8], names: &[u8]) -> BTreeMap<u32, String> {
    let mut out = BTreeMap::new();
    let mut r = Cur::new(c13);
    while !r.is_empty() {
        let (Some(kind), Some(length)) = (r.u32(), r.u32()) else {
            break;
        };
        let Some(body) = r.bytes(length as usize) else {
            break;
        };
        if kind == DEBUG_S_FILECHKSMS {
            let mut e = Cur::new(body);
            // An entry costs six bytes before its checksum, so the subsection
            // bounds how many there are.
            while !e.is_empty() {
                let at = e.position() as u32;
                let (Some(name), Some(size), Some(_kind)) = (e.u32(), e.u8(), e.u8()) else {
                    break;
                };
                if e.bytes(size as usize).is_none() {
                    break;
                }
                out.insert(at, string_at(names, name));
                if !e.align() {
                    break;
                }
            }
        }
        if !r.align() {
            break;
        }
    }
    out
}

/// A string from the name table the line information indexes into.
fn string_at(names: &[u8], offset: u32) -> String {
    let mut r = Cur::new(names);
    if r.u32() != Some(NAMES_MAGIC) {
        return String::new();
    }
    match names.get(NAMES_HEADER..) {
        Some(buffer) => cstring(buffer, offset),
        None => String::new(),
    }
}

/// One lines subsection: a run of code, then blocks of rows within it.
fn line_block(body: &[u8], files: &BTreeMap<u32, String>, bases: &[Addr], out: &mut Vec<LineRow>) {
    let mut r = Cur::new(body);
    let (Some(offset), Some(section), Some(flags), Some(length)) =
        (r.u32(), r.u16(), r.u16(), r.u32())
    else {
        return;
    };
    let Some(start) = address(bases, section, offset) else {
        return;
    };
    let columns = flags & LINES_HAVE_COLUMNS != 0;
    // Every block costs its twelve byte header, so the walk advances.
    while !r.is_empty() {
        let (Some(file), Some(count), Some(_size)) = (r.u32(), r.u32(), r.u32()) else {
            return;
        };
        // A row is eight bytes, twelve where there are columns, so the bytes
        // left in the subsection bound the count.
        let each = if columns { 12 } else { 8 };
        if count as usize > r.remaining() / each {
            return;
        }
        let name = files.get(&file).cloned().unwrap_or_default();
        let at = r.position();
        for n in 0..count as usize {
            let (Some(delta), Some(bits)) = (r.u32(), r.u32()) else {
                return;
            };
            // The columns for a block follow all of its rows rather than
            // travelling with them.
            let column = match columns {
                true => body
                    .get(at + count as usize * 8 + n * 4..)
                    .and_then(|b| b.get(..2))
                    .map(|b| u16::from_le_bytes([b[0], b[1]]) as u32)
                    .unwrap_or(0),
                false => 0,
            };
            out.push(LineRow {
                addr: start.checked_add(delta as u64).unwrap_or(start),
                file: name.clone(),
                line: bits & 0x00ff_ffff,
                column,
                end: false,
                statement: bits & 0x8000_0000 != 0,
            });
        }
        if columns && !r.seek((at + count as usize * 12).min(r.len())) {
            return;
        }
    }
    // Where the run ends, so a lookup past the last row does not extend it.
    out.push(LineRow {
        addr: start.checked_add(length as u64).unwrap_or(start),
        file: String::new(),
        line: 0,
        column: 0,
        end: true,
        statement: false,
    });
}

/// Everything one program database says.
///
/// [`Pdb::debug`] is the same shape the DWARF reader produces, so nothing
/// above this layer has to know which format the information came from. The
/// other fields are what a database carries and DWARF does not.
#[derive(Debug, Clone)]
pub struct Pdb {
    /// What the database says it is, for matching against an image.
    pub identity: Identity,
    /// What the compiler knew, in the shape the DWARF reader also produces.
    pub debug: DebugInfo,
    /// The object files that went into the link, in the order the DBI stream
    /// lists them, which is the order a contribution's index refers to.
    pub modules: Vec<ModuleInfo>,
    /// Which module contributed which addresses.
    pub contributions: Vec<Contribution>,
    /// Stack frame descriptions, by the procedure they belong to.
    pub frames: BTreeMap<Addr, Frame>,
    /// The machine the DBI stream names, as a PE machine number.
    pub machine: u16,
    /// What was noticed but not acted on, for the report.
    pub warnings: Vec<String>,
}

impl Pdb {
    /// The function entries the database proves.
    ///
    /// A symbol record naming a procedure is a declaration by the compiler
    /// that a function starts there, which is as strong as evidence gets; a
    /// public symbol flagged as code is the same claim with no size attached.
    pub fn hints(&self) -> Vec<crate::FunctionHint> {
        let mut out = Vec::with_capacity(self.debug.functions.len());
        for (addr, f) in &self.debug.functions {
            if f.name.is_empty() {
                continue;
            }
            out.push(crate::FunctionHint {
                addr: *addr,
                size: f.size.filter(|n| *n > 0),
                name: Some(f.name.clone()),
                provenance: Provenance::new(Evidence::Pdb),
            });
        }
        out
    }
}

/// Read a program database, or `None` when the bytes are not one.
///
/// The image's section headers turn the section and offset pairs the records
/// carry into addresses. Without them the linker's own copy is used instead,
/// and the addresses come out relative to the image base.
pub fn parse(data: &[u8], sections: &[crate::Section]) -> Option<DebugInfo> {
    read(data, sections).map(|p| p.debug)
}

/// Read a program database whole, including what does not fit in
/// [`DebugInfo`].
pub fn read(data: &[u8], sections: &[crate::Section]) -> Option<Pdb> {
    let msf = Msf::open(data)?;
    let (identity, named) = msf
        .stream(STREAM_INFO)
        .and_then(|s| info(&s))
        .unwrap_or_default();
    let dbi = msf
        .stream(STREAM_DBI)
        .and_then(|s| dbi(&s))
        .unwrap_or_default();
    let bases = section_bases(sections, &msf, &dbi);
    let tpi_stream = msf.stream(STREAM_TPI).unwrap_or_default();
    let ipi_stream = msf.stream(STREAM_IPI).unwrap_or_default();
    let tpi = TypeTable::scan(&tpi_stream);
    let ipi = TypeTable::scan(&ipi_stream);
    let names = named
        .get(NAMES_STREAM)
        .and_then(|n| msf.stream(*n as usize))
        .unwrap_or_default();

    let mut warnings = Vec::new();
    // A type server holds the records for every module that used it, and it is
    // a separate file this was not given. Saying so is the difference between
    // "no types" and "the types are somewhere else".
    if tpi.type_server {
        warnings.push("types live in a type server this was not given".into());
    }

    let mut types = Types::new();
    let mut symbols = Symbols {
        tpi: &tpi,
        ipi: &ipi,
        bases: &bases,
        machine: dbi.machine,
        types: &mut types,
        made: Made::new(),
        functions: Vec::new(),
        variables: Vec::new(),
        frames: BTreeMap::new(),
    };
    let mut rows = Vec::new();
    let mut modules = Vec::with_capacity(dbi.modules.len());
    for module in &dbi.modules {
        let mut info = ModuleInfo {
            name: module.name.clone(),
            object: module.object.clone(),
            producer: None,
        };
        let Some(stream) = msf.stream(module.stream as usize) else {
            modules.push(info);
            continue;
        };
        // A module stream is a signature, then the symbols, then the two
        // generations of line information, each as long as the header said.
        // The signature is inside the symbol substream, and a module with no
        // symbols has no substream rather than an empty one, so the line
        // information starts at the front.
        let symbols_end = module.symbol_bytes as usize;
        let c11_end = symbols_end + module.c11_bytes as usize;
        let c13_end = c11_end + module.c13_bytes as usize;
        if symbols_end > 4 {
            let body = stream.get(4..symbols_end).unwrap_or_default();
            info.producer = producer(body);
            symbols.walk(body);
        }
        if let Some(c13) = stream.get(c11_end..c13_end) {
            lines(c13, &names, &bases, &mut rows);
        }
        modules.push(info);
    }
    // The global records last: a public says less than a procedure record
    // about the same address, so it must not displace one.
    if let Some(stream) = msf.stream(dbi.symbols as usize) {
        symbols.walk(&stream);
    }
    let (mut functions, variables, frames) = (symbols.functions, symbols.variables, symbols.frames);

    rows.sort_by_key(|r| r.addr);
    // A local addressed from the register the frame record names as the local
    // base is at a frame offset, which is the same fact the older records
    // state directly. Saying it both ways costs nothing and means a caller
    // that only reads `frame_offset` sees the stack slots either way.
    for f in &mut functions {
        let Some(base) = frames.get(&f.low_pc).and_then(|frame| frame.local_base) else {
            continue;
        };
        for local in &mut f.locals {
            if local.frame_offset.is_some() {
                continue;
            }
            let mut offsets = local.locations.iter().map(|r| match r.location {
                Location::RegisterOffset(reg, n) if reg == base => Some(n),
                _ => None,
            });
            let first = offsets.next().flatten();
            local.frame_offset = first.filter(|n| offsets.all(|o| o == Some(*n)));
        }
    }
    // The declaration site is in the line table rather than on the record, so
    // it comes from the row the function starts at.
    for f in &mut functions {
        let n = rows.partition_point(|r| r.addr < f.low_pc);
        if let Some(row) = rows.get(n).filter(|r| r.addr == f.low_pc && !r.end) {
            f.decl_file = Some(row.file.clone());
            f.decl_line = Some(row.line as u64);
        }
        // An inlined call's own lines are in its annotation stream, but the
        // line table proper attributes inlined code to where the outermost
        // call was written, which is exactly the call site of a frame inlined
        // directly into this function. It says nothing about where a nested
        // frame was called from, so those are left unanswered.
        for frame in &mut f.inlines {
            let Some(at) = frame.entry_pc.filter(|_| frame.depth == 0) else {
                continue;
            };
            let n = rows.partition_point(|r| r.addr <= at);
            if let Some(row) = n
                .checked_sub(1)
                .and_then(|n| rows.get(n))
                .filter(|r| !r.end)
            {
                frame.call_file = Some(row.file.clone());
                frame.call_line = Some(row.line);
                frame.call_column = Some(row.column);
            }
        }
    }

    let contributions = dbi
        .contributions
        .iter()
        .filter_map(|c| {
            let start = address(&bases, c.section, c.offset)?;
            Some(Contribution {
                range: AddrRange::sized(start, c.size as u64)?,
                module: c.module,
                characteristics: c.characteristics,
            })
        })
        .collect();

    let mut debug = DebugInfo {
        types,
        units: dbi.modules.len(),
        lines: rows,
        ..Default::default()
    };
    for f in functions {
        debug.functions.entry(f.low_pc).or_insert(f);
    }
    for v in variables {
        debug.variables.entry(v.addr).or_insert(v);
    }
    Some(Pdb {
        identity,
        debug,
        modules,
        contributions,
        frames,
        machine: dbi.machine,
        warnings,
    })
}

/// The compiler string a module's first records carry, when it has one.
fn producer(symbols: &[u8]) -> Option<String> {
    for (kind, body) in records(symbols) {
        if kind != S_COMPILE3 {
            continue;
        }
        let mut r = Cur::new(body);
        // Flags and language, the machine, then four version numbers as pairs
        // of words, and the string behind them.
        let _flags = r.u32()?;
        let _machine = r.u16()?;
        r.bytes(16)?;
        return r.cstr();
    }
    None
}

/// The signature every version of the container since 7.00 starts with.
const MAGIC: &[u8] = b"Microsoft C/C++ MSF 7.00\r\n\x1aDS\0\0\0";

// Fixed stream numbers.
const STREAM_INFO: usize = 1;
const STREAM_TPI: usize = 2;
const STREAM_DBI: usize = 3;
const STREAM_IPI: usize = 4;
/// The signature a debug directory's CodeView record carries when it names a
/// program database by GUID.
const CODEVIEW_RSDS: &[u8] = b"RSDS";
/// The name the line information's string table is filed under.
const NAMES_STREAM: &str = "/names";
const NAMES_MAGIC: u32 = 0xeffe_effe;
const NAMES_HEADER: usize = 12;

/// The first version that carries a GUID rather than only a timestamp.
const VERSION_VC70: u32 = 20000404;
/// Slot of the section headers in the DBI stream's optional header.
const DBG_SECTION_HEADERS: usize = 5;
/// Fixed bytes of a module entry, before its two names.
const MODULE_ENTRY: usize = 64;
/// Bytes of one image section header.
const SECTION_HEADER: usize = 40;
/// How deep one scope may open another. Blocks nest a handful deep in real
/// code and inlined calls a little more; this is only here so that a file
/// claiming a million nested scopes cannot exhaust the stack.
const MAX_NESTING: u32 = 64;
/// Smallest type stream header, which is where the records begin.
const TPI_HEADER: usize = 56;
/// Below this a type index is one of the built-in types, not a record.
const FIRST_RECORD: u32 = 0x1000;
/// The property bit that says a record only names a type.
const FORWARD_REFERENCE: u16 = 0x0080;
/// The public symbol flag that says the address is code.
const PUBLIC_FUNCTION: u32 = 0x0002;
/// Bytes of one section contribution entry, before the later version's extra
/// field.
const CONTRIBUTION_ENTRY: usize = 28;
/// The two versions of the section contribution substream, which differ only
/// in the field the later one appends to each entry.
const SECTION_CONTRIB_V1: u32 = 0xeffe_0000 + 19970605;
const SECTION_CONTRIB_V2: u32 = 0xeffe_0000 + 20140516;
/// Where a frame record's flag word encodes the register locals and parameters
/// are addressed from.
const FRAME_LOCAL_BASE_SHIFT: u32 = 14;
const FRAME_PARAM_BASE_SHIFT: u32 = 16;
/// In a register relative range record, the bit saying the record describes a
/// member spilled out of an aggregate and the field giving that member's
/// offset. Either one means the record is about part of the local rather than
/// all of it, which nothing here can express.
const DEFRANGE_SPILLED_MEMBER: u16 = 0xfff1;

// PE machine numbers, which is how the DBI stream names the target.
const MACHINE_AMD64: u16 = 0x8664;
const MACHINE_ARM64: u16 = 0xaa64;

// CodeView register numbers. The byte, word and doubleword names of the first
// eight x86-64 registers are numbered in the order the 8086 numbered them, and
// the sixty four bit names are a separate block added later.
const CV_AMD64_AL: u16 = 1;
const CV_AMD64_BH: u16 = 8;
const CV_AMD64_AX: u16 = 9;
const CV_AMD64_DI: u16 = 16;
const CV_AMD64_EAX: u16 = 17;
const CV_AMD64_EDI: u16 = 24;
const CV_AMD64_RAX: u16 = 328;
const CV_AMD64_R15: u16 = 343;
const CV_ARM64_W0: u16 = 10;
const CV_ARM64_W30: u16 = 40;
const CV_ARM64_X0: u16 = 50;
const CV_ARM64_X28: u16 = 78;
const CV_ARM64_FP: u16 = 79;
const CV_ARM64_LR: u16 = 80;
const CV_ARM64_SP: u16 = 81;

// Binary annotation opcodes, which describe an inlined call's extent.
const BA_END: u32 = 0;
const BA_CODE_OFFSET: u32 = 1;
const BA_CHANGE_CODE_OFFSET: u32 = 3;
const BA_CHANGE_CODE_LENGTH: u32 = 4;
const BA_CHANGE_FILE: u32 = 5;
const BA_CHANGE_LINE_OFFSET: u32 = 6;
const BA_CHANGE_LINE_END_DELTA: u32 = 7;
const BA_CHANGE_RANGE_KIND: u32 = 8;
const BA_CHANGE_COLUMN_START: u32 = 9;
const BA_CHANGE_COLUMN_END_DELTA: u32 = 10;
const BA_CHANGE_CODE_OFFSET_AND_LINE_OFFSET: u32 = 11;
const BA_CHANGE_CODE_LENGTH_AND_CODE_OFFSET: u32 = 12;
const BA_CHANGE_COLUMN_END: u32 = 13;
/// The lines subsection flag that says columns follow the rows.
const LINES_HAVE_COLUMNS: u16 = 0x0001;

// Built-in type indices.
const T_NOTYPE: u32 = 0x0000;
const T_VOID: u32 = 0x0003;
const T_CHAR: u32 = 0x0010;
const T_SHORT: u32 = 0x0011;
const T_LONG: u32 = 0x0012;
const T_QUAD: u32 = 0x0013;
const T_UCHAR: u32 = 0x0020;
const T_USHORT: u32 = 0x0021;
const T_ULONG: u32 = 0x0022;
const T_UQUAD: u32 = 0x0023;
const T_BOOL08: u32 = 0x0030;
const T_REAL32: u32 = 0x0040;
const T_REAL64: u32 = 0x0041;
const T_REAL80: u32 = 0x0042;
const T_REAL128: u32 = 0x0043;
const T_RCHAR: u32 = 0x0070;
const T_WCHAR: u32 = 0x0071;
const T_INT2: u32 = 0x0072;
const T_UINT2: u32 = 0x0073;
const T_INT4: u32 = 0x0074;
const T_UINT4: u32 = 0x0075;
const T_INT8: u32 = 0x0076;
const T_UINT8: u32 = 0x0077;
const T_INT16: u32 = 0x0078;
const T_UINT16: u32 = 0x0079;
const T_INT1: u32 = 0x0068;
const T_UINT1: u32 = 0x0069;

// Type record leaves.
const LF_MODIFIER: u16 = 0x1001;
const LF_POINTER: u16 = 0x1002;
const LF_PROCEDURE: u16 = 0x1008;
const LF_MFUNCTION: u16 = 0x1009;
const LF_ARGLIST: u16 = 0x1201;
const LF_FIELDLIST: u16 = 0x1203;
const LF_BITFIELD: u16 = 0x1205;
const LF_BCLASS: u16 = 0x1400;
const LF_VBCLASS: u16 = 0x1401;
const LF_IVBCLASS: u16 = 0x1402;
const LF_INDEX: u16 = 0x1404;
const LF_VFUNCTAB: u16 = 0x1409;
const LF_ENUMERATE: u16 = 0x1502;
const LF_ARRAY: u16 = 0x1503;
const LF_CLASS: u16 = 0x1504;
const LF_STRUCTURE: u16 = 0x1505;
const LF_UNION: u16 = 0x1506;
const LF_ENUM: u16 = 0x1507;
const LF_MEMBER: u16 = 0x150d;
const LF_STMEMBER: u16 = 0x150e;
const LF_METHOD: u16 = 0x150f;
const LF_NESTTYPE: u16 = 0x1510;
const LF_ONEMETHOD: u16 = 0x1511;
const LF_INTERFACE: u16 = 0x1519;
const LF_TYPESERVER2: u16 = 0x1515;
const LF_FUNC_ID: u16 = 0x1601;
const LF_MFUNC_ID: u16 = 0x1602;

// Numeric leaves, and the value below which a field is its own value.
const LF_NUMERIC: u16 = 0x8000;
const LF_CHAR: u16 = 0x8000;
const LF_SHORT: u16 = 0x8001;
const LF_USHORT: u16 = 0x8002;
const LF_LONG: u16 = 0x8003;
const LF_ULONG: u16 = 0x8004;
const LF_REAL32: u16 = 0x8005;
const LF_REAL64: u16 = 0x8006;
const LF_REAL80: u16 = 0x8007;
const LF_REAL128: u16 = 0x8008;
const LF_QUADWORD: u16 = 0x8009;
const LF_UQUADWORD: u16 = 0x800a;
const LF_COMPLEX32: u16 = 0x800c;
const LF_COMPLEX64: u16 = 0x800d;
const LF_OCTWORD: u16 = 0x8017;
const LF_UOCTWORD: u16 = 0x8018;
/// Padding leaves, whose low nibble is how far to step.
const LF_PAD: u8 = 0xf0;

// Symbol records.
const S_END: u16 = 0x0006;
const S_FRAMEPROC: u16 = 0x1012;
const S_CONSTANT: u16 = 0x1107;
const S_COMPILE3: u16 = 0x113c;
const S_LOCAL: u16 = 0x113e;
/// The range records, which are contiguous: everything from here to
/// `S_DEFRANGE_REGISTER_REL` says where the local in front of it lives.
const S_DEFRANGE: u16 = 0x113f;
const S_DEFRANGE_REGISTER: u16 = 0x1141;
const S_DEFRANGE_FRAMEPOINTER_REL: u16 = 0x1142;
const S_DEFRANGE_FRAMEPOINTER_REL_FULL_SCOPE: u16 = 0x1144;
const S_DEFRANGE_REGISTER_REL: u16 = 0x1145;
const S_INLINESITE2: u16 = 0x115d;
const S_THUNK32: u16 = 0x1102;
const S_BLOCK32: u16 = 0x1103;
const S_LDATA32: u16 = 0x110c;
const S_GDATA32: u16 = 0x110d;
const S_PUB32: u16 = 0x110e;
const S_LPROC32: u16 = 0x110f;
const S_GPROC32: u16 = 0x1110;
const S_REGREL32: u16 = 0x1111;
const S_BPREL32: u16 = 0x110b;
const S_SEPCODE: u16 = 0x1132;
const S_INLINESITE: u16 = 0x114d;
const S_INLINESITE_END: u16 = 0x114e;
const S_PROC_ID_END: u16 = 0x114f;
const S_LPROC32_ID: u16 = 0x1146;
const S_GPROC32_ID: u16 = 0x1147;

// Module debug subsections.
const DEBUG_S_LINES: u32 = 0xf2;
const DEBUG_S_FILECHKSMS: u32 = 0xf4;
