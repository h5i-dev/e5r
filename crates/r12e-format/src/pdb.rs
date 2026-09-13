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

use r12e_core::{Addr, Reader};
use r12e_types::ctype::{Composite, Enumeration, Field, Signature, Type, TypeId, Types};

use crate::dwarf::{DebugFunction, DebugInfo, DebugLocal, DebugVariable, LineRow};

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
            // A stream cannot be longer than the file it is stored in, and the
            // block list that follows is read through the directory's own
            // cursor, so a lying length runs out of directory rather than
            // memory.
            if size > data.len() {
                return None;
            }
            let mut blocks = Vec::with_capacity(size.div_ceil(block_size));
            for _ in 0..size.div_ceil(block_size) {
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
}

/// One module: where its symbols and its line information are.
#[derive(Debug)]
struct Module {
    stream: u16,
    symbol_bytes: u32,
    c11_bytes: u32,
    c13_bytes: u32,
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
    let _machine = r.u16()?;
    let _padding = r.u32()?;

    let start = r.position();
    let mut at = start.checked_add(modules)?;
    let modules = module_list(data.get(start..at).unwrap_or_default());
    // The optional header is last, behind five substreams whose lengths are
    // all from the file, so the walk to it is checked at every step.
    for n in [
        contributions,
        section_map,
        sources,
        type_servers,
        edit_continue,
    ] {
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
    })
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
    let _module = r.cstr()?;
    let _object = r.cstr()?;
    Some(Module {
        stream,
        symbol_bytes,
        c11_bytes,
        c13_bytes,
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

/// Type ids already built, so a graph with a cycle in it is walked once.
type Made = BTreeMap<u32, TypeId>;

/// The type records of one stream, indexed so a reference resolves on demand.
#[derive(Default)]
struct TypeTable<'a> {
    records: BTreeMap<u32, (u16, &'a [u8])>,
    /// The defining record for each tag, so a forward reference reaches the
    /// members instead of the empty shell that names them.
    definitions: BTreeMap<String, u32>,
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
    types: &'a mut Types,
    made: Made,
    functions: Vec<DebugFunction>,
    variables: Vec<DebugVariable>,
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
                    let Some(mut f) = self.procedure(kind, body) else {
                        continue;
                    };
                    // Locals live in the scope the record opened, and it runs
                    // to the end record that closes it.
                    let mut depth = 1usize;
                    while n < records.len() && depth > 0 {
                        let (kind, body) = records[n];
                        n += 1;
                        match kind {
                            S_BLOCK32 | S_THUNK32 | S_INLINESITE | S_SEPCODE => depth += 1,
                            S_END | S_INLINESITE_END | S_PROC_ID_END => depth -= 1,
                            _ => {
                                if let Some(local) = self.local(kind, body) {
                                    f.locals.push(local);
                                }
                            }
                        }
                    }
                    self.functions.push(f);
                }
                _ => {}
            }
        }
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

    /// A local at a frame offset, which is the only location this models.
    fn local(&mut self, kind: u16, body: &[u8]) -> Option<DebugLocal> {
        if kind != S_BPREL32 && kind != S_REGREL32 {
            return None;
        }
        let mut r = Cur::new(body);
        let offset = r.i32()?;
        let index = r.u32()?;
        if kind == S_REGREL32 {
            let _register = r.u16()?;
        }
        let name = r.cstr()?;
        let ty = self
            .tpi
            .build(index, self.types, &mut self.made, 0)
            .unwrap_or(Types::VOID);
        Some(DebugLocal {
            name,
            ty,
            frame_offset: Some(offset as i64),
            ..Default::default()
        })
    }
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

/// Read a program database, or `None` when the bytes are not one.
///
/// The image's section headers turn the section and offset pairs the records
/// carry into addresses. Without them the linker's own copy is used instead,
/// and the addresses come out relative to the image base.
pub fn parse(data: &[u8], sections: &[crate::Section]) -> Option<DebugInfo> {
    let msf = Msf::open(data)?;
    let (_, named) = msf
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

    let mut types = Types::new();
    let mut symbols = Symbols {
        tpi: &tpi,
        ipi: &ipi,
        bases: &bases,
        types: &mut types,
        made: Made::new(),
        functions: Vec::new(),
        variables: Vec::new(),
    };
    let mut rows = Vec::new();
    for module in &dbi.modules {
        let Some(stream) = msf.stream(module.stream as usize) else {
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
            symbols.walk(stream.get(4..symbols_end).unwrap_or_default());
        }
        if let Some(c13) = stream.get(c11_end..c13_end) {
            lines(c13, &names, &bases, &mut rows);
        }
    }
    // The global records last: a public says less than a procedure record
    // about the same address, so it must not displace one.
    if let Some(stream) = msf.stream(dbi.symbols as usize) {
        symbols.walk(&stream);
    }
    let (mut functions, variables) = (symbols.functions, symbols.variables);

    rows.sort_by_key(|r| r.addr);
    // The declaration site is in the line table rather than on the record, so
    // it comes from the row the function starts at.
    for f in &mut functions {
        let n = rows.partition_point(|r| r.addr < f.low_pc);
        if let Some(row) = rows.get(n).filter(|r| r.addr == f.low_pc && !r.end) {
            f.decl_file = Some(row.file.clone());
            f.decl_line = Some(row.line as u64);
        }
    }

    let mut out = DebugInfo {
        types,
        units: dbi.modules.len(),
        lines: rows,
        ..Default::default()
    };
    for f in functions {
        out.functions.entry(f.low_pc).or_insert(f);
    }
    for v in variables {
        out.variables.entry(v.addr).or_insert(v);
    }
    Some(out)
}

/// The signature every version of the container since 7.00 starts with.
const MAGIC: &[u8] = b"Microsoft C/C++ MSF 7.00\r\n\x1aDS\0\0\0";

// Fixed stream numbers.
const STREAM_INFO: usize = 1;
const STREAM_TPI: usize = 2;
const STREAM_DBI: usize = 3;
const STREAM_IPI: usize = 4;
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
/// Smallest type stream header, which is where the records begin.
const TPI_HEADER: usize = 56;
/// Below this a type index is one of the built-in types, not a record.
const FIRST_RECORD: u32 = 0x1000;
/// The property bit that says a record only names a type.
const FORWARD_REFERENCE: u16 = 0x0080;
/// The public symbol flag that says the address is code.
const PUBLIC_FUNCTION: u32 = 0x0002;
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
