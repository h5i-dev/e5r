//! Reading DWARF debug information.
//!
//! What a binary with debug information tells you is what the compiler knew:
//! the names of functions and their parameters, the types of both, and which
//! source line each address came from. None of that can be recovered from
//! machine code, so when it is present it is worth more than any inference.
//!
//! Covers DWARF 4 and 5, both endiannesses, 32-bit and 64-bit formats. Forms
//! this does not know are skipped by their declared length rather than
//! guessed at, so an unfamiliar producer costs coverage and not correctness.

use std::collections::BTreeMap;

use r12e_core::{Addr, Endian, Reader};
use r12e_types::ctype::{Composite, Enumeration, Field, Signature, Type, TypeId, Types};


/// A cursor over a debug section.
///
/// The core reader labels every read for its error messages; DWARF reads
/// thousands of fields whose label would be the same word, so this wraps it
/// and turns a failure into `None`, which is what every caller here does with
/// it anyway.
struct Cur<'a>(Reader<'a>);

impl<'a> Cur<'a> {
    fn new(data: &'a [u8], endian: Endian) -> Cur<'a> {
        Cur(Reader::new(data, endian))
    }
    fn position(&self) -> usize {
        self.0.pos() as usize
    }
    /// Move to an offset, clamped to the end of the data. Returns false when
    /// the cursor did not actually move forward, which is how a length field
    /// that points backwards or past the end is caught.
    fn seek(&mut self, at: usize) -> bool {
        let before = self.position();
        let target = at.min(self.0.len());
        let _ = self.0.seek("dwarf", target as u64);
        self.position() > before
    }
    fn is_empty(&self) -> bool {
        self.0.remaining() == 0
    }
    fn u8(&mut self) -> Option<u8> {
        self.0.u8("dwarf").ok()
    }
    fn u16(&mut self) -> Option<u16> {
        self.0.u16("dwarf").ok()
    }
    fn u32(&mut self) -> Option<u32> {
        self.0.u32("dwarf").ok()
    }
    fn u64(&mut self) -> Option<u64> {
        self.0.u64("dwarf").ok()
    }
    fn uleb128(&mut self) -> Option<u64> {
        self.0.uleb128("dwarf").ok()
    }
    fn sleb128(&mut self) -> Option<i64> {
        self.0.sleb128("dwarf").ok()
    }
    fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        self.0.bytes("dwarf", n as u64).ok()
    }
    fn cstr(&mut self) -> Option<String> {
        let at = self.0.pos();
        let bytes = self.0.cstr_at("dwarf", at, self.0.remaining() as u64).ok()?;
        let out = String::from_utf8_lossy(bytes).into_owned();
        let _ = self.0.seek("dwarf", at + bytes.len() as u64 + 1);
        Some(out)
    }
}

/// What the debug information said.
#[derive(Debug, Clone, Default)]
pub struct DebugInfo {
    /// The types it defined.
    pub types: Types,
    /// The functions it described, by entry address.
    pub functions: BTreeMap<Addr, DebugFunction>,
    /// Global variables, by address.
    pub variables: BTreeMap<Addr, DebugVariable>,
    /// Compilation units seen, for reporting.
    pub units: usize,
    /// Where each address came from in the source.
    pub lines: Vec<LineRow>,
}

impl DebugInfo {
    /// True when nothing was found.
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.variables.is_empty() && self.lines.is_empty()
    }

    /// The source position of an address, if the line table covers it.
    pub fn line_for(&self, addr: Addr) -> Option<&LineRow> {
        let n = self.lines.partition_point(|r| r.addr <= addr);
        self.lines.get(n.checked_sub(1)?).filter(|r| !r.end)
    }
}

/// A function the compiler described.
#[derive(Debug, Clone, Default)]
pub struct DebugFunction {
    /// Its name in the source.
    pub name: String,
    /// The linkage name, when it differs.
    pub linkage_name: Option<String>,
    /// Where it starts.
    pub low_pc: Addr,
    /// How long it is, when the entry said.
    pub size: Option<u64>,
    /// Its signature.
    pub signature: Signature,
    /// Local variables with a stack offset, keyed by that offset.
    pub locals: Vec<DebugLocal>,
    /// The source file it was declared in.
    pub decl_file: Option<String>,
    /// The line it was declared on.
    pub decl_line: Option<u64>,
    /// True when the compiler inlined it somewhere.
    pub inlined: bool,
}

/// A local variable with a known frame offset.
#[derive(Debug, Clone)]
pub struct DebugLocal {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: TypeId,
    /// Offset from the frame base, when the location was a simple one.
    pub frame_offset: Option<i64>,
}

/// A variable at a fixed address.
#[derive(Debug, Clone)]
pub struct DebugVariable {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: TypeId,
    /// Where it lives.
    pub addr: Addr,
}

/// One row of the line table.
#[derive(Debug, Clone)]
pub struct LineRow {
    /// The address this row starts at.
    pub addr: Addr,
    /// The file, as an index into the unit's file names.
    pub file: String,
    /// The source line.
    pub line: u32,
    /// The source column.
    pub column: u32,
    /// True when this row marks the end of a sequence rather than code.
    pub end: bool,
    /// True when this address is a statement boundary.
    pub statement: bool,
}

/// The sections DWARF lives in.
#[derive(Debug, Clone, Copy, Default)]
pub struct Sections<'a> {
    /// `.debug_info`.
    pub info: &'a [u8],
    /// `.debug_abbrev`.
    pub abbrev: &'a [u8],
    /// `.debug_str`.
    pub str: &'a [u8],
    /// `.debug_line_str`, DWARF 5.
    pub line_str: &'a [u8],
    /// `.debug_str_offsets`, DWARF 5.
    pub str_offsets: &'a [u8],
    /// `.debug_addr`, DWARF 5.
    pub addr: &'a [u8],
    /// `.debug_rnglists`, DWARF 5.
    pub rnglists: &'a [u8],
    /// `.debug_line`.
    pub line: &'a [u8],
}

impl Sections<'_> {
    /// True when there is nothing to read.
    pub fn is_empty(&self) -> bool {
        self.info.is_empty() && self.line.is_empty()
    }
}

/// Parse what the sections carry.
pub fn parse(sections: &Sections<'_>, endian: Endian) -> DebugInfo {
    let mut out = DebugInfo {
        types: Types::new(),
        ..Default::default()
    };
    if sections.is_empty() {
        return out;
    }
    let mut reader = Cur::new(sections.info, endian);
    // A malformed unit header stops the walk rather than resynchronizing on a
    // guess, because a wrong guess produces confident nonsense. A unit that
    // does not advance the cursor stops it too: a length field is a number
    // from the file and can say anything, including nothing.
    while !reader.is_empty() {
        let before = reader.position();
        match unit(&mut reader, sections, endian, &mut out) {
            Some(()) => out.units += 1,
            None => break,
        }
        if reader.position() <= before {
            break;
        }
    }
    if !sections.line.is_empty() {
        out.lines = lines(sections, endian);
        out.lines.sort_by_key(|r| r.addr);
    }
    out
}

/// One compilation unit.
fn unit(
    reader: &mut Cur<'_>,
    sections: &Sections<'_>,
    endian: Endian,
    out: &mut DebugInfo,
) -> Option<()> {
    let start = reader.position();
    let mut length = reader.u32()? as u64;
    let sixty_four = length == 0xffff_ffff;
    if sixty_four {
        length = reader.u64()?;
    }
    // The length is from the file: a unit that claims to run past the end of
    // the section is malformed, and believing it would walk off the data.
    let end = reader
        .position()
        .checked_add(length as usize)
        .filter(|e| *e <= sections.info.len() && *e > reader.position())?;
    let version = reader.u16()?;
    if !(2..=5).contains(&version) {
        return None;
    }

    // DWARF 5 moved the address size and put a unit type first.
    let (address_size, abbrev_offset) = if version >= 5 {
        let _unit_type = reader.u8()?;
        let address_size = reader.u8()?;
        let abbrev_offset = offset(reader, sixty_four)?;
        (address_size, abbrev_offset)
    } else {
        let abbrev_offset = offset(reader, sixty_four)?;
        let address_size = reader.u8()?;
        (address_size, abbrev_offset)
    };

    let abbrevs = abbreviations(sections.abbrev, abbrev_offset as usize)?;
    let mut unit = Unit {
        address_size,
        sixty_four,
        base: start,
        str_offsets_base: 8,
        addr_base: 8,
        endian,
        sections: *sections,
    };

    // Walk the tree, collecting every entry with its children's indices, so a
    // type can be resolved by its offset without a second pass.
    let mut entries: BTreeMap<usize, Entry> = BTreeMap::new();
    let mut stack: Vec<usize> = Vec::new();
    while reader.position() < end {
        // One entry is at least one byte, so a unit cannot hold more entries
        // than it has bytes; anything beyond that is a cursor going nowhere.
        if entries.len() > length as usize {
            return None;
        }
        let at = reader.position();
        let code = reader.uleb128()?;
        if code == 0 {
            stack.pop();
            continue;
        }
        let Some(abbrev) = abbrevs.get(&code) else {
            return Some(()); // an abbreviation this unit did not declare
        };
        let mut entry = Entry {
            tag: abbrev.tag,
            parent: stack.last().copied(),
            attributes: Vec::new(),
        };
        for (attribute, form, implicit) in &abbrev.attributes {
            let value = read_form(reader, *form, *implicit, &mut unit)?;
            entry.attributes.push((*attribute, value));
        }
        if abbrev.children {
            stack.push(at);
        }
        entries.insert(at, entry);
    }

    // The bases DWARF 5 indirects through live on the unit's own entry.
    if let Some((_, root)) = entries.iter().next() {
        if let Some(Value::Unsigned(v)) = root.get(DW_AT_STR_OFFSETS_BASE) {
            unit.str_offsets_base = *v as usize;
        }
        if let Some(Value::Unsigned(v)) = root.get(DW_AT_ADDR_BASE) {
            unit.addr_base = *v as usize;
        }
    }

    let mut resolver = Resolver {
        entries: &entries,
        types: &mut out.types,
        made: BTreeMap::new(),
        unit: &unit,
    };

    // Functions and globals.
    let mut functions = Vec::new();
    let mut variables = Vec::new();
    for (at, entry) in &entries {
        match entry.tag {
            DW_TAG_SUBPROGRAM => {
                if let Some(f) = resolver.function(*at, entry) {
                    functions.push(f);
                }
            }
            DW_TAG_VARIABLE if entry.parent.is_none_or(|p| is_unit(&entries, p)) => {
                if let Some(v) = resolver.variable(entry) {
                    variables.push(v);
                }
            }
            _ => {}
        }
    }
    for f in functions {
        out.functions.insert(f.low_pc, f);
    }
    for v in variables {
        out.variables.insert(v.addr, v);
    }

    reader.seek(end);
    Some(())
}

fn is_unit(entries: &BTreeMap<usize, Entry>, at: usize) -> bool {
    entries.get(&at).map(|e| e.tag) == Some(DW_TAG_COMPILE_UNIT)
}

/// One debugging information entry.
#[derive(Debug, Clone)]
struct Entry {
    tag: u64,
    parent: Option<usize>,
    attributes: Vec<(u64, Value)>,
}

impl Entry {
    fn get(&self, attribute: u64) -> Option<&Value> {
        self.attributes
            .iter()
            .find(|(a, _)| *a == attribute)
            .map(|(_, v)| v)
    }

    fn unsigned(&self, attribute: u64) -> Option<u64> {
        match self.get(attribute)? {
            Value::Unsigned(v) => Some(*v),
            Value::Signed(v) => Some(*v as u64),
            Value::Address(a) => Some(a.get()),
            _ => None,
        }
    }

    fn string(&self) -> Option<&str> {
        match self.get(DW_AT_NAME)? {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    fn reference(&self, attribute: u64) -> Option<usize> {
        match self.get(attribute)? {
            Value::Reference(r) => Some(*r),
            _ => None,
        }
    }
}

/// An attribute's value.
#[derive(Debug, Clone)]
enum Value {
    Unsigned(u64),
    Signed(i64),
    Address(Addr),
    String(String),
    Reference(usize),
    Block(Vec<u8>),
    Flag(#[allow(dead_code)] bool),
}

struct Unit<'a> {
    address_size: u8,
    sixty_four: bool,
    base: usize,
    str_offsets_base: usize,
    addr_base: usize,
    endian: Endian,
    sections: Sections<'a>,
}

/// Build C types from the entries that describe them.
struct Resolver<'a> {
    entries: &'a BTreeMap<usize, Entry>,
    types: &'a mut Types,
    made: BTreeMap<usize, TypeId>,
    unit: &'a Unit<'a>,
}

impl Resolver<'_> {
    fn function(&mut self, at: usize, entry: &Entry) -> Option<DebugFunction> {
        let low = match entry.get(DW_AT_LOW_PC) {
            Some(Value::Address(a)) => *a,
            Some(Value::Unsigned(v)) => Addr(*v),
            _ => return None,
        };
        // A relocatable object legitimately puts a function at offset zero,
        // so zero is an address here and not a missing one.
        // `high_pc` is an address in DWARF 2 and 3 and a length in 4 and 5,
        // told apart by the form class rather than by the version.
        let size = match entry.get(DW_AT_HIGH_PC) {
            Some(Value::Address(a)) => Some(a.get().saturating_sub(low.get())),
            Some(Value::Unsigned(v)) => Some(*v),
            _ => None,
        };
        let returns = entry
            .reference(DW_AT_TYPE)
            .and_then(|r| self.type_at(r, 0));
        let mut signature = Signature {
            returns,
            ..Default::default()
        };
        let mut locals = Vec::new();
        for (child_at, child) in self.entries.iter() {
            if child.parent != Some(at) {
                continue;
            }
            let _ = child_at;
            match child.tag {
                DW_TAG_FORMAL_PARAMETER => {
                    let ty = child
                        .reference(DW_AT_TYPE)
                        .and_then(|r| self.type_at(r, 0))
                        .unwrap_or(Types::VOID);
                    signature
                        .parameters
                        .push((child.string().map(str::to_string), ty));
                }
                DW_TAG_UNSPECIFIED_PARAMETERS => signature.varargs = true,
                DW_TAG_VARIABLE => {
                    let ty = child
                        .reference(DW_AT_TYPE)
                        .and_then(|r| self.type_at(r, 0))
                        .unwrap_or(Types::VOID);
                    if let Some(name) = child.string() {
                        locals.push(DebugLocal {
                            name: name.to_string(),
                            ty,
                            frame_offset: frame_offset(child.get(DW_AT_LOCATION)),
                        });
                    }
                }
                _ => {}
            }
        }
        Some(DebugFunction {
            name: entry.string().unwrap_or_default().to_string(),
            linkage_name: match entry.get(DW_AT_LINKAGE_NAME) {
                Some(Value::String(s)) => Some(s.clone()),
                _ => None,
            },
            low_pc: low,
            size,
            signature,
            locals,
            decl_file: None,
            decl_line: entry.unsigned(DW_AT_DECL_LINE),
            inlined: entry.get(DW_AT_INLINE).is_some(),
        })
    }

    fn variable(&mut self, entry: &Entry) -> Option<DebugVariable> {
        let name = entry.string()?.to_string();
        let ty = entry
            .reference(DW_AT_TYPE)
            .and_then(|r| self.type_at(r, 0))
            .unwrap_or(Types::VOID);
        let addr = static_address(entry.get(DW_AT_LOCATION), self.unit)?;
        Some(DebugVariable { name, ty, addr })
    }

    /// The C type an entry describes, built once and remembered.
    fn type_at(&mut self, at: usize, depth: u32) -> Option<TypeId> {
        if depth > 32 {
            return None;
        }
        if let Some(id) = self.made.get(&at) {
            return Some(*id);
        }
        let entry = self.entries.get(&at)?.clone();
        let name = entry.string().map(str::to_string);
        let id = match entry.tag {
            DW_TAG_BASE_TYPE => {
                let size = entry.unsigned(DW_AT_BYTE_SIZE).unwrap_or(4) as u8;
                let encoding = entry.unsigned(DW_AT_ENCODING).unwrap_or(DW_ATE_SIGNED);
                self.types.add(match encoding {
                    DW_ATE_BOOLEAN => Type::Bool,
                    DW_ATE_FLOAT => Type::Float { size },
                    DW_ATE_SIGNED | DW_ATE_SIGNED_CHAR => Type::Int { size, signed: true },
                    _ => Type::Int {
                        size,
                        signed: false,
                    },
                })
            }
            DW_TAG_POINTER_TYPE => {
                let inner = entry
                    .reference(DW_AT_TYPE)
                    .and_then(|r| self.type_at(r, depth + 1))
                    .unwrap_or(Types::VOID);
                self.types.add(Type::Pointer(inner))
            }
            // Qualifiers do not change the layout, and carrying them through
            // the decompiler would clutter every declaration.
            DW_TAG_CONST_TYPE | DW_TAG_VOLATILE_TYPE | DW_TAG_RESTRICT_TYPE => {
                match entry.reference(DW_AT_TYPE) {
                    Some(r) => self.type_at(r, depth + 1).unwrap_or(Types::VOID),
                    None => Types::VOID,
                }
            }
            DW_TAG_TYPEDEF => {
                let inner = entry
                    .reference(DW_AT_TYPE)
                    .and_then(|r| self.type_at(r, depth + 1))
                    .unwrap_or(Types::VOID);
                match name {
                    Some(n) => self.types.add(Type::Typedef(n, inner)),
                    None => inner,
                }
            }
            DW_TAG_ARRAY_TYPE => {
                let inner = entry
                    .reference(DW_AT_TYPE)
                    .and_then(|r| self.type_at(r, depth + 1))
                    .unwrap_or(Types::VOID);
                // The count lives on a subrange child, as either a count or an
                // upper bound.
                let count = self
                    .entries
                    .iter()
                    .find(|(_, c)| c.parent == Some(at) && c.tag == DW_TAG_SUBRANGE_TYPE)
                    .and_then(|(_, c)| {
                        c.unsigned(DW_AT_COUNT)
                            .or_else(|| c.unsigned(DW_AT_UPPER_BOUND).map(|n| n + 1))
                    });
                self.types.add(Type::Array(inner, count))
            }
            DW_TAG_STRUCTURE_TYPE | DW_TAG_UNION_TYPE | DW_TAG_CLASS_TYPE => {
                // Reserved first, so a field pointing back at this structure
                // finds it instead of recursing forever.
                let placeholder = self
                    .types
                    .reserve(name.as_deref().unwrap_or("anonymous"));
                self.made.insert(at, placeholder);
                let mut fields = Vec::new();
                let children: Vec<(usize, Entry)> = self
                    .entries
                    .iter()
                    .filter(|(_, c)| c.parent == Some(at) && c.tag == DW_TAG_MEMBER)
                    .map(|(a, c)| (*a, c.clone()))
                    .collect();
                for (_, child) in children {
                    let ty = child
                        .reference(DW_AT_TYPE)
                        .and_then(|r| self.type_at(r, depth + 1))
                        .unwrap_or(Types::VOID);
                    fields.push(Field {
                        name: child.string().unwrap_or("field").to_string(),
                        ty,
                        offset: child.unsigned(DW_AT_DATA_MEMBER_LOCATION).unwrap_or(0),
                        bits: child.unsigned(DW_AT_BIT_SIZE).map(|b| b as u8),
                    });
                }
                fields.sort_by_key(|f| f.offset);
                let composite = Type::Composite(Composite {
                    name,
                    union: entry.tag == DW_TAG_UNION_TYPE,
                    size: entry.unsigned(DW_AT_BYTE_SIZE),
                    fields,
                });
                self.types.define(placeholder, composite);
                placeholder
            }
            DW_TAG_ENUMERATION_TYPE => {
                let values: Vec<(String, i64)> = self
                    .entries
                    .iter()
                    .filter(|(_, c)| c.parent == Some(at) && c.tag == DW_TAG_ENUMERATOR)
                    .filter_map(|(_, c)| {
                        Some((
                            c.string()?.to_string(),
                            match c.get(DW_AT_CONST_VALUE)? {
                                Value::Signed(v) => *v,
                                Value::Unsigned(v) => *v as i64,
                                _ => return None,
                            },
                        ))
                    })
                    .collect();
                self.types.add(Type::Enum(Enumeration {
                    name,
                    size: entry.unsigned(DW_AT_BYTE_SIZE).unwrap_or(4) as u8,
                    values,
                }))
            }
            DW_TAG_SUBROUTINE_TYPE => {
                let returns = entry
                    .reference(DW_AT_TYPE)
                    .and_then(|r| self.type_at(r, depth + 1));
                let mut signature = Signature {
                    returns,
                    ..Default::default()
                };
                let children: Vec<Entry> = self
                    .entries
                    .iter()
                    .filter(|(_, c)| c.parent == Some(at))
                    .map(|(_, c)| c.clone())
                    .collect();
                for child in children {
                    match child.tag {
                        DW_TAG_FORMAL_PARAMETER => {
                            let ty = child
                                .reference(DW_AT_TYPE)
                                .and_then(|r| self.type_at(r, depth + 1))
                                .unwrap_or(Types::VOID);
                            signature.parameters.push((None, ty));
                        }
                        DW_TAG_UNSPECIFIED_PARAMETERS => signature.varargs = true,
                        _ => {}
                    }
                }
                self.types.add(Type::Function(signature))
            }
            _ => return None,
        };
        self.made.insert(at, id);
        Some(id)
    }
}

/// A location expression that is just a frame offset.
fn frame_offset(value: Option<&Value>) -> Option<i64> {
    let Value::Block(bytes) = value? else {
        return None;
    };
    // `DW_OP_fbreg <sleb>` and nothing else: anything longer is a location
    // this does not model.
    if bytes.first() != Some(&DW_OP_FBREG) {
        return None;
    }
    let mut reader = Cur::new(&bytes[1..], Endian::Little);
    let offset = reader.sleb128()?;
    reader.is_empty().then_some(offset)
}

/// A location expression that is a fixed address.
fn static_address(value: Option<&Value>, unit: &Unit<'_>) -> Option<Addr> {
    let Value::Block(bytes) = value? else {
        return None;
    };
    match bytes.first() {
        Some(&DW_OP_ADDR) => {
            let mut reader = Cur::new(&bytes[1..], unit.endian);
            Some(Addr(if unit.address_size == 4 {
                reader.u32()? as u64
            } else {
                reader.u64()?
            }))
        }
        Some(&DW_OP_ADDRX) => {
            let mut reader = Cur::new(&bytes[1..], unit.endian);
            let index = reader.uleb128()?;
            address_from_table(unit, index)
        }
        _ => None,
    }
}

fn address_from_table(unit: &Unit<'_>, index: u64) -> Option<Addr> {
    let size = unit.address_size.max(1) as usize;
    let at = unit.addr_base + index as usize * size;
    let bytes = unit.sections.addr.get(at..at + size)?;
    let mut reader = Cur::new(bytes, unit.endian);
    Some(Addr(if size == 4 {
        reader.u32()? as u64
    } else {
        reader.u64()?
    }))
}

/// One abbreviation: what an entry's tag and attributes are.
#[derive(Debug, Clone)]
struct Abbreviation {
    tag: u64,
    children: bool,
    attributes: Vec<(u64, u64, i64)>,
}

fn abbreviations(data: &[u8], at: usize) -> Option<BTreeMap<u64, Abbreviation>> {
    let rest = data.get(at..)?;
    let mut reader = Cur::new(rest, Endian::Little);
    let mut out = BTreeMap::new();
    loop {
        // Every declaration costs bytes, so there cannot be more of them than
        // the table has.
        if out.len() > rest.len() {
            return None;
        }
        let code = reader.uleb128()?;
        if code == 0 {
            break;
        }
        let tag = reader.uleb128()?;
        let children = reader.u8()? != 0;
        let mut attributes = Vec::new();
        loop {
            if attributes.len() > rest.len() {
                return None;
            }
            let attribute = reader.uleb128()?;
            let form = reader.uleb128()?;
            // `implicit_const` carries its value in the abbreviation itself.
            let implicit = if form == DW_FORM_IMPLICIT_CONST {
                reader.sleb128()?
            } else {
                0
            };
            if attribute == 0 && form == 0 {
                break;
            }
            attributes.push((attribute, form, implicit));
        }
        out.insert(
            code,
            Abbreviation {
                tag,
                children,
                attributes,
            },
        );
    }
    Some(out)
}

fn offset(reader: &mut Cur<'_>, sixty_four: bool) -> Option<u64> {
    if sixty_four {
        reader.u64()
    } else {
        reader.u32().map(|v| v as u64)
    }
}

/// Read one attribute value in its form.
fn read_form(
    reader: &mut Cur<'_>,
    form: u64,
    implicit: i64,
    unit: &mut Unit<'_>,
) -> Option<Value> {
    Some(match form {
        DW_FORM_ADDR => Value::Address(Addr(match unit.address_size {
            4 => reader.u32()? as u64,
            _ => reader.u64()?,
        })),
        DW_FORM_BLOCK1 => {
            let n = reader.u8()? as usize;
            Value::Block(reader.bytes(n)?.to_vec())
        }
        DW_FORM_BLOCK2 => {
            let n = reader.u16()? as usize;
            Value::Block(reader.bytes(n)?.to_vec())
        }
        DW_FORM_BLOCK4 => {
            let n = reader.u32()? as usize;
            Value::Block(reader.bytes(n)?.to_vec())
        }
        DW_FORM_BLOCK | DW_FORM_EXPRLOC => {
            let n = reader.uleb128()? as usize;
            Value::Block(reader.bytes(n)?.to_vec())
        }
        DW_FORM_DATA1 => Value::Unsigned(reader.u8()? as u64),
        DW_FORM_DATA2 => Value::Unsigned(reader.u16()? as u64),
        DW_FORM_DATA4 => Value::Unsigned(reader.u32()? as u64),
        DW_FORM_DATA8 => Value::Unsigned(reader.u64()?),
        DW_FORM_DATA16 => Value::Block(reader.bytes(16)?.to_vec()),
        DW_FORM_SDATA => Value::Signed(reader.sleb128()?),
        DW_FORM_UDATA => Value::Unsigned(reader.uleb128()?),
        DW_FORM_STRING => Value::String(reader.cstr()?),
        DW_FORM_STRP => {
            let at = offset(reader, unit.sixty_four)? as usize;
            Value::String(string_at(unit.sections.str, at))
        }
        DW_FORM_LINE_STRP => {
            let at = offset(reader, unit.sixty_four)? as usize;
            Value::String(string_at(unit.sections.line_str, at))
        }
        DW_FORM_STRX | DW_FORM_STRX1 | DW_FORM_STRX2 | DW_FORM_STRX3 | DW_FORM_STRX4 => {
            let index = match form {
                DW_FORM_STRX1 => reader.u8()? as u64,
                DW_FORM_STRX2 => reader.u16()? as u64,
                DW_FORM_STRX3 => {
                    let b = reader.bytes(3)?;
                    (b[0] as u64) | ((b[1] as u64) << 8) | ((b[2] as u64) << 16)
                }
                DW_FORM_STRX4 => reader.u32()? as u64,
                _ => reader.uleb128()?,
            };
            Value::String(indexed_string(unit, index))
        }
        DW_FORM_ADDRX | DW_FORM_ADDRX1 | DW_FORM_ADDRX2 | DW_FORM_ADDRX3 | DW_FORM_ADDRX4 => {
            let index = match form {
                DW_FORM_ADDRX1 => reader.u8()? as u64,
                DW_FORM_ADDRX2 => reader.u16()? as u64,
                DW_FORM_ADDRX3 => {
                    let b = reader.bytes(3)?;
                    (b[0] as u64) | ((b[1] as u64) << 8) | ((b[2] as u64) << 16)
                }
                DW_FORM_ADDRX4 => reader.u32()? as u64,
                _ => reader.uleb128()?,
            };
            Value::Address(address_from_table(unit, index).unwrap_or(Addr::ZERO))
        }
        DW_FORM_REF1 => Value::Reference(unit.base + reader.u8()? as usize),
        DW_FORM_REF2 => Value::Reference(unit.base + reader.u16()? as usize),
        DW_FORM_REF4 => Value::Reference(unit.base + reader.u32()? as usize),
        DW_FORM_REF8 => Value::Reference(unit.base + reader.u64()? as usize),
        DW_FORM_REF_UDATA => Value::Reference(unit.base + reader.uleb128()? as usize),
        DW_FORM_REF_ADDR => Value::Reference(offset(reader, unit.sixty_four)? as usize),
        DW_FORM_SEC_OFFSET => Value::Unsigned(offset(reader, unit.sixty_four)?),
        DW_FORM_FLAG => Value::Flag(reader.u8()? != 0),
        DW_FORM_FLAG_PRESENT => Value::Flag(true),
        DW_FORM_IMPLICIT_CONST => Value::Signed(implicit),
        DW_FORM_INDIRECT => {
            let actual = reader.uleb128()?;
            return read_form(reader, actual, 0, unit);
        }
        DW_FORM_LOCLISTX | DW_FORM_RNGLISTX => Value::Unsigned(reader.uleb128()?),
        DW_FORM_REF_SUP4 | DW_FORM_STRP_SUP => {
            Value::Unsigned(offset(reader, unit.sixty_four)?)
        }
        // A form this does not know cannot be skipped by length, so the unit
        // stops here rather than reading garbage as attributes.
        _ => return None,
    })
}

fn string_at(section: &[u8], at: usize) -> String {
    let Some(rest) = section.get(at..) else {
        return String::new();
    };
    let end = rest.iter().position(|b| *b == 0).unwrap_or(rest.len());
    String::from_utf8_lossy(&rest[..end]).into_owned()
}

fn indexed_string(unit: &Unit<'_>, index: u64) -> String {
    let size = if unit.sixty_four { 8 } else { 4 };
    let at = unit.str_offsets_base + index as usize * size;
    let Some(bytes) = unit.sections.str_offsets.get(at..at + size) else {
        return String::new();
    };
    let mut reader = Cur::new(bytes, unit.endian);
    let offset = if unit.sixty_four {
        reader.u64().unwrap_or(0) as usize
    } else {
        reader.u32().unwrap_or(0) as usize
    };
    string_at(unit.sections.str, offset)
}

/// Decode the line number program into rows.
fn lines(sections: &Sections<'_>, endian: Endian) -> Vec<LineRow> {
    let mut out = Vec::new();
    let mut reader = Cur::new(sections.line, endian);
    while !reader.is_empty() {
        let before = reader.position();
        if line_program(&mut reader, sections, endian, &mut out).is_none() {
            break;
        }
        if reader.position() <= before {
            break;
        }
    }
    out
}

fn line_program(
    reader: &mut Cur<'_>,
    sections: &Sections<'_>,
    endian: Endian,
    out: &mut Vec<LineRow>,
) -> Option<()> {
    let mut length = reader.u32()? as u64;
    let sixty_four = length == 0xffff_ffff;
    if sixty_four {
        length = reader.u64()?;
    }
    let end = reader
        .position()
        .checked_add(length as usize)
        .filter(|e| *e <= sections.line.len() && *e > reader.position())?;
    let version = reader.u16()?;
    if !(2..=5).contains(&version) {
        reader.seek(end);
        return Some(());
    }
    if version >= 5 {
        let _address_size = reader.u8()?;
        let _segment_selector = reader.u8()?;
    }
    let header_length = offset(reader, sixty_four)?;
    let program_start = reader.position() + header_length as usize;

    let minimum_instruction_length = reader.u8()?;
    let max_ops = if version >= 4 { reader.u8()? } else { 1 };
    let _ = max_ops;
    let default_is_stmt = reader.u8()? != 0;
    let line_base = reader.u8()? as i8 as i64;
    let line_range = reader.u8()?.max(1) as i64;
    let opcode_base = reader.u8()?.max(1);
    let mut standard_lengths = Vec::new();
    for _ in 1..opcode_base {
        standard_lengths.push(reader.u8()?);
    }

    let files = if version >= 5 {
        file_names_v5(reader, sections, endian, sixty_four)?
    } else {
        file_names_v4(reader)?
    };

    reader.seek(program_start);
    let mut state = LineState::new(default_is_stmt);
    let rows_before = out.len();
    while reader.position() < end {
        // Every opcode costs a byte and at most one row, so a program cannot
        // emit more rows than it has bytes.
        if out.len() - rows_before > length as usize {
            return None;
        }
        let opcode = reader.u8()?;
        if opcode == 0 {
            // Extended.
            let size = reader.uleb128()? as usize;
            let at = reader.position();
            let sub = reader.u8()?;
            match sub {
                DW_LNE_END_SEQUENCE => {
                    state.end = true;
                    emit(&mut state, &files, out);
                    state = LineState::new(default_is_stmt);
                }
                DW_LNE_SET_ADDRESS => {
                    let remaining = size - 1;
                    state.address = if remaining == 4 {
                        reader.u32()? as u64
                    } else {
                        reader.u64()?
                    };
                }
                _ => {}
            }
            reader.seek(at + size);
        } else if opcode < opcode_base {
            match opcode {
                DW_LNS_COPY => emit(&mut state, &files, out),
                DW_LNS_ADVANCE_PC => {
                    let n = reader.uleb128()?;
                    state.address += n * minimum_instruction_length.max(1) as u64;
                }
                DW_LNS_ADVANCE_LINE => {
                    let n = reader.sleb128()?;
                    state.line = state.line.saturating_add_signed(n as i32 as i64 as i32);
                }
                DW_LNS_SET_FILE => state.file = reader.uleb128()?,
                DW_LNS_SET_COLUMN => state.column = reader.uleb128()? as u32,
                DW_LNS_NEGATE_STMT => state.statement = !state.statement,
                DW_LNS_CONST_ADD_PC => {
                    let adjusted = (255 - opcode_base) as i64;
                    state.address += (adjusted / line_range) as u64
                        * minimum_instruction_length.max(1) as u64;
                }
                DW_LNS_FIXED_ADVANCE_PC => state.address += reader.u16()? as u64,
                _ => {
                    // An opcode this does not model still declares how many
                    // arguments it takes.
                    let n = standard_lengths
                        .get(opcode as usize - 1)
                        .copied()
                        .unwrap_or(0);
                    for _ in 0..n {
                        reader.uleb128()?;
                    }
                }
            }
        } else {
            let adjusted = (opcode - opcode_base) as i64;
            state.address +=
                (adjusted / line_range) as u64 * minimum_instruction_length.max(1) as u64;
            state.line = state
                .line
                .saturating_add_signed((line_base + adjusted % line_range) as i32);
            emit(&mut state, &files, out);
        }
    }
    reader.seek(end);
    Some(())
}

fn file_names_v4(reader: &mut Cur<'_>) -> Option<Vec<String>> {
    // Include directories, which this does not need but has to step over.
    let limit = reader.0.len();
    let mut seen = 0;
    loop {
        seen += 1;
        if seen > limit {
            return None;
        }
        let s = reader.cstr()?;
        if s.is_empty() {
            break;
        }
    }
    // DWARF 4 numbers files from one, so index zero is a placeholder.
    let mut files = vec![String::new()];
    loop {
        let name = reader.cstr()?;
        if name.is_empty() {
            break;
        }
        reader.uleb128()?; // directory
        reader.uleb128()?; // modification time
        reader.uleb128()?; // length
        files.push(name);
    }
    Some(files)
}

fn file_names_v5(
    reader: &mut Cur<'_>,
    sections: &Sections<'_>,
    endian: Endian,
    sixty_four: bool,
) -> Option<Vec<String>> {
    // Two tables in the same shape: directories, then files. Only the second
    // is wanted, but the first has to be stepped over entry by entry because
    // its size is not declared.
    let directories = entry_table(reader, sections, endian, sixty_four)?;
    let files = entry_table(reader, sections, endian, sixty_four)?;
    let _ = directories;
    Some(files)
}

/// One DWARF 5 entry table: a description of the fields, then the rows.
fn entry_table(
    reader: &mut Cur<'_>,
    sections: &Sections<'_>,
    endian: Endian,
    sixty_four: bool,
) -> Option<Vec<String>> {
    let format_count = reader.u8()?;
    let mut formats = Vec::new();
    for _ in 0..format_count {
        let content = reader.uleb128()?;
        let form = reader.uleb128()?;
        formats.push((content, form));
    }
    let count = reader.uleb128()?;
    // A count from the file is attacker-controlled; a table longer than the
    // section could hold is a malformed file, not a big one.
    if count > sections.line.len() as u64 {
        return None;
    }
    let mut names = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let mut name = String::new();
        for (content, form) in &formats {
            let mut unit = Unit {
                address_size: 8,
                sixty_four,
                base: 0,
                str_offsets_base: 8,
                addr_base: 8,
                endian,
                sections: *sections,
            };
            let value = read_form(reader, *form, 0, &mut unit)?;
            if *content == DW_LNCT_PATH {
                if let Value::String(s) = value {
                    name = s;
                }
            }
        }
        names.push(name);
    }
    Some(names)
}

struct LineState {
    address: u64,
    file: u64,
    line: u32,
    column: u32,
    statement: bool,
    end: bool,
}

impl LineState {
    fn new(default_is_stmt: bool) -> LineState {
        LineState {
            address: 0,
            file: 1,
            line: 1,
            column: 0,
            statement: default_is_stmt,
            end: false,
        }
    }
}

fn emit(state: &mut LineState, files: &[String], out: &mut Vec<LineRow>) {
    out.push(LineRow {
        addr: Addr(state.address),
        file: files
            .get(state.file as usize)
            .cloned()
            .unwrap_or_default(),
        line: state.line,
        column: state.column,
        end: state.end,
        statement: state.statement,
    });
}

// Tags.
const DW_TAG_ARRAY_TYPE: u64 = 0x01;
const DW_TAG_CLASS_TYPE: u64 = 0x02;
const DW_TAG_ENUMERATION_TYPE: u64 = 0x04;
const DW_TAG_FORMAL_PARAMETER: u64 = 0x05;
const DW_TAG_MEMBER: u64 = 0x0d;
const DW_TAG_POINTER_TYPE: u64 = 0x0f;
const DW_TAG_COMPILE_UNIT: u64 = 0x11;
const DW_TAG_STRUCTURE_TYPE: u64 = 0x13;
const DW_TAG_SUBROUTINE_TYPE: u64 = 0x15;
const DW_TAG_TYPEDEF: u64 = 0x16;
const DW_TAG_UNION_TYPE: u64 = 0x17;
const DW_TAG_UNSPECIFIED_PARAMETERS: u64 = 0x18;
const DW_TAG_SUBRANGE_TYPE: u64 = 0x21;
const DW_TAG_BASE_TYPE: u64 = 0x24;
const DW_TAG_CONST_TYPE: u64 = 0x26;
const DW_TAG_ENUMERATOR: u64 = 0x28;
const DW_TAG_SUBPROGRAM: u64 = 0x2e;
const DW_TAG_VARIABLE: u64 = 0x34;
const DW_TAG_VOLATILE_TYPE: u64 = 0x35;
const DW_TAG_RESTRICT_TYPE: u64 = 0x37;

// Attributes.
const DW_AT_LOCATION: u64 = 0x02;
const DW_AT_NAME: u64 = 0x03;
const DW_AT_BYTE_SIZE: u64 = 0x0b;
const DW_AT_BIT_SIZE: u64 = 0x0d;
const DW_AT_LOW_PC: u64 = 0x11;
const DW_AT_HIGH_PC: u64 = 0x12;
const DW_AT_UPPER_BOUND: u64 = 0x2f;
const DW_AT_CONST_VALUE: u64 = 0x1c;
const DW_AT_INLINE: u64 = 0x20;
const DW_AT_COUNT: u64 = 0x37;
const DW_AT_DATA_MEMBER_LOCATION: u64 = 0x38;
const DW_AT_DECL_LINE: u64 = 0x3b;
const DW_AT_ENCODING: u64 = 0x3e;
const DW_AT_TYPE: u64 = 0x49;
const DW_AT_LINKAGE_NAME: u64 = 0x6e;
const DW_AT_STR_OFFSETS_BASE: u64 = 0x72;
const DW_AT_ADDR_BASE: u64 = 0x73;

// Base type encodings.
const DW_ATE_BOOLEAN: u64 = 0x02;
const DW_ATE_FLOAT: u64 = 0x04;
const DW_ATE_SIGNED: u64 = 0x05;
const DW_ATE_SIGNED_CHAR: u64 = 0x06;

// Forms.
const DW_FORM_ADDR: u64 = 0x01;
const DW_FORM_BLOCK2: u64 = 0x03;
const DW_FORM_BLOCK4: u64 = 0x04;
const DW_FORM_DATA2: u64 = 0x05;
const DW_FORM_DATA4: u64 = 0x06;
const DW_FORM_DATA8: u64 = 0x07;
const DW_FORM_STRING: u64 = 0x08;
const DW_FORM_BLOCK: u64 = 0x09;
const DW_FORM_BLOCK1: u64 = 0x0a;
const DW_FORM_DATA1: u64 = 0x0b;
const DW_FORM_FLAG: u64 = 0x0c;
const DW_FORM_SDATA: u64 = 0x0d;
const DW_FORM_STRP: u64 = 0x0e;
const DW_FORM_UDATA: u64 = 0x0f;
const DW_FORM_REF_ADDR: u64 = 0x10;
const DW_FORM_REF1: u64 = 0x11;
const DW_FORM_REF2: u64 = 0x12;
const DW_FORM_REF4: u64 = 0x13;
const DW_FORM_REF8: u64 = 0x14;
const DW_FORM_REF_UDATA: u64 = 0x15;
const DW_FORM_INDIRECT: u64 = 0x16;
const DW_FORM_SEC_OFFSET: u64 = 0x17;
const DW_FORM_EXPRLOC: u64 = 0x18;
const DW_FORM_FLAG_PRESENT: u64 = 0x19;
const DW_FORM_STRX: u64 = 0x1a;
const DW_FORM_ADDRX: u64 = 0x1b;
const DW_FORM_REF_SUP4: u64 = 0x1c;
const DW_FORM_STRP_SUP: u64 = 0x1d;
const DW_FORM_DATA16: u64 = 0x1e;
const DW_FORM_LINE_STRP: u64 = 0x1f;
const DW_FORM_IMPLICIT_CONST: u64 = 0x21;
const DW_FORM_LOCLISTX: u64 = 0x22;
const DW_FORM_RNGLISTX: u64 = 0x23;
const DW_FORM_STRX1: u64 = 0x25;
const DW_FORM_STRX2: u64 = 0x26;
const DW_FORM_STRX3: u64 = 0x27;
const DW_FORM_STRX4: u64 = 0x28;
const DW_FORM_ADDRX1: u64 = 0x29;
const DW_FORM_ADDRX2: u64 = 0x2a;
const DW_FORM_ADDRX3: u64 = 0x2b;
const DW_FORM_ADDRX4: u64 = 0x2c;

// Location expression opcodes.
const DW_OP_ADDR: u8 = 0x03;
const DW_OP_FBREG: u8 = 0x91;
const DW_OP_ADDRX: u8 = 0xa1;

// Line number program opcodes.
const DW_LNS_COPY: u8 = 0x01;
const DW_LNS_ADVANCE_PC: u8 = 0x02;
const DW_LNS_ADVANCE_LINE: u8 = 0x03;
const DW_LNS_SET_FILE: u8 = 0x04;
const DW_LNS_SET_COLUMN: u8 = 0x05;
const DW_LNS_NEGATE_STMT: u8 = 0x06;
const DW_LNS_CONST_ADD_PC: u8 = 0x08;
const DW_LNS_FIXED_ADVANCE_PC: u8 = 0x09;
const DW_LNE_END_SEQUENCE: u8 = 0x01;
const DW_LNE_SET_ADDRESS: u8 = 0x02;
const DW_LNCT_PATH: u64 = 0x01;
