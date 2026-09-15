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

use e5r_core::{Addr, AddrRange, Endian, Evidence, Provenance, Reader};
use e5r_types::ctype::{Composite, Enumeration, Field, Signature, Type, TypeId, Types};

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
        let bytes = self
            .0
            .cstr_at("dwarf", at, self.0.remaining() as u64)
            .ok()?;
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

    /// The function whose body covers `addr`.
    pub fn function_at(&self, addr: Addr) -> Option<&DebugFunction> {
        let n = self.functions.range(..=addr).next_back().map(|(_, f)| f);
        n.filter(|f| f.covers(addr))
    }

    /// The inlined frames covering `addr`, outermost first.
    ///
    /// The last one is the function whose source the instruction was written
    /// in; the others are the calls that brought it here.
    pub fn inlined_at(&self, addr: Addr) -> Vec<&InlinedFrame> {
        let Some(f) = self.function_at(addr) else {
            return Vec::new();
        };
        let mut found: Vec<&InlinedFrame> = f.inlines.iter().filter(|i| i.covers(addr)).collect();
        found.sort_by_key(|i| i.depth);
        found
    }

    /// The call the compiler recorded as returning to `addr`.
    pub fn call_site_returning_to(&self, addr: Addr) -> Option<&CallSite> {
        self.function_at(addr)?
            .call_sites
            .iter()
            .find(|c| c.return_pc == Some(addr))
    }

    /// Function entries the debug information proves, including the callees
    /// call sites name at an address.
    ///
    /// Not wired into the loaders: `elf.rs` emits its own hints from
    /// [`DebugInfo::functions`]. This is the same list plus the call targets,
    /// for a caller that wants both.
    pub fn hints(&self) -> Vec<crate::FunctionHint> {
        let mut out = Vec::new();
        for (addr, f) in &self.functions {
            if f.name.is_empty() {
                continue;
            }
            out.push(crate::FunctionHint {
                addr: *addr,
                size: f.size.filter(|s| *s > 0),
                name: Some(f.name.clone()),
                provenance: Provenance::new(Evidence::DebugInfo),
            });
        }
        for f in self.functions.values() {
            for c in &f.call_sites {
                let Some(target) = c.target else { continue };
                out.push(crate::FunctionHint {
                    addr: target,
                    size: None,
                    name: c.target_name.clone(),
                    provenance: Provenance::new(Evidence::DebugInfo),
                });
            }
        }
        out
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
    /// The ranges the body occupies when it is not one contiguous piece, which
    /// is what `DW_AT_ranges` says. Empty when `low_pc` and `size` describe it.
    pub ranges: Vec<AddrRange>,
    /// Functions inlined into this one, innermost frames carrying the larger
    /// `depth`. Sorted by start address then depth.
    pub inlines: Vec<InlinedFrame>,
    /// Calls the compiler described, sorted by the address each returns to.
    pub call_sites: Vec<CallSite>,
}

impl DebugFunction {
    /// True when `addr` is inside the body.
    pub fn covers(&self, addr: Addr) -> bool {
        if !self.ranges.is_empty() {
            return self.ranges.iter().any(|r| r.contains(addr));
        }
        match self.size {
            Some(n) => AddrRange::sized(self.low_pc, n).is_some_and(|r| r.contains(addr)),
            // Without a size the entry address is all that is known, and
            // claiming the rest of the image would be an invention.
            None => addr == self.low_pc,
        }
    }
}

/// A call the compiler inlined, and the source it came from.
///
/// An inlined call has no function of its own: the instructions belong to the
/// caller, and only this says a different function's source is sitting inside
/// it.
#[derive(Debug, Clone, Default)]
pub struct InlinedFrame {
    /// The inlined function's name, from the entry its abstract origin names.
    pub name: String,
    /// Its linkage name, when the abstract origin carried one.
    pub linkage_name: Option<String>,
    /// Offset in `.debug_info` of the abstract origin, so a caller can join
    /// this to the out-of-line copy when there is one.
    pub abstract_origin: Option<u64>,
    /// The file the call was written in, resolved through the unit's line
    /// program file table.
    pub call_file: Option<String>,
    /// The line the call was written on.
    pub call_line: Option<u32>,
    /// The column the call was written at.
    pub call_column: Option<u32>,
    /// Where the inlined body starts, when the entry said so separately from
    /// its ranges.
    pub entry_pc: Option<Addr>,
    /// Every range of addresses the inlined body occupies.
    pub ranges: Vec<AddrRange>,
    /// How deep inside other inlined frames this one sits; zero for a call
    /// inlined directly into the function itself.
    pub depth: u32,
    /// Its parameters and locals, in the caller's frame.
    pub locals: Vec<DebugLocal>,
}

impl InlinedFrame {
    /// True when `addr` is inside the inlined body.
    pub fn covers(&self, addr: Addr) -> bool {
        self.ranges.iter().any(|r| r.contains(addr))
    }

    /// The lowest address the frame covers.
    pub fn low_pc(&self) -> Option<Addr> {
        self.ranges.iter().map(|r| r.start()).min()
    }
}

/// One call, as the compiler described it.
///
/// This is the prototype information our own analysis tries to derive: which
/// registers and stack slots hold the arguments at the call, and what the
/// caller put in them.
#[derive(Debug, Clone, Default)]
pub struct CallSite {
    /// The address the call returns to, which is what DWARF keys a call site
    /// by. Absent only for a tail call that never returns here.
    pub return_pc: Option<Addr>,
    /// The address of the call instruction, when the producer recorded one.
    pub call_pc: Option<Addr>,
    /// The callee's entry address, when the entry it names has one.
    pub target: Option<Addr>,
    /// The callee's name, when the entry names a callee at all.
    pub target_name: Option<String>,
    /// Where the callee is found at run time, for an indirect call.
    pub target_location: Option<Location>,
    /// True when the call is a tail call, so control does not come back.
    pub tail_call: bool,
    /// What the caller puts where, one per argument the producer described.
    pub parameters: Vec<CallSiteParameter>,
}

/// One argument of a call, as the compiler described it.
#[derive(Debug, Clone, Default)]
pub struct CallSiteParameter {
    /// Where the callee reads the argument from: a register, or a slot.
    pub location: Option<Location>,
    /// The value the caller passes, as far as the expression says.
    pub value: Option<Location>,
    /// The same value expressed so the callee can still recover it after the
    /// call has clobbered the register: `DW_AT_call_data_value`.
    pub data_value: Option<Location>,
}

/// Where a value lives, as far as a location expression says.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Location {
    /// In a DWARF register number, which is architecture specific.
    Register(u16),
    /// At an offset from the frame base.
    FrameOffset(i64),
    /// At an offset from a register's value.
    RegisterOffset(u16, i64),
    /// At a fixed address.
    Address(Addr),
    /// A constant: the value itself, not storage holding it.
    Constant(i64),
    /// An expression this does not model, kept as the file spells it so a
    /// caller with a full evaluator can still use it.
    Expression(Vec<u8>),
}

/// Where a value lives over one range of the program counter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocationRange {
    /// The addresses this entry applies to.
    pub range: AddrRange,
    /// Where the value is while the program counter is in that range.
    pub location: Location,
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
    /// Where it lives, when one expression covers the whole function.
    pub location: Option<Location>,
    /// Where it lives per range of the program counter, from a location list.
    /// At -O2 a variable that is in a register for part of a function and on
    /// the stack for the rest is the normal case, and this is the only honest
    /// answer for it; `location` is then `None`.
    pub locations: Vec<LocationRange>,
}

impl Default for DebugLocal {
    fn default() -> DebugLocal {
        DebugLocal {
            name: String::new(),
            ty: Types::VOID,
            frame_offset: None,
            location: None,
            locations: Vec::new(),
        }
    }
}

impl DebugLocal {
    /// Where the variable is while the program counter is at `pc`.
    ///
    /// A location list wins over a single location when there is one, because
    /// a single location on a variable that also has a list would be a
    /// contradiction rather than a default.
    pub fn location_at(&self, pc: Addr) -> Option<&Location> {
        if let Some(e) = self.locations.iter().find(|e| e.range.contains(pc)) {
            return Some(&e.location);
        }
        if self.locations.is_empty() {
            return self.location.as_ref();
        }
        None
    }
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
    /// `.debug_ranges`, DWARF 4.
    pub ranges: &'a [u8],
    /// `.debug_loclists`, DWARF 5.
    pub loclists: &'a [u8],
    /// `.debug_loc`, DWARF 4.
    pub loc: &'a [u8],
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
        version,
        base: start,
        str_offsets_base: 8,
        addr_base: 8,
        // The default is the size of the list section's own header, which is
        // what an index is measured from when the unit declares no base.
        rnglists_base: if sixty_four { 20 } else { 12 },
        loclists_base: if sixty_four { 20 } else { 12 },
        low_pc: Addr::ZERO,
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

    // The bases DWARF 5 indirects through live on the unit's own entry, and so
    // does the base address that a range or location pair is measured from.
    let mut stmt_list = None;
    if let Some((_, root)) = entries.iter().next() {
        if let Some(Value::Unsigned(v)) = root.get(DW_AT_STR_OFFSETS_BASE) {
            unit.str_offsets_base = *v as usize;
        }
        if let Some(Value::Unsigned(v)) = root.get(DW_AT_ADDR_BASE) {
            unit.addr_base = *v as usize;
        }
        if let Some(Value::Unsigned(v)) = root.get(DW_AT_RNGLISTS_BASE) {
            unit.rnglists_base = *v as usize;
        }
        if let Some(Value::Unsigned(v)) = root.get(DW_AT_LOCLISTS_BASE) {
            unit.loclists_base = *v as usize;
        }
        if let Some(a) = root.addr_of(DW_AT_LOW_PC) {
            unit.low_pc = a;
        }
        stmt_list = root.unsigned(DW_AT_STMT_LIST);
    }

    // Children by parent, built once. Every walk below wants them, and a scan
    // of the whole unit per entry is what makes a large unit quadratic.
    let mut children: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (at, entry) in &entries {
        if let Some(parent) = entry.parent {
            children.entry(parent).or_default().push(*at);
        }
    }

    // `DW_AT_decl_file` and `DW_AT_call_file` index the file table of this
    // unit's own line program, so it has to be read before either can be a name.
    let files = stmt_list
        .and_then(|at| file_table(sections, endian, at as usize))
        .unwrap_or_default();

    let mut resolver = Resolver {
        entries: &entries,
        children: &children,
        files: &files,
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

    /// An attribute that names an address, in either of the two forms a
    /// producer writes one.
    fn addr_of(&self, attribute: u64) -> Option<Addr> {
        match self.get(attribute)? {
            Value::Address(a) => Some(*a),
            Value::Unsigned(v) => Some(Addr(*v)),
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
    /// An index into a unit's range or location list offset table, which is a
    /// different thing from a section offset and cannot be told apart later.
    ListIndex(u64),
}

struct Unit<'a> {
    address_size: u8,
    sixty_four: bool,
    version: u16,
    base: usize,
    str_offsets_base: usize,
    addr_base: usize,
    rnglists_base: usize,
    loclists_base: usize,
    /// The unit's own `DW_AT_low_pc`, which is what an offset pair in a range
    /// or location list is measured from until an entry says otherwise.
    low_pc: Addr,
    endian: Endian,
    sections: Sections<'a>,
}

/// Build C types from the entries that describe them.
struct Resolver<'a> {
    entries: &'a BTreeMap<usize, Entry>,
    children: &'a BTreeMap<usize, Vec<usize>>,
    files: &'a [String],
    types: &'a mut Types,
    made: BTreeMap<usize, TypeId>,
    unit: &'a Unit<'a>,
}

impl Resolver<'_> {
    fn function(&mut self, at: usize, entry: &Entry) -> Option<DebugFunction> {
        // A function need not be contiguous: `DW_AT_ranges` describes one that
        // the compiler split, and its lowest range is then where it starts.
        let ranges = self.ranges_of(entry);
        let low = match entry.addr_of(DW_AT_LOW_PC) {
            // A relocatable object legitimately puts a function at offset
            // zero, so zero is an address here and not a missing one.
            Some(a) => a,
            // A function split into a hot and a cold piece has ranges and an
            // entry point, and the lowest range is the cold piece as often as
            // not, so the declared entry wins over it.
            None => match entry.addr_of(DW_AT_ENTRY_PC) {
                Some(a) => a,
                None => ranges.iter().map(|r| r.start()).min()?,
            },
        };
        // `high_pc` is an address in DWARF 2 and 3 and a length in 4 and 5,
        // told apart by the form class rather than by the version.
        let size = match entry.get(DW_AT_HIGH_PC) {
            Some(Value::Address(a)) => Some(a.get().saturating_sub(low.get())),
            Some(Value::Unsigned(v)) => Some(*v),
            _ => None,
        };
        let returns = entry.reference(DW_AT_TYPE).and_then(|r| self.type_at(r, 0));
        let mut signature = Signature {
            returns,
            ..Default::default()
        };
        let mut locals = Vec::new();
        for child_at in self.kids(at) {
            let Some(child) = self.entries.get(&child_at).cloned() else {
                continue;
            };
            match child.tag {
                DW_TAG_FORMAL_PARAMETER => {
                    let ty = child
                        .reference(DW_AT_TYPE)
                        .and_then(|r| self.type_at(r, 0))
                        .unwrap_or(Types::VOID);
                    signature
                        .parameters
                        .push((child.string().map(str::to_string), ty));
                    if let Some(local) = self.local(&child) {
                        locals.push(local);
                    }
                }
                DW_TAG_UNSPECIFIED_PARAMETERS => signature.varargs = true,
                DW_TAG_VARIABLE => {
                    if let Some(local) = self.local(&child) {
                        locals.push(local);
                    }
                }
                _ => {}
            }
        }
        let (inlines, call_sites) = self.subtree(at);
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
            decl_file: self.file(entry.unsigned(DW_AT_DECL_FILE)),
            decl_line: entry.unsigned(DW_AT_DECL_LINE),
            inlined: entry.get(DW_AT_INLINE).is_some(),
            ranges,
            inlines,
            call_sites,
        })
    }

    /// One named variable or parameter, with whatever its location says.
    fn local(&mut self, entry: &Entry) -> Option<DebugLocal> {
        // A parameter of an inlined call carries nothing of its own but a
        // reference to the abstract copy, which is where its name and its
        // type live. Without following that, an inlined frame has anonymous
        // arguments, which is most of what makes the frame worth having.
        let origin = entry.reference(DW_AT_ABSTRACT_ORIGIN);
        let name = match entry.string() {
            Some(n) => n.to_string(),
            None => match self.origin_names(origin) {
                (n, _) if !n.is_empty() => n,
                _ => return None,
            },
        };
        let ty = entry
            .reference(DW_AT_TYPE)
            .or_else(|| self.entries.get(&origin?)?.reference(DW_AT_TYPE))
            .and_then(|r| self.type_at(r, 0))
            .unwrap_or(Types::VOID);
        let value = entry.get(DW_AT_LOCATION);
        let (location, locations) = self.locations_of(value);
        Some(DebugLocal {
            name,
            ty,
            frame_offset: frame_offset(value),
            location,
            locations,
        })
    }

    /// The children of an entry, in the order the file wrote them.
    fn kids(&self, at: usize) -> Vec<usize> {
        self.children.get(&at).cloned().unwrap_or_default()
    }

    /// Every inlined frame and call site under a subprogram.
    ///
    /// Both nest: a call site sits inside the inlined body it was made from,
    /// and an inlined body inside another. The walk is iterative because the
    /// nesting depth is a number from the file.
    fn subtree(&mut self, root: usize) -> (Vec<InlinedFrame>, Vec<CallSite>) {
        // (entry, inline depth). Reversed on push so siblings come out in
        // document order, which is what makes the result deterministic.
        let mut stack: Vec<(usize, u32)> = vec![(root, 0)];
        let mut found: Vec<(usize, u64, u32)> = Vec::new();
        let mut visited = 0usize;
        while let Some((at, depth)) = stack.pop() {
            // The tree cannot have more nodes than the unit has entries, so a
            // parent chain that somehow loops still terminates here.
            visited += 1;
            if visited > self.entries.len() {
                break;
            }
            for child_at in self.kids(at).into_iter().rev() {
                let Some(tag) = self.entries.get(&child_at).map(|e| e.tag) else {
                    continue;
                };
                match tag {
                    // A nested function is a function of its own, and its call
                    // sites belong to it rather than to this one.
                    DW_TAG_SUBPROGRAM => continue,
                    DW_TAG_INLINED_SUBROUTINE => {
                        found.push((child_at, tag, depth));
                        stack.push((child_at, depth + 1));
                    }
                    DW_TAG_CALL_SITE | DW_TAG_GNU_CALL_SITE => {
                        found.push((child_at, tag, depth));
                    }
                    _ => stack.push((child_at, depth)),
                }
            }
        }

        let mut inlines = Vec::new();
        let mut call_sites = Vec::new();
        for (at, tag, depth) in found {
            let Some(entry) = self.entries.get(&at).cloned() else {
                continue;
            };
            if tag == DW_TAG_INLINED_SUBROUTINE {
                if let Some(f) = self.inlined(at, &entry, depth) {
                    inlines.push(f);
                }
            } else if let Some(c) = self.call_site(at, &entry) {
                call_sites.push(c);
            }
        }
        inlines.sort_by_key(|i| (i.low_pc().unwrap_or(Addr::MAX), i.depth));
        call_sites.sort_by_key(|c| (c.return_pc.unwrap_or(Addr::MAX), c.call_pc));
        (inlines, call_sites)
    }

    /// One `DW_TAG_inlined_subroutine`.
    fn inlined(&mut self, at: usize, entry: &Entry, depth: u32) -> Option<InlinedFrame> {
        let mut ranges = self.ranges_of(entry);
        if ranges.is_empty() {
            // The contiguous form, which is what a producer writes when the
            // inlined body was not split.
            let low = entry.addr_of(DW_AT_LOW_PC)?;
            let end = match entry.get(DW_AT_HIGH_PC) {
                Some(Value::Address(a)) => *a,
                Some(Value::Unsigned(v)) => low.checked_add(*v)?,
                _ => return None,
            };
            ranges.push(AddrRange::new(low, end)?);
        }
        let origin = entry.reference(DW_AT_ABSTRACT_ORIGIN);
        let (name, linkage_name) = self.origin_names(origin);
        let mut locals = Vec::new();
        for child_at in self.kids(at) {
            let Some(child) = self.entries.get(&child_at).cloned() else {
                continue;
            };
            if matches!(child.tag, DW_TAG_FORMAL_PARAMETER | DW_TAG_VARIABLE) {
                if let Some(local) = self.local(&child) {
                    locals.push(local);
                }
            }
        }
        Some(InlinedFrame {
            name,
            linkage_name,
            abstract_origin: origin.map(|r| r as u64),
            call_file: self.file(entry.unsigned(DW_AT_CALL_FILE)),
            call_line: entry.unsigned(DW_AT_CALL_LINE).map(|v| v as u32),
            call_column: entry.unsigned(DW_AT_CALL_COLUMN).map(|v| v as u32),
            entry_pc: entry.addr_of(DW_AT_ENTRY_PC),
            ranges,
            depth,
            locals,
        })
    }

    /// One `DW_TAG_call_site`, or the GNU spelling of the same thing.
    fn call_site(&mut self, at: usize, entry: &Entry) -> Option<CallSite> {
        // The GNU form predates the standard one and puts the return address
        // in `DW_AT_low_pc` rather than in an attribute of its own.
        let gnu = entry.tag == DW_TAG_GNU_CALL_SITE;
        let return_pc = entry
            .addr_of(DW_AT_CALL_RETURN_PC)
            .or_else(|| gnu.then(|| entry.addr_of(DW_AT_LOW_PC)).flatten());
        let call_pc = entry.addr_of(DW_AT_CALL_PC);
        if return_pc.is_none() && call_pc.is_none() {
            // Without an address the entry says nothing an analysis can use.
            return None;
        }
        let origin = entry
            .reference(DW_AT_CALL_ORIGIN)
            .or_else(|| entry.reference(DW_AT_ABSTRACT_ORIGIN));
        let (name, _) = self.origin_names(origin);
        let target = origin.and_then(|r| self.entries.get(&r)?.addr_of(DW_AT_LOW_PC));
        let target_location = self
            .single_location(entry.get(DW_AT_CALL_TARGET))
            .or_else(|| self.single_location(entry.get(DW_AT_GNU_CALL_SITE_TARGET)));
        let tail_call =
            entry.get(DW_AT_CALL_TAIL_CALL).is_some() || entry.get(DW_AT_GNU_TAIL_CALL).is_some();

        let mut parameters = Vec::new();
        for child_at in self.kids(at) {
            let Some(child) = self.entries.get(&child_at) else {
                continue;
            };
            if !matches!(
                child.tag,
                DW_TAG_CALL_SITE_PARAMETER | DW_TAG_GNU_CALL_SITE_PARAMETER
            ) {
                continue;
            }
            parameters.push(CallSiteParameter {
                location: self.single_location(child.get(DW_AT_LOCATION)),
                value: self
                    .single_location(child.get(DW_AT_CALL_VALUE))
                    .or_else(|| self.single_location(child.get(DW_AT_GNU_CALL_SITE_VALUE))),
                data_value: self
                    .single_location(child.get(DW_AT_CALL_DATA_VALUE))
                    .or_else(|| self.single_location(child.get(DW_AT_GNU_CALL_SITE_DATA_VALUE))),
            });
        }
        Some(CallSite {
            return_pc,
            call_pc,
            target,
            target_name: (!name.is_empty()).then_some(name),
            target_location,
            tail_call,
            parameters,
        })
    }

    /// The name and linkage name of the entry a reference points at, following
    /// the chain an abstract instance or a declaration adds.
    fn origin_names(&self, origin: Option<usize>) -> (String, Option<String>) {
        let mut at = origin;
        let mut name = String::new();
        let mut linkage = None;
        // Eight hops: a chain longer than that is a file playing games.
        for _ in 0..8 {
            let Some(entry) = at.and_then(|r| self.entries.get(&r)) else {
                break;
            };
            if name.is_empty() {
                if let Some(n) = entry.string() {
                    name = n.to_string();
                }
            }
            if linkage.is_none() {
                if let Some(Value::String(s)) = entry.get(DW_AT_LINKAGE_NAME) {
                    linkage = Some(s.clone());
                }
            }
            if !name.is_empty() && linkage.is_some() {
                break;
            }
            at = entry
                .reference(DW_AT_ABSTRACT_ORIGIN)
                .or_else(|| entry.reference(DW_AT_SPECIFICATION));
        }
        (name, linkage)
    }

    /// A file index as the unit's line program spells it.
    fn file(&self, index: Option<u64>) -> Option<String> {
        let name = self.files.get(usize::try_from(index?).ok()?)?;
        (!name.is_empty()).then(|| name.clone())
    }

    /// A location attribute that is one expression rather than a list.
    fn single_location(&self, value: Option<&Value>) -> Option<Location> {
        match value? {
            Value::Block(bytes) => decode_location(bytes, self.unit),
            _ => None,
        }
    }

    /// A location attribute in either shape: one expression, or a list keyed
    /// by program counter.
    fn locations_of(&self, value: Option<&Value>) -> (Option<Location>, Vec<LocationRange>) {
        match value {
            Some(Value::Block(bytes)) => (decode_location(bytes, self.unit), Vec::new()),
            Some(Value::Unsigned(at)) => (None, location_list(self.unit, *at as usize)),
            Some(Value::ListIndex(i)) => (
                None,
                match list_offset(self.unit, *i, true) {
                    Some(at) => location_list(self.unit, at),
                    None => Vec::new(),
                },
            ),
            _ => (None, Vec::new()),
        }
    }

    /// The address ranges an entry's `DW_AT_ranges` names.
    fn ranges_of(&self, entry: &Entry) -> Vec<AddrRange> {
        match entry.get(DW_AT_RANGES) {
            Some(Value::Unsigned(at)) => range_list(self.unit, *at as usize),
            Some(Value::ListIndex(i)) => match list_offset(self.unit, *i, false) {
                Some(at) => range_list(self.unit, at),
                None => Vec::new(),
            },
            _ => Vec::new(),
        }
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
                    .kids(at)
                    .into_iter()
                    .filter_map(|k| self.entries.get(&k))
                    .find(|c| c.tag == DW_TAG_SUBRANGE_TYPE)
                    .and_then(|c| {
                        c.unsigned(DW_AT_COUNT)
                            .or_else(|| c.unsigned(DW_AT_UPPER_BOUND).map(|n| n + 1))
                    });
                self.types.add(Type::Array(inner, count))
            }
            DW_TAG_STRUCTURE_TYPE | DW_TAG_UNION_TYPE | DW_TAG_CLASS_TYPE => {
                // Reserved first, so a field pointing back at this structure
                // finds it instead of recursing forever.
                let placeholder = self.types.reserve(name.as_deref().unwrap_or("anonymous"));
                self.made.insert(at, placeholder);
                let mut fields = Vec::new();
                let children: Vec<Entry> = self
                    .kids(at)
                    .into_iter()
                    .filter_map(|k| self.entries.get(&k))
                    .filter(|c| c.tag == DW_TAG_MEMBER)
                    .cloned()
                    .collect();
                for child in children {
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
                    .kids(at)
                    .into_iter()
                    .filter_map(|k| self.entries.get(&k))
                    .filter(|c| c.tag == DW_TAG_ENUMERATOR)
                    .filter_map(|c| {
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
                    .kids(at)
                    .into_iter()
                    .filter_map(|k| self.entries.get(&k))
                    .cloned()
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
    // Checked: `index` comes out of the file, so a corrupt one multiplies
    // past `usize` and lands the read somewhere it was never meant to be.
    let at = (index as usize)
        .checked_mul(size)
        .and_then(|off| unit.addr_base.checked_add(off))?;
    let bytes = unit.sections.addr.get(at..at.checked_add(size)?)?;
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
fn read_form(reader: &mut Cur<'_>, form: u64, implicit: i64, unit: &mut Unit<'_>) -> Option<Value> {
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
        DW_FORM_LOCLISTX | DW_FORM_RNGLISTX => Value::ListIndex(reader.uleb128()?),
        DW_FORM_REF_SUP4 | DW_FORM_STRP_SUP => Value::Unsigned(offset(reader, unit.sixty_four)?),
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
                // `size` counts the sub-opcode byte, so it cannot be zero in a
                // well-formed program; `reader.seek` below resynchronises
                // whatever this arm does, so a corrupt one is skipped rather
                // than ending the program.
                DW_LNE_SET_ADDRESS if size >= 1 => {
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
                    state.address = state
                        .address
                        .saturating_add(n.saturating_mul(minimum_instruction_length.max(1) as u64));
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
                    state.address = state.address.saturating_add(
                        (adjusted / line_range) as u64 * minimum_instruction_length.max(1) as u64,
                    );
                }
                DW_LNS_FIXED_ADVANCE_PC => {
                    state.address = state.address.saturating_add(reader.u16()? as u64)
                }
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
            state.address = state.address.saturating_add(
                (adjusted / line_range) as u64 * minimum_instruction_length.max(1) as u64,
            );
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
                version: 5,
                base: 0,
                str_offsets_base: 8,
                addr_base: 8,
                rnglists_base: 12,
                loclists_base: 12,
                low_pc: Addr::ZERO,
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
        file: files.get(state.file as usize).cloned().unwrap_or_default(),
        line: state.line,
        column: state.column,
        end: state.end,
        statement: state.statement,
    });
}

/// An address in the unit's address size.
fn read_address(reader: &mut Cur<'_>, unit: &Unit<'_>) -> Option<Addr> {
    Some(Addr(if unit.address_size == 4 {
        reader.u32()? as u64
    } else {
        reader.u64()?
    }))
}

/// The section offset an index into a unit's range or location offset table
/// resolves to.
///
/// DWARF 5 lets a unit reach its lists by index so the attribute stays small;
/// the table sits at the unit's base and its entries are measured from that
/// same base.
fn list_offset(unit: &Unit<'_>, index: u64, locations: bool) -> Option<usize> {
    let (section, base) = if locations {
        (unit.sections.loclists, unit.loclists_base)
    } else {
        (unit.sections.rnglists, unit.rnglists_base)
    };
    let size = if unit.sixty_four { 8 } else { 4 };
    let at = base.checked_add(usize::try_from(index).ok()?.checked_mul(size)?)?;
    let bytes = section.get(at..at.checked_add(size)?)?;
    let mut reader = Cur::new(bytes, unit.endian);
    let value = if unit.sixty_four {
        reader.u64()?
    } else {
        reader.u32()? as u64
    };
    base.checked_add(usize::try_from(value).ok()?)
}

/// The ranges a `DW_AT_ranges` offset names, in whichever section this DWARF
/// version keeps them in.
fn range_list(unit: &Unit<'_>, at: usize) -> Vec<AddrRange> {
    if unit.version >= 5 {
        rnglists(unit, at)
    } else {
        debug_ranges(unit, at)
    }
}

/// A DWARF 5 `.debug_rnglists` list.
fn rnglists(unit: &Unit<'_>, at: usize) -> Vec<AddrRange> {
    let Some(rest) = unit.sections.rnglists.get(at..) else {
        return Vec::new();
    };
    let mut reader = Cur::new(rest, unit.endian);
    let mut base = unit.low_pc;
    let mut out = Vec::new();
    // Every entry costs at least its one-byte kind, so a list cannot hold more
    // entries than the bytes behind it.
    for _ in 0..rest.len() {
        let Some(kind) = reader.u8() else { break };
        let pair = match kind {
            DW_RLE_END_OF_LIST => break,
            DW_RLE_BASE_ADDRESSX => {
                match reader.uleb128().and_then(|i| address_from_table(unit, i)) {
                    Some(a) => base = a,
                    None => break,
                }
                continue;
            }
            DW_RLE_BASE_ADDRESS => {
                match read_address(&mut reader, unit) {
                    Some(a) => base = a,
                    None => break,
                }
                continue;
            }
            DW_RLE_STARTX_ENDX => {
                let (Some(s), Some(e)) = (reader.uleb128(), reader.uleb128()) else {
                    break;
                };
                match (address_from_table(unit, s), address_from_table(unit, e)) {
                    (Some(s), Some(e)) => (s, e),
                    _ => break,
                }
            }
            DW_RLE_STARTX_LENGTH => {
                let (Some(s), Some(n)) = (reader.uleb128(), reader.uleb128()) else {
                    break;
                };
                match address_from_table(unit, s).and_then(|s| Some((s, s.checked_add(n)?))) {
                    Some(p) => p,
                    None => break,
                }
            }
            DW_RLE_OFFSET_PAIR => {
                let (Some(s), Some(e)) = (reader.uleb128(), reader.uleb128()) else {
                    break;
                };
                match (base.checked_add(s), base.checked_add(e)) {
                    (Some(s), Some(e)) => (s, e),
                    _ => break,
                }
            }
            DW_RLE_START_END => {
                let (Some(s), Some(e)) = (
                    read_address(&mut reader, unit),
                    read_address(&mut reader, unit),
                ) else {
                    break;
                };
                (s, e)
            }
            DW_RLE_START_LENGTH => {
                let Some(s) = read_address(&mut reader, unit) else {
                    break;
                };
                match reader.uleb128().and_then(|n| s.checked_add(n)) {
                    Some(e) => (s, e),
                    None => break,
                }
            }
            // A kind this does not know carries an operand of a length only
            // the kind says, so the list stops rather than resynchronizing.
            _ => break,
        };
        if let Some(r) = AddrRange::new(pair.0, pair.1).filter(|r| !r.is_empty()) {
            out.push(r);
        }
    }
    out
}

/// A DWARF 4 `.debug_ranges` list: bare address pairs.
fn debug_ranges(unit: &Unit<'_>, at: usize) -> Vec<AddrRange> {
    let Some(rest) = unit.sections.ranges.get(at..) else {
        return Vec::new();
    };
    let mut reader = Cur::new(rest, unit.endian);
    let mut base = unit.low_pc;
    let mut out = Vec::new();
    let all_ones = if unit.address_size == 4 {
        u32::MAX as u64
    } else {
        u64::MAX
    };
    // Each entry is two addresses, so the bytes bound the count.
    for _ in 0..rest.len() / 2 {
        let (Some(start), Some(end)) = (
            read_address(&mut reader, unit),
            read_address(&mut reader, unit),
        ) else {
            break;
        };
        if start == Addr::ZERO && end == Addr::ZERO {
            break;
        }
        // The all-ones first word is how the format announces a new base
        // rather than a range.
        if start.get() == all_ones {
            base = end;
            continue;
        }
        match (base.checked_add(start.get()), base.checked_add(end.get())) {
            (Some(s), Some(e)) => {
                if let Some(r) = AddrRange::new(s, e).filter(|r| !r.is_empty()) {
                    out.push(r);
                }
            }
            _ => break,
        }
    }
    out
}

/// The entries a location list offset names, in whichever section this DWARF
/// version keeps them in.
fn location_list(unit: &Unit<'_>, at: usize) -> Vec<LocationRange> {
    if unit.version >= 5 {
        loclists(unit, at)
    } else {
        debug_loc(unit, at)
    }
}

/// A DWARF 5 `.debug_loclists` list.
fn loclists(unit: &Unit<'_>, at: usize) -> Vec<LocationRange> {
    let Some(rest) = unit.sections.loclists.get(at..) else {
        return Vec::new();
    };
    let mut reader = Cur::new(rest, unit.endian);
    let mut base = unit.low_pc;
    let mut out = Vec::new();
    for _ in 0..rest.len() {
        let Some(kind) = reader.u8() else { break };
        let pair = match kind {
            DW_LLE_END_OF_LIST => break,
            DW_LLE_BASE_ADDRESSX => {
                match reader.uleb128().and_then(|i| address_from_table(unit, i)) {
                    Some(a) => base = a,
                    None => break,
                }
                continue;
            }
            DW_LLE_BASE_ADDRESS => {
                match read_address(&mut reader, unit) {
                    Some(a) => base = a,
                    None => break,
                }
                continue;
            }
            DW_LLE_STARTX_ENDX => {
                let (Some(s), Some(e)) = (reader.uleb128(), reader.uleb128()) else {
                    break;
                };
                match (address_from_table(unit, s), address_from_table(unit, e)) {
                    (Some(s), Some(e)) => (s, e),
                    _ => break,
                }
            }
            DW_LLE_STARTX_LENGTH => {
                let (Some(s), Some(n)) = (reader.uleb128(), reader.uleb128()) else {
                    break;
                };
                match address_from_table(unit, s).and_then(|s| Some((s, s.checked_add(n)?))) {
                    Some(p) => p,
                    None => break,
                }
            }
            DW_LLE_OFFSET_PAIR => {
                let (Some(s), Some(e)) = (reader.uleb128(), reader.uleb128()) else {
                    break;
                };
                match (base.checked_add(s), base.checked_add(e)) {
                    (Some(s), Some(e)) => (s, e),
                    _ => break,
                }
            }
            DW_LLE_START_END => {
                let (Some(s), Some(e)) = (
                    read_address(&mut reader, unit),
                    read_address(&mut reader, unit),
                ) else {
                    break;
                };
                (s, e)
            }
            DW_LLE_START_LENGTH => {
                let Some(s) = read_address(&mut reader, unit) else {
                    break;
                };
                match reader.uleb128().and_then(|n| s.checked_add(n)) {
                    Some(e) => (s, e),
                    None => break,
                }
            }
            // A default location applies wherever no other entry does, which
            // is not a range and has nowhere to go in the result.
            DW_LLE_DEFAULT_LOCATION => {
                let Some(n) = reader.uleb128() else { break };
                if reader.bytes(n as usize).is_none() {
                    break;
                }
                continue;
            }
            _ => break,
        };
        let Some(n) = reader.uleb128() else { break };
        let Some(expression) = reader.bytes(n as usize) else {
            break;
        };
        let Some(range) = AddrRange::new(pair.0, pair.1).filter(|r| !r.is_empty()) else {
            continue;
        };
        if let Some(location) = decode_location(expression, unit) {
            out.push(LocationRange { range, location });
        }
    }
    out
}

/// A DWARF 4 `.debug_loc` list: address pairs, each with a counted expression.
fn debug_loc(unit: &Unit<'_>, at: usize) -> Vec<LocationRange> {
    let Some(rest) = unit.sections.loc.get(at..) else {
        return Vec::new();
    };
    let mut reader = Cur::new(rest, unit.endian);
    let mut base = unit.low_pc;
    let mut out = Vec::new();
    let all_ones = if unit.address_size == 4 {
        u32::MAX as u64
    } else {
        u64::MAX
    };
    for _ in 0..rest.len() / 2 {
        let (Some(start), Some(end)) = (
            read_address(&mut reader, unit),
            read_address(&mut reader, unit),
        ) else {
            break;
        };
        if start == Addr::ZERO && end == Addr::ZERO {
            break;
        }
        if start.get() == all_ones {
            base = end;
            continue;
        }
        let Some(n) = reader.u16() else { break };
        let Some(expression) = reader.bytes(n as usize) else {
            break;
        };
        let (Some(s), Some(e)) = (base.checked_add(start.get()), base.checked_add(end.get()))
        else {
            break;
        };
        let Some(range) = AddrRange::new(s, e).filter(|r| !r.is_empty()) else {
            continue;
        };
        if let Some(location) = decode_location(expression, unit) {
            out.push(LocationRange { range, location });
        }
    }
    out
}

/// What a location expression says about where a value is.
///
/// The shapes a compiler actually emits for storage are a register, a frame
/// offset, a register offset and a fixed address. Anything else is kept as its
/// bytes rather than half-evaluated, because a half-evaluated expression is a
/// wrong answer that looks like a right one.
fn decode_location(bytes: &[u8], unit: &Unit<'_>) -> Option<Location> {
    if bytes.is_empty() {
        return None;
    }
    // Anything the decoder cannot finish becomes the bytes themselves rather
    // than nothing: dropping the entry would lose the range it covers, which
    // is information even when the expression is not understood.
    Some(decode_known(bytes, unit).unwrap_or_else(|| Location::Expression(bytes.to_vec())))
}

fn decode_known(bytes: &[u8], unit: &Unit<'_>) -> Option<Location> {
    let mut reader = Cur::new(bytes, unit.endian);
    let op = reader.u8()?;
    let decoded = match op {
        DW_OP_ADDR => Location::Address(read_address(&mut reader, unit)?),
        DW_OP_ADDRX => Location::Address(address_from_table(unit, reader.uleb128()?)?),
        DW_OP_FBREG => Location::FrameOffset(reader.sleb128()?),
        DW_OP_REGX => Location::Register(u16::try_from(reader.uleb128()?).ok()?),
        DW_OP_BREGX => {
            let register = u16::try_from(reader.uleb128()?).ok()?;
            Location::RegisterOffset(register, reader.sleb128()?)
        }
        DW_OP_LIT0..=DW_OP_LIT31 => Location::Constant((op - DW_OP_LIT0) as i64),
        DW_OP_REG0..=DW_OP_REG31 => Location::Register((op - DW_OP_REG0) as u16),
        DW_OP_BREG0..=DW_OP_BREG31 => {
            Location::RegisterOffset((op - DW_OP_BREG0) as u16, reader.sleb128()?)
        }
        _ => return Some(Location::Expression(bytes.to_vec())),
    };
    // What is left has to be nothing, or a marker that changes what the value
    // means rather than where it is.
    loop {
        match reader.u8() {
            None => return Some(decoded),
            Some(DW_OP_STACK_VALUE) => {}
            Some(_) => return Some(Location::Expression(bytes.to_vec())),
        }
    }
}

/// The file table of the line program at `at`.
///
/// `DW_AT_decl_file` and `DW_AT_call_file` are indices into this, and without
/// it neither can become a name. Only the header is read: the program itself
/// is walked separately, for the rows.
fn file_table(sections: &Sections<'_>, endian: Endian, at: usize) -> Option<Vec<String>> {
    if at >= sections.line.len() {
        return None;
    }
    let mut reader = Cur::new(sections.line, endian);
    if at != 0 && !reader.seek(at) {
        return None;
    }
    let length = reader.u32()?;
    let sixty_four = length == 0xffff_ffff;
    if sixty_four {
        reader.u64()?;
    }
    let version = reader.u16()?;
    if !(2..=5).contains(&version) {
        return None;
    }
    if version >= 5 {
        reader.u8()?; // address size
        reader.u8()?; // segment selector size
    }
    offset(&mut reader, sixty_four)?; // header length
    reader.u8()?; // minimum instruction length
    if version >= 4 {
        reader.u8()?; // maximum operations per instruction
    }
    reader.u8()?; // default is_stmt
    reader.u8()?; // line base
    reader.u8()?; // line range
    let opcode_base = reader.u8()?.max(1);
    for _ in 1..opcode_base {
        reader.u8()?;
    }
    if version >= 5 {
        file_names_v5(&mut reader, sections, endian, sixty_four)
    } else {
        file_names_v4(&mut reader)
    }
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
const DW_TAG_INLINED_SUBROUTINE: u64 = 0x1d;
const DW_TAG_CALL_SITE: u64 = 0x48;
const DW_TAG_CALL_SITE_PARAMETER: u64 = 0x49;
/// The GNU spelling, which is what a producer writing DWARF 4 emits.
const DW_TAG_GNU_CALL_SITE: u64 = 0x4109;
const DW_TAG_GNU_CALL_SITE_PARAMETER: u64 = 0x410a;
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
const DW_AT_STMT_LIST: u64 = 0x10;
const DW_AT_DECL_FILE: u64 = 0x3a;
const DW_AT_ABSTRACT_ORIGIN: u64 = 0x31;
const DW_AT_SPECIFICATION: u64 = 0x47;
const DW_AT_ENTRY_PC: u64 = 0x52;
const DW_AT_RANGES: u64 = 0x55;
const DW_AT_CALL_COLUMN: u64 = 0x57;
const DW_AT_CALL_FILE: u64 = 0x58;
const DW_AT_CALL_LINE: u64 = 0x59;
const DW_AT_RNGLISTS_BASE: u64 = 0x74;
const DW_AT_LOCLISTS_BASE: u64 = 0x8c;
const DW_AT_CALL_RETURN_PC: u64 = 0x7d;
const DW_AT_CALL_VALUE: u64 = 0x7e;
const DW_AT_CALL_ORIGIN: u64 = 0x7f;
const DW_AT_CALL_PC: u64 = 0x81;
const DW_AT_CALL_TAIL_CALL: u64 = 0x82;
const DW_AT_CALL_TARGET: u64 = 0x83;
const DW_AT_CALL_DATA_VALUE: u64 = 0x86;
// The GNU call site attributes, which a DWARF 4 producer uses instead.
const DW_AT_GNU_CALL_SITE_VALUE: u64 = 0x2111;
const DW_AT_GNU_CALL_SITE_DATA_VALUE: u64 = 0x2112;
const DW_AT_GNU_CALL_SITE_TARGET: u64 = 0x2113;
const DW_AT_GNU_TAIL_CALL: u64 = 0x2115;

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
const DW_OP_LIT0: u8 = 0x30;
const DW_OP_LIT31: u8 = 0x4f;
const DW_OP_REG0: u8 = 0x50;
const DW_OP_REG31: u8 = 0x6f;
const DW_OP_BREG0: u8 = 0x70;
const DW_OP_BREG31: u8 = 0x8f;
const DW_OP_REGX: u8 = 0x90;
const DW_OP_FBREG: u8 = 0x91;
const DW_OP_BREGX: u8 = 0x92;
const DW_OP_STACK_VALUE: u8 = 0x9f;
const DW_OP_ADDRX: u8 = 0xa1;

// Range list entry kinds, DWARF 5.
const DW_RLE_END_OF_LIST: u8 = 0x00;
const DW_RLE_BASE_ADDRESSX: u8 = 0x01;
const DW_RLE_STARTX_ENDX: u8 = 0x02;
const DW_RLE_STARTX_LENGTH: u8 = 0x03;
const DW_RLE_OFFSET_PAIR: u8 = 0x04;
const DW_RLE_BASE_ADDRESS: u8 = 0x05;
const DW_RLE_START_END: u8 = 0x06;
const DW_RLE_START_LENGTH: u8 = 0x07;

// Location list entry kinds, DWARF 5.
const DW_LLE_END_OF_LIST: u8 = 0x00;
const DW_LLE_BASE_ADDRESSX: u8 = 0x01;
const DW_LLE_STARTX_ENDX: u8 = 0x02;
const DW_LLE_STARTX_LENGTH: u8 = 0x03;
const DW_LLE_OFFSET_PAIR: u8 = 0x04;
const DW_LLE_DEFAULT_LOCATION: u8 = 0x05;
const DW_LLE_BASE_ADDRESS: u8 = 0x06;
const DW_LLE_START_END: u8 = 0x07;
const DW_LLE_START_LENGTH: u8 = 0x08;

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
