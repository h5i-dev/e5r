//! Reading a Windows program database.
//!
//! Two gates, and they measure different things.
//!
//! The first builds a database byte by byte the way the PE tests build an
//! image. A synthesized database pins exactly which bytes the reader is
//! supposed to have read, so an assertion fails when the layout is misread
//! rather than when a tool is missing, and it is the only gate a checkout with
//! no corpus can run.
//!
//! The second reads the databases `scripts/build-fixtures.sh` produces with
//! clang and rust-lld, and compares them against `llvm-pdbutil`, record by
//! record rather than by counting. An earlier note here said this machine
//! could not produce a database; that was wrong. It has no Windows linker and
//! no CRT, but `-gcodeview` and lld's `/debug` need neither.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use r12e_core::{Addr, AddrRange, Evidence, Strength};
use r12e_format::dwarf::Location;
use r12e_format::{Section, pdb};

/// A little-endian writer, so the builder reads like the layout it produces.
#[derive(Default, Clone)]
struct Buf(Vec<u8>);

impl Buf {
    fn u8(&mut self, v: u8) -> &mut Self {
        self.0.push(v);
        self
    }
    fn u16(&mut self, v: u16) -> &mut Self {
        self.0.extend_from_slice(&v.to_le_bytes());
        self
    }
    fn u32(&mut self, v: u32) -> &mut Self {
        self.0.extend_from_slice(&v.to_le_bytes());
        self
    }
    fn i32(&mut self, v: i32) -> &mut Self {
        self.0.extend_from_slice(&v.to_le_bytes());
        self
    }
    fn bytes(&mut self, v: &[u8]) -> &mut Self {
        self.0.extend_from_slice(v);
        self
    }
    fn cstr(&mut self, v: &str) -> &mut Self {
        self.0.extend_from_slice(v.as_bytes());
        self.0.push(0);
        self
    }
    /// Pad to a four byte boundary with the padding leaves a type record uses,
    /// which say how far to step rather than being skipped by alignment.
    fn pad_leaf(&mut self) -> &mut Self {
        let n = (4 - self.0.len() % 4) % 4;
        for i in (1..=n).rev() {
            self.0.push(0xf0 + i as u8);
        }
        self
    }
    fn pad_zero(&mut self) -> &mut Self {
        while self.0.len() % 4 != 0 {
            self.0.push(0);
        }
        self
    }
}

const IMAGE_BASE: u64 = 0x1_4000_0000;
const TEXT_RVA: u64 = 0x1000;
const DATA_RVA: u64 = 0x2000;
const BLOCK: usize = 1024;
const GUID: [u8; 16] = [
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00,
];

// Stream numbers this builder uses. The first five are fixed by the format.
const GLOBALS: u16 = 5;
const MODULE: u16 = 6;
const NAMES: u16 = 7;
const HEADERS: u16 = 8;

// Type indices, in the order the records are written.
const T_INT4: u32 = 0x0074;
const T_UQUAD: u32 = 0x0023;
const T_REAL32: u32 = 0x0040;
const POINT_FIELDS: u32 = 0x1000;
const POINT: u32 = 0x1001;
const POINT_PTR: u32 = 0x1002;
const ARGS: u32 = 0x1003;
const ADD_PROC: u32 = 0x1004;
const COLOUR_FIELDS: u32 = 0x1005;
const COLOUR: u32 = 0x1006;
const VALUE_FIELDS: u32 = 0x1007;
const VALUE: u32 = 0x1008;
const TABLE: u32 = 0x1009;
const KONST: u32 = 0x100a;
const POINT_FORWARD: u32 = 0x100b;

/// One record: the length, the kind, and the payload the kind describes.
fn record(kind: u16, payload: &[u8], leaf_padding: bool) -> Vec<u8> {
    let mut body = Buf::default();
    body.u16(kind).bytes(payload);
    if leaf_padding {
        body.pad_leaf();
    } else {
        body.pad_zero();
    }
    let mut out = Buf::default();
    out.u16(body.0.len() as u16).bytes(&body.0);
    out.0
}

fn type_record(kind: u16, payload: &[u8]) -> Vec<u8> {
    record(kind, payload, true)
}

fn symbol(kind: u16, payload: &[u8]) -> Vec<u8> {
    record(kind, payload, false)
}

/// One entry of a field list, padded the way the next entry expects to find.
fn entry(kind: u16, payload: &[u8]) -> Vec<u8> {
    let mut out = Buf::default();
    out.u16(kind).bytes(payload).pad_leaf();
    out.0
}

/// The type stream: enough of a graph to exercise every leaf the reader knows.
fn tpi() -> Vec<u8> {
    let mut records = Buf::default();
    let member = |ty: u32, offset: u16, name: &str| {
        let mut b = Buf::default();
        b.u16(3).u32(ty).u16(offset).cstr(name);
        entry(0x150d, &b.0)
    };
    let enumerate = |value: u16, name: &str| {
        let mut b = Buf::default();
        b.u16(3).u16(value).cstr(name);
        entry(0x1502, &b.0)
    };

    // The members of Point, then Point itself.
    let mut fields = Buf::default();
    fields
        .bytes(&member(T_INT4, 0, "x"))
        .bytes(&member(T_INT4, 4, "y"));
    records.bytes(&type_record(0x1203, &fields.0));
    let mut point = Buf::default();
    point
        .u16(2)
        .u16(0)
        .u32(POINT_FIELDS)
        .u32(0)
        .u32(0)
        .u16(8)
        .cstr("Point");
    records.bytes(&type_record(0x1505, &point.0));

    // A pointer to it, an argument list holding that, and the procedure.
    let mut pointer = Buf::default();
    pointer.u32(POINT).u32(0x0004_000c);
    records.bytes(&type_record(0x1002, &pointer.0));
    let mut args = Buf::default();
    args.u32(1).u32(POINT_PTR);
    records.bytes(&type_record(0x1201, &args.0));
    let mut procedure = Buf::default();
    procedure.u32(T_INT4).u8(0).u8(0).u16(1).u32(ARGS);
    records.bytes(&type_record(0x1008, &procedure.0));

    // An enumeration.
    let mut values = Buf::default();
    values
        .bytes(&enumerate(0, "RED"))
        .bytes(&enumerate(1, "GREEN"));
    records.bytes(&type_record(0x1203, &values.0));
    let mut colour = Buf::default();
    colour
        .u16(2)
        .u16(0)
        .u32(T_INT4)
        .u32(COLOUR_FIELDS)
        .cstr("Colour");
    records.bytes(&type_record(0x1507, &colour.0));

    // A union, whose members both start at zero.
    let mut both = Buf::default();
    both.bytes(&member(T_INT4, 0, "i"))
        .bytes(&member(T_REAL32, 0, "f"));
    records.bytes(&type_record(0x1203, &both.0));
    let mut union = Buf::default();
    union.u16(2).u16(0).u32(VALUE_FIELDS).u16(4).cstr("Value");
    records.bytes(&type_record(0x1506, &union.0));

    // An array, which declares a size in bytes where C declares a count.
    let mut array = Buf::default();
    array.u32(T_INT4).u32(T_UQUAD).u16(40).cstr("");
    records.bytes(&type_record(0x1503, &array.0));

    // A qualifier, which changes nothing about the layout.
    let mut modifier = Buf::default();
    modifier.u32(T_INT4).u16(1);
    records.bytes(&type_record(0x1001, &modifier.0));

    // A forward reference to Point, which names it and nothing else.
    let mut forward = Buf::default();
    forward
        .u16(0)
        .u16(0x80)
        .u32(0)
        .u32(0)
        .u32(0)
        .u16(0)
        .cstr("Point");
    records.bytes(&type_record(0x1505, &forward.0));

    let mut out = Buf::default();
    out.u32(20040203)
        .u32(56)
        .u32(POINT_FIELDS)
        .u32(POINT_FORWARD + 1)
        .u32(records.0.len() as u32)
        .u16(0xffff)
        .u16(0xffff)
        .u32(4)
        .u32(0x3ffff)
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0);
    assert_eq!(out.0.len(), 56, "type stream header");
    out.bytes(&records.0);
    out.0
}

/// The item stream, where a modern compiler puts the name and type of a
/// procedure the symbol record only points at.
fn ipi() -> Vec<u8> {
    let mut identity = Buf::default();
    identity.u32(0).u32(ADD_PROC).cstr("add");
    let records = type_record(0x1601, &identity.0);
    let mut out = Buf::default();
    out.u32(20040203)
        .u32(56)
        .u32(0x1000)
        .u32(0x1001)
        .u32(records.len() as u32)
        .u16(0xffff)
        .u16(0xffff)
        .u32(4)
        .u32(0x3ffff)
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0);
    out.bytes(&records);
    out.0
}

/// The module's symbols: one procedure with a local, then its globals.
fn module_symbols() -> Vec<u8> {
    let mut out = Buf::default();
    out.u32(4); // C13 line information follows the symbols
    let mut procedure = Buf::default();
    procedure
        .u32(0)
        .u32(0)
        .u32(0)
        .u32(0x20)
        .u32(0)
        .u32(0x20)
        .u32(0x1000) // the item stream's identity record
        .u32(0)
        .u16(1)
        .u8(0)
        .cstr("add");
    out.bytes(&symbol(0x1147, &procedure.0));
    let mut local = Buf::default();
    local.i32(16).u32(POINT_PTR).u16(335).cstr("p");
    out.bytes(&symbol(0x1111, &local.0));
    out.bytes(&symbol(0x0006, &[]));

    let mut data = |ty: u32, offset: u32, name: &str| {
        let mut b = Buf::default();
        b.u32(ty).u32(offset).u16(2).cstr(name);
        out.bytes(&symbol(0x110d, &b.0));
    };
    data(COLOUR, 0x00, "colour");
    data(TABLE, 0x40, "table");
    data(VALUE, 0x80, "value");
    data(KONST, 0xc0, "konst");
    data(POINT_FORWARD, 0x100, "shape");
    out.0
}

/// The line information: which file, and which line each address came from.
fn module_lines() -> Vec<u8> {
    let mut out = Buf::default();
    let mut checksum = Buf::default();
    checksum.u32(1).u8(0).u8(0).pad_zero();
    out.u32(0xf4)
        .u32(checksum.0.len() as u32)
        .bytes(&checksum.0);

    let mut block = Buf::default();
    block
        .u32(0) // offset into the section
        .u16(1) // the section
        .u16(0) // no columns
        .u32(0x20) // bytes of code covered
        .u32(0) // the checksum entry naming the file
        .u32(2) // rows
        .u32(12 + 2 * 8)
        .u32(0)
        .u32(42 | 0x8000_0000)
        .u32(8)
        .u32(43 | 0x8000_0000);
    out.u32(0xf2).u32(block.0.len() as u32).bytes(&block.0);
    out.0
}

/// The stream the debug directory's GUID is matched against.
fn info() -> Vec<u8> {
    let mut out = Buf::default();
    out.u32(20000404).u32(0x5f5e100).u32(1).bytes(&GUID);
    let mut names = Buf::default();
    names.cstr("/names");
    out.u32(names.0.len() as u32).bytes(&names.0);
    out.u32(1) // entries in use
        .u32(1) // capacity
        .u32(1) // one word of the present vector
        .u32(1)
        .u32(0) // no deleted words
        .u32(0) // the name at offset zero
        .u32(NAMES as u32);
    out.0
}

/// The DBI stream: where the symbols are, and which modules there were.
fn dbi(symbol_bytes: usize, line_bytes: usize) -> Vec<u8> {
    let mut module = Buf::default();
    module
        .u32(0)
        .u16(1)
        .u16(0)
        .i32(0)
        .i32(0x20)
        .u32(0x6000_0020)
        .u16(0)
        .u16(0)
        .u32(0)
        .u32(0)
        .u16(0) // flags
        .u16(MODULE)
        .u32(symbol_bytes as u32)
        .u32(0)
        .u32(line_bytes as u32)
        .u16(1)
        .u16(0)
        .u32(0)
        .u32(0)
        .u32(0)
        .cstr("main.obj")
        .cstr("main.obj")
        .pad_zero();

    let mut optional = Buf::default();
    for n in 0..11u16 {
        optional.u16(if n == 5 { HEADERS } else { 0xffff });
    }

    let mut out = Buf::default();
    out.i32(-1)
        .u32(19990903)
        .u32(1)
        .u16(0xffff) // globals
        .u16(0)
        .u16(0xffff) // publics
        .u16(0)
        .u16(GLOBALS)
        .u16(0)
        .i32(module.0.len() as i32)
        .i32(0) // section contributions
        .i32(0) // section map
        .i32(0) // source files
        .i32(0) // type servers
        .u32(0)
        .i32(optional.0.len() as i32)
        .i32(0) // edit and continue
        .u16(0)
        .u16(0x8664)
        .u32(0);
    assert_eq!(out.0.len(), 64, "DBI header");
    out.bytes(&module.0).bytes(&optional.0);
    out.0
}

/// The global records, which name addresses and say nothing about types.
fn globals() -> Vec<u8> {
    let mut out = Buf::default();
    let mut public = Buf::default();
    public.u32(2).u32(0x30).u16(1).cstr("?add@@YAHPEAUPoint@@Z");
    out.bytes(&symbol(0x110e, &public.0));
    let mut data = Buf::default();
    data.u32(0).u32(0x200).u16(2).cstr("g_counter");
    out.bytes(&symbol(0x110e, &data.0));
    out.0
}

/// The linker's copy of the image's section headers.
fn section_headers() -> Vec<u8> {
    let mut out = Buf::default();
    for (name, rva) in [(b".text\0\0\0", TEXT_RVA), (b".data\0\0\0", DATA_RVA)] {
        out.bytes(name)
            .u32(0x1000)
            .u32(rva as u32)
            .u32(0x1000)
            .u32(0x400)
            .u32(0)
            .u32(0)
            .u16(0)
            .u16(0)
            .u32(0x6000_0020);
    }
    out.0
}

/// The string table the line information indexes into.
fn names() -> Vec<u8> {
    let mut buffer = Buf::default();
    buffer.u8(0).cstr("c:\\src\\main.c");
    let mut out = Buf::default();
    out.u32(0xeffe_effe)
        .u32(1)
        .u32(buffer.0.len() as u32)
        .bytes(&buffer.0);
    out.0
}

/// A whole container: the superblock, the blocks, and the directory that says
/// which of them each stream is scattered across.
fn synth_pdb() -> Vec<u8> {
    let symbols = module_symbols();
    let lines = module_lines();
    let mut module = symbols.clone();
    module.extend_from_slice(&lines);
    let streams = vec![
        Vec::new(), // the previous directory
        info(),
        tpi(),
        dbi(symbols.len(), lines.len()),
        ipi(),
        globals(),
        module,
        names(),
        section_headers(),
    ];

    // Blocks zero to two are the superblock and the two free block maps.
    let mut next = 3usize;
    let mut blocks: Vec<Vec<u32>> = Vec::new();
    for s in &streams {
        let n = s.len().div_ceil(BLOCK);
        blocks.push((0..n).map(|i| (next + i) as u32).collect());
        next += n;
    }
    let mut directory = Buf::default();
    directory.u32(streams.len() as u32);
    for s in &streams {
        directory.u32(s.len() as u32);
    }
    for b in &blocks {
        for n in b {
            directory.u32(*n);
        }
    }
    let map: Vec<u32> = (0..directory.0.len().div_ceil(BLOCK))
        .map(|i| (next + i) as u32)
        .collect();
    next += map.len();
    let map_block = next;
    next += 1;

    let mut file = vec![0u8; next * BLOCK];
    let mut superblock = Buf::default();
    superblock
        .bytes(b"Microsoft C/C++ MSF 7.00\r\n\x1aDS\0\0\0")
        .u32(BLOCK as u32)
        .u32(1)
        .u32(next as u32)
        .u32(directory.0.len() as u32)
        .u32(0)
        .u32(map_block as u32);
    assert_eq!(superblock.0.len(), 56, "superblock");
    file[..superblock.0.len()].copy_from_slice(&superblock.0);
    for (s, b) in streams.iter().zip(&blocks) {
        write_blocks(&mut file, b, s);
    }
    write_blocks(&mut file, &map, &directory.0);
    let mut list = Buf::default();
    for n in &map {
        list.u32(*n);
    }
    let at = map_block * BLOCK;
    file[at..at + list.0.len()].copy_from_slice(&list.0);
    file
}

fn write_blocks(file: &mut [u8], blocks: &[u32], data: &[u8]) {
    for (n, chunk) in blocks.iter().zip(data.chunks(BLOCK)) {
        let at = *n as usize * BLOCK;
        file[at..at + chunk.len()].copy_from_slice(chunk);
    }
}

fn section(name: &str, rva: u64) -> Section {
    Section {
        name: name.to_string(),
        range: AddrRange::sized(Addr(IMAGE_BASE + rva), 0x1000).unwrap(),
        file_offset: 0x400,
        file_size: 0x1000,
        exec: name == ".text",
        write: name == ".data",
        kind: 0,
    }
}

fn image_sections() -> Vec<Section> {
    vec![section(".text", TEXT_RVA), section(".data", DATA_RVA)]
}

#[test]
fn the_identity_is_the_guid_and_the_age_the_image_asked_for() {
    let data = synth_pdb();
    let id = pdb::identity(&data).expect("a database has an identity");
    assert_eq!(id.guid, GUID);
    assert_eq!(id.age, 1);
    assert!(id.matches(&GUID, 1));
    // A rebuild keeps the GUID and bumps the age, and is not the same file.
    assert!(!id.matches(&GUID, 2));
    assert_eq!(id.key(), "443322116655887799AABBCCDDEEFF001");
}

#[test]
fn the_container_hands_back_the_streams_it_was_given() {
    let data = synth_pdb();
    let msf = pdb::Msf::open(&data).expect("opens");
    assert_eq!(msf.count(), 9);
    assert_eq!(msf.stream(NAMES as usize).unwrap(), names());
    assert_eq!(msf.stream(HEADERS as usize).unwrap(), section_headers());
    // A stream the directory does not name is not a stream.
    assert!(msf.stream(9).is_none());
}

#[test]
fn a_procedure_comes_back_with_its_address_size_and_signature() {
    let data = synth_pdb();
    let info = pdb::parse(&data, &image_sections()).expect("parses");
    let at = Addr(IMAGE_BASE + TEXT_RVA);
    let f = info.functions.get(&at).expect("the procedure record");
    assert_eq!(f.name, "add");
    assert_eq!(f.size, Some(0x20));
    // The signature came from the item stream by way of the identity record.
    let returns = f.signature.returns.expect("a return type");
    assert_eq!(info.types.name_of(returns), "int32_t");
    assert_eq!(f.signature.parameters.len(), 1);
    let (_, parameter) = f.signature.parameters[0];
    assert_eq!(info.types.declare(parameter, "p"), "struct Point *p");
    // And the frame-relative local the scope held.
    assert_eq!(f.locals.len(), 1);
    assert_eq!(f.locals[0].name, "p");
    assert_eq!(f.locals[0].frame_offset, Some(16));
    assert_eq!(f.locals[0].ty, parameter);
}

#[test]
fn the_type_graph_is_the_one_the_records_described() {
    let data = synth_pdb();
    let info = pdb::parse(&data, &image_sections()).expect("parses");
    let variable = |name: &str| {
        info.variables
            .values()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("no variable {name}"))
    };

    let point = variable("shape");
    // A forward reference names a type; the members are on the record that
    // defines it, and the reader has to have followed that.
    assert_eq!(
        info.types.definition(point.ty).unwrap(),
        "struct Point { int32_t x; int32_t y; };"
    );
    assert_eq!(
        info.types.definition(variable("colour").ty).unwrap(),
        "enum Colour { RED = 0, GREEN = 1 };"
    );
    assert_eq!(
        info.types.definition(variable("value").ty).unwrap(),
        "union Value { int32_t i; float f; };"
    );
    // The array record gave forty bytes of four byte elements.
    assert_eq!(
        info.types.declare(variable("table").ty, "table"),
        "int32_t table[10]"
    );
    // A qualifier does not change the layout, so it is not carried.
    assert_eq!(info.types.name_of(variable("konst").ty), "int32_t");
}

#[test]
fn public_symbols_name_addresses_no_procedure_record_claimed() {
    let data = synth_pdb();
    let info = pdb::parse(&data, &image_sections()).expect("parses");
    let public = info
        .functions
        .get(&Addr(IMAGE_BASE + TEXT_RVA + 0x30))
        .expect("the public");
    assert_eq!(public.name, "?add@@YAHPEAUPoint@@Z");
    assert_eq!(public.size, None);
    // The procedure record says more about its address than the public does,
    // so it is the one that survives.
    assert_eq!(info.functions[&Addr(IMAGE_BASE + TEXT_RVA)].name, "add");
    let counter = info
        .variables
        .get(&Addr(IMAGE_BASE + DATA_RVA + 0x200))
        .expect("the public data symbol");
    assert_eq!(counter.name, "g_counter");
}

#[test]
fn line_rows_say_where_each_address_came_from() {
    let data = synth_pdb();
    let info = pdb::parse(&data, &image_sections()).expect("parses");
    let at = Addr(IMAGE_BASE + TEXT_RVA);
    let first = info.line_for(at).expect("a row at the entry");
    assert_eq!(first.file, "c:\\src\\main.c");
    assert_eq!(first.line, 42);
    assert!(first.statement);
    assert_eq!(info.line_for(Addr(at.get() + 8)).unwrap().line, 43);
    assert_eq!(info.line_for(Addr(at.get() + 12)).unwrap().line, 43);
    // Past the run the subsection covered there is no row, only its end.
    assert!(info.line_for(Addr(at.get() + 0x20)).is_none());
    // The declaration site is in the line table rather than on the record.
    let f = &info.functions[&at];
    assert_eq!(f.decl_file.as_deref(), Some("c:\\src\\main.c"));
    assert_eq!(f.decl_line, Some(42));
}

#[test]
fn without_the_image_the_linkers_own_section_headers_are_used() {
    let data = synth_pdb();
    let info = pdb::parse(&data, &[]).expect("parses");
    // The database knows only relative addresses, so that is what comes back.
    let f = info.functions.get(&Addr(TEXT_RVA)).expect("the procedure");
    assert_eq!(f.name, "add");
    assert!(info.variables.contains_key(&Addr(DATA_RVA + 0x200)));
    assert_eq!(info.units, 1);
}

#[test]
fn truncation_at_every_length_is_refused_rather_than_survived() {
    let data = synth_pdb();
    let started = Instant::now();
    for n in 0..data.len() {
        // The contract is the loaders': a value or nothing, never a panic and
        // never a loop that does not end.
        let _ = pdb::parse(&data[..n], &image_sections());
        let _ = pdb::identity(&data[..n]);
    }
    // A prefix is never the whole file, so none of them can have parsed into
    // the symbols the whole file has.
    assert!(
        pdb::parse(&data[..data.len() - 1], &[])
            .is_none_or(|i| i.functions.is_empty() || i.lines.is_empty())
    );
    assert!(
        started.elapsed() < Duration::from_secs(30),
        "truncation sweep took {:?}",
        started.elapsed()
    );
}

#[test]
fn corrupted_fields_are_refused_rather_than_believed() {
    let data = synth_pdb();
    let started = Instant::now();
    // Every byte, set to the values that break parsers: a saturating count, a
    // zero length, and a high bit that turns a length negative.
    for n in 0..data.len() {
        for value in [0xff, 0x00, 0x80] {
            let mut case = data.clone();
            case[n] = value;
            let _ = pdb::parse(&case, &image_sections());
            let _ = pdb::identity(&case);
        }
    }
    assert!(
        started.elapsed() < Duration::from_secs(60),
        "corruption sweep took {:?}",
        started.elapsed()
    );
}

#[test]
fn a_lying_count_does_not_exhaust_memory() {
    let data = synth_pdb();
    // The directory says four billion streams, and the superblock says the
    // directory is four billion bytes long. Both are bounded by the size of
    // the file, so both have to be refused rather than allocated for.
    let mut case = data.clone();
    case[44..48].copy_from_slice(&u32::MAX.to_le_bytes());
    let started = Instant::now();
    assert!(pdb::Msf::open(&case).is_none());
    let mut case = data.clone();
    let map = u32::from_le_bytes([case[52], case[53], case[54], case[55]]) as usize;
    let directory = u32::from_le_bytes([case[48 - 4], case[49 - 4], case[50 - 4], case[51 - 4]]);
    assert!(directory > 0, "the directory has bytes");
    // The first word of the directory is the stream count.
    let at = map * BLOCK;
    let block = u32::from_le_bytes([case[at], case[at + 1], case[at + 2], case[at + 3]]) as usize;
    case[block * BLOCK..block * BLOCK + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(pdb::Msf::open(&case).is_none());
    assert!(
        started.elapsed() < Duration::from_secs(2),
        "a lying count took too long"
    );
}

#[test]
fn arbitrary_bytes_are_not_a_database() {
    assert!(pdb::parse(&[], &[]).is_none());
    assert!(pdb::parse(b"not a program database at all", &[]).is_none());
    let mut rng = 0x5eed_1234_abcd_0001u64;
    let mut next = move || {
        rng ^= rng >> 12;
        rng ^= rng << 25;
        rng ^= rng >> 27;
        rng.wrapping_mul(0x2545_f491_4f6c_dd1d)
    };
    let started = Instant::now();
    for _ in 0..2000 {
        // The magic, so the probe actually reaches the container.
        let mut case = b"Microsoft C/C++ MSF 7.00\r\n\x1aDS\0\0\0".to_vec();
        while case.len() < 2048 {
            case.extend_from_slice(&next().to_le_bytes());
        }
        let _ = pdb::parse(&case, &image_sections());
    }
    assert!(
        started.elapsed() < Duration::from_secs(20),
        "random input took {:?}",
        started.elapsed()
    );
}

#[test]
fn a_real_database_reads_when_one_is_present() {
    // There is no Windows toolchain here, so this is a fixture only when
    // somebody points at one. Absent, the synthesized container is the gate.
    let Ok(path) = std::env::var("R12E_PDB") else {
        return;
    };
    let data = std::fs::read(&path).expect("the named database");
    let id = pdb::identity(&data).expect("an identity");
    let info = pdb::parse(&data, &[]).expect("parses");
    println!(
        "{path}: {} age {}, {} functions, {} variables, {} rows, {} types",
        id.key(),
        id.age,
        info.functions.len(),
        info.variables.len(),
        info.lines.len(),
        info.types.len()
    );
    assert!(!info.is_empty(), "a real database describes something");
}

// The corpus gate. Everything below reads databases a real producer wrote and
// compares them against llvm-pdbutil, which is the only external tool on this
// machine that reads the format.

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// Every fixture database, or an empty list when the corpus is not built.
fn fixtures() -> Vec<(String, Vec<u8>)> {
    let Some(dir) = corpus() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for arch in ["x64", "a64"] {
        for opt in ["O0", "O2"] {
            let name = format!("pdb.{arch}.{opt}.pdb");
            if let Ok(data) = std::fs::read(dir.join(&name)) {
                out.push((name, data));
            }
        }
    }
    out
}

/// Ask llvm-pdbutil, so the expectations are not our own reader's opinion.
/// `None` when it is not installed, which downgrades the gate to the
/// synthesized database rather than failing.
fn pdbutil(name: &str, args: &[&str]) -> Option<String> {
    let p = corpus()?.join(name);
    for tool in [
        "llvm-pdbutil",
        "llvm-pdbutil-20",
        "llvm-pdbutil-19",
        "llvm-pdbutil-18",
        "llvm-pdbutil-17",
        "llvm-pdbutil-16",
        "llvm-pdbutil-15",
    ] {
        let Ok(out) = Command::new(tool).arg("dump").args(args).arg(&p).output() else {
            continue;
        };
        if out.status.success() {
            return Some(String::from_utf8_lossy(&out.stdout).into_owned());
        }
    }
    None
}

/// Where each section starts, from the oracle rather than from us, so a
/// `0001:0010` in its output can be compared with an address in ours.
fn oracle_sections(name: &str) -> Option<Vec<u64>> {
    let text = pdbutil(name, &["--section-headers"])?;
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some(hex) = line.strip_suffix(" virtual address") {
            out.push(u64::from_str_radix(hex.trim(), 16).ok()?);
        }
    }
    (!out.is_empty()).then_some(out)
}

/// `0001:0010` as a relative address.
fn oracle_addr(sections: &[u64], spec: &str) -> Option<Addr> {
    let (section, offset) = spec.split_once(':')?;
    let section: usize = section.trim().parse().ok()?;
    let offset: u64 = offset.trim().parse().ok()?;
    Some(Addr(sections.get(section.checked_sub(1)?)? + offset))
}

/// The value of `key = ` in one of the oracle's detail lines.
fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let at = line.find(&format!("{key} = "))? + key.len() + 3;
    let rest = &line[at..];
    Some(rest.split(',').next().unwrap_or(rest).trim())
}

#[test]
fn procedures_match_the_oracle_name_address_and_size() {
    let mut checked = 0;
    for (name, data) in fixtures() {
        let Some(text) = pdbutil(&name, &["--symbols"]) else {
            continue;
        };
        let Some(sections) = oracle_sections(&name) else {
            continue;
        };
        // Every procedure record the oracle saw, as name, entry and length.
        let mut want: Vec<(String, Addr, u64)> = Vec::new();
        let mut lines = text.lines().peekable();
        while let Some(line) = lines.next() {
            let is_proc = line.contains("S_GPROC32 [") || line.contains("S_LPROC32 [");
            if !is_proc {
                continue;
            }
            let symbol = line.rsplit('`').nth(1).expect("a quoted name").to_string();
            let detail = lines.next().expect("a procedure has a detail line");
            let addr = oracle_addr(&sections, field(detail, "addr").expect("addr"));
            let size: u64 = field(detail, "code size")
                .expect("code size")
                .parse()
                .expect("a number");
            want.push((symbol, addr.expect("a section the headers list"), size));
        }
        assert!(!want.is_empty(), "{name}: the oracle saw no procedures");

        let db = pdb::read(&data, &[]).expect("a fixture database parses");
        // Record by record, not by count: a reader that found the right number
        // of the wrong functions would pass a count.
        for (symbol, addr, size) in &want {
            let found = db
                .debug
                .functions
                .get(addr)
                .unwrap_or_else(|| panic!("{name}: nothing at {addr:?} for {symbol}"));
            assert_eq!(&found.name, symbol, "{name}: name at {addr:?}");
            assert_eq!(found.size, Some(*size), "{name}: size of {symbol}");
            checked += 1;
        }
        // And nothing invented: every function we report is one the oracle saw
        // as a procedure or as a public.
        let publics = pdbutil(&name, &["--publics"]).unwrap_or_default();
        for (addr, f) in &db.debug.functions {
            let known = want.iter().any(|(n, a, _)| n == &f.name && a == addr)
                || publics.contains(&format!("`{}`", f.name));
            assert!(known, "{name}: {} at {addr:?} is ours alone", f.name);
        }
    }
    assert!(checked > 0, "no corpus or no llvm-pdbutil: gate not run");
    println!("procedures checked against llvm-pdbutil: {checked}");
}

#[test]
fn public_function_symbols_match_the_oracle() {
    let mut checked = 0;
    for (name, data) in fixtures() {
        let Some(text) = pdbutil(&name, &["--publics"]) else {
            continue;
        };
        let Some(sections) = oracle_sections(&name) else {
            continue;
        };
        let db = pdb::read(&data, &[]).expect("parses");
        let mut lines = text.lines().peekable();
        while let Some(line) = lines.next() {
            if !line.contains("S_PUB32 [") {
                continue;
            }
            let symbol = line.rsplit('`').nth(1).expect("a quoted name").to_string();
            let detail = lines.next().expect("a public has a detail line");
            let addr = oracle_addr(&sections, field(detail, "addr").expect("addr"))
                .expect("a section the headers list");
            let code = field(detail, "flags").is_some_and(|f| f.contains("function"));
            if code {
                let found = db
                    .debug
                    .functions
                    .get(&addr)
                    .unwrap_or_else(|| panic!("{name}: no function at {addr:?} for {symbol}"));
                assert_eq!(found.name, symbol, "{name}: public at {addr:?}");
            } else {
                let found = db
                    .debug
                    .variables
                    .get(&addr)
                    .unwrap_or_else(|| panic!("{name}: no variable at {addr:?} for {symbol}"));
                assert_eq!(found.name, symbol, "{name}: public data at {addr:?}");
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "no corpus or no llvm-pdbutil: gate not run");
    println!("public symbols checked against llvm-pdbutil: {checked}");
}

#[test]
fn frame_relative_locals_match_the_oracle_offsets() {
    let mut checked = 0;
    for (name, data) in fixtures() {
        let Some(text) = pdbutil(&name, &["--symbols"]) else {
            continue;
        };
        let Some(sections) = oracle_sections(&name) else {
            continue;
        };
        // (procedure entry, local name) -> frame offset, as the oracle read it.
        let mut want: BTreeMap<(Addr, String), i64> = BTreeMap::new();
        let mut procedure = None;
        let mut local = None;
        let mut lines = text.lines().peekable();
        while let Some(line) = lines.next() {
            if line.contains("S_GPROC32 [") || line.contains("S_LPROC32 [") {
                let detail = lines.next().expect("a detail line");
                procedure = oracle_addr(&sections, field(detail, "addr").expect("addr"));
                local = None;
            } else if line.contains("S_LOCAL [") {
                local = line.rsplit('`').nth(1).map(str::to_string);
            } else if line.contains("S_DEFRANGE_FRAMEPOINTER_REL [")
                || line.contains("S_DEFRANGE_REGISTER_REL [")
            {
                let detail = lines.next().expect("a detail line");
                // The register relative form only names a frame slot when its
                // register is the one the frame record calls the local base.
                if line.contains("S_DEFRANGE_REGISTER_REL [")
                    && !field(detail, "register").is_some_and(|r| r.ends_with("SP"))
                {
                    continue;
                }
                let offset: i64 = field(detail, "offset")
                    .expect("offset")
                    .parse()
                    .expect("a number");
                if let (Some(p), Some(l)) = (procedure, local.clone()) {
                    want.insert((p, l), offset);
                }
            } else if line.contains("S_INLINESITE [") {
                // Locals inside an inlined call belong to the frame, not to
                // the procedure, and are compared by the inline site gate.
                local = None;
                while let Some(next) = lines.peek() {
                    if next.contains("S_INLINESITE_END [") {
                        break;
                    }
                    lines.next();
                }
            }
        }
        // At -O2 a target can keep every local in a register, and then there
        // is nothing here to compare; the register gate covers those.
        let db = pdb::read(&data, &[]).expect("parses");
        for ((at, local), offset) in &want {
            let f = db
                .debug
                .functions
                .get(at)
                .unwrap_or_else(|| panic!("{name}: no function at {at:?}"));
            let found = f
                .locals
                .iter()
                .find(|l| &l.name == local)
                .unwrap_or_else(|| panic!("{name}: {} has no local {local}", f.name));
            assert_eq!(
                found.frame_offset,
                Some(*offset),
                "{name}: {}::{local}",
                f.name
            );
            checked += 1;
        }
    }
    assert!(checked > 0, "no corpus or no llvm-pdbutil: gate not run");
    println!("frame locals checked against llvm-pdbutil: {checked}");
}

#[test]
fn register_locations_name_the_register_the_oracle_named() {
    // CodeView and DWARF number registers differently and for unrelated
    // reasons, so the translation is worth nothing unless it is checked
    // against something that prints the name. Only the registers these
    // fixtures use are covered here; the rest of the table is unverified and
    // the scorecard must not say otherwise.
    let names: BTreeMap<&str, u16> = BTreeMap::from([
        ("RAX", 0),
        ("EAX", 0),
        ("RDX", 1),
        ("EDX", 1),
        ("RCX", 2),
        ("ECX", 2),
        ("RSP", 7),
        ("ARM64_X0", 0),
        ("ARM64_W0", 0),
        ("ARM64_X1", 1),
        ("ARM64_W1", 1),
        ("ARM64_X8", 8),
        ("ARM64_W8", 8),
        ("ARM64_X9", 9),
        ("ARM64_W9", 9),
        ("ARM64_X10", 10),
        ("ARM64_W10", 10),
        ("ARM64_SP", 31),
    ]);
    let mut checked = 0;
    for (name, data) in fixtures() {
        let Some(text) = pdbutil(&name, &["--symbols"]) else {
            continue;
        };
        let Some(sections) = oracle_sections(&name) else {
            continue;
        };
        // Each range the oracle printed, with the register it named over it.
        let mut want: Vec<(AddrRange, u16, &str)> = Vec::new();
        let mut lines = text.lines().peekable();
        while let Some(line) = lines.next() {
            let Some(reg) = field(line, "register") else {
                continue;
            };
            let Some(number) = names.get(reg) else {
                continue;
            };
            // The plain register form prints its range on the same line; the
            // register relative form prints it on the next one.
            let range = match field(line, "range start") {
                Some(spec) => {
                    let len: u64 = field(line, "length").expect("length").parse().expect("n");
                    AddrRange::sized(oracle_addr(&sections, spec).expect("a section"), len)
                }
                None => lines.next().and_then(|next| {
                    let at = next.find("range = [")? + 9;
                    let (spec, rest) = next[at..].split_once(",+")?;
                    let len: u64 = rest.split(')').next()?.parse().ok()?;
                    AddrRange::sized(oracle_addr(&sections, spec)?, len)
                }),
            };
            want.push((range.expect("a range the oracle printed"), *number, reg));
        }
        if want.is_empty() {
            continue;
        }

        let db = pdb::read(&data, &[]).expect("parses");
        // Every register location we report, keyed by the range it covers.
        let mut ours: Vec<(AddrRange, u16)> = Vec::new();
        for f in db.debug.functions.values() {
            let inner = f.inlines.iter().flat_map(|i| i.locals.iter());
            for l in f.locals.iter().chain(inner) {
                for r in &l.locations {
                    match r.location {
                        Location::Register(n) | Location::RegisterOffset(n, _) => {
                            ours.push((r.range, n));
                        }
                        _ => {}
                    }
                }
            }
        }
        for (range, number, reg) in &want {
            // Our ranges are the oracle's with the record's gaps punched out,
            // so they sit inside it and together reach both of its ends.
            let mine: Vec<AddrRange> = ours
                .iter()
                .filter(|(r, n)| n == number && range.contains_range(*r))
                .map(|(r, _)| *r)
                .collect();
            assert!(
                mine.iter().any(|r| r.start() == range.start())
                    && mine.iter().any(|r| r.end() == range.end()),
                "{name}: the oracle names {reg} over {range:?}, we report {mine:?} for {number}"
            );
            checked += 1;
        }
    }
    assert!(checked > 0, "no corpus or no llvm-pdbutil: gate not run");
    println!("register locations checked against llvm-pdbutil: {checked}");
}

#[test]
fn inlined_frames_match_the_oracle_inlinee_and_extent() {
    let mut checked = 0;
    let mut files = 0;
    for (name, data) in fixtures() {
        let Some(text) = pdbutil(&name, &["--symbols"]) else {
            continue;
        };
        let Some(sections) = oracle_sections(&name) else {
            continue;
        };
        // The oracle prints each site's accumulated code offset and the end it
        // computes, both relative to the procedure the site sits in.
        let mut want: Vec<(Addr, String, u64, u64)> = Vec::new();
        let mut procedure = Addr::ZERO;
        let mut lines = text.lines().peekable();
        while let Some(line) = lines.next() {
            if line.contains("S_GPROC32 [") || line.contains("S_LPROC32 [") {
                let detail = lines.next().expect("a detail line");
                procedure = oracle_addr(&sections, field(detail, "addr").expect("addr"))
                    .expect("a section the headers list");
            } else if line.contains("S_INLINESITE [") || line.contains("S_INLINESITE2 [") {
                let detail = lines.next().expect("a detail line");
                let inlinee = detail
                    .rsplit_once('(')
                    .and_then(|(_, r)| r.split(')').next())
                    .expect("an inlinee name")
                    .to_string();
                // The annotation lines follow until the next record, and a
                // site can describe more than one range.
                let mut start = None;
                while let Some(next) = lines.peek() {
                    if next.contains('|') {
                        break;
                    }
                    let hex = |s: &str| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok();
                    if let Some(at) = next.find("code end 0x") {
                        let end = hex(next[at + 9..].split_whitespace().next().unwrap_or(""));
                        if let (Some(from), Some(end)) = (start.take(), end) {
                            want.push((procedure, inlinee.clone(), from, end));
                        }
                    } else if let Some(at) = next.find("code 0x") {
                        start = hex(next[at + 5..].split_whitespace().next().unwrap_or(""));
                    }
                    lines.next();
                }
            }
        }
        if want.is_empty() {
            continue;
        }
        files += 1;

        let db = pdb::read(&data, &[]).expect("parses");
        for (at, inlinee, start, end) in &want {
            let f = db
                .debug
                .functions
                .get(at)
                .unwrap_or_else(|| panic!("{name}: no function at {at:?}"));
            let range = AddrRange::new(Addr(at.get() + start), Addr(at.get() + end))
                .expect("a range the oracle printed");
            let found = f.inlines.iter().find(|i| i.ranges.contains(&range));
            let found = found.unwrap_or_else(|| {
                panic!("{name}: {} has no inlined frame over {range:?}", f.name)
            });
            assert_eq!(&found.name, inlinee, "{name}: inlinee over {range:?}");
            checked += 1;
        }
        // Nothing invented the other way either.
        let mine: usize = db.debug.functions.values().map(|f| f.inlines.len()).sum();
        assert_eq!(mine, want.len(), "{name}: inlined frame count");
    }
    assert!(files > 0, "no corpus or no llvm-pdbutil: gate not run");
    println!("inlined frames checked against llvm-pdbutil: {checked}");
}

#[test]
fn section_contributions_match_the_oracle() {
    let mut checked = 0;
    for (name, data) in fixtures() {
        let Some(text) = pdbutil(&name, &["--section-contribs"]) else {
            continue;
        };
        let Some(sections) = oracle_sections(&name) else {
            continue;
        };
        let mut want: Vec<(Addr, u64, u16)> = Vec::new();
        for line in text.lines() {
            let Some((_, rest)) = line.split_once("| mod = ") else {
                continue;
            };
            let mut parts = rest.split(',').map(str::trim);
            let module: u16 = parts.next().expect("a module").parse().expect("a number");
            let addr =
                oracle_addr(&sections, parts.next().expect("an address")).expect("a section");
            let size: u64 = parts
                .next()
                .and_then(|s| s.strip_prefix("size = "))
                .expect("a size")
                .parse()
                .expect("a number");
            want.push((addr, size, module));
        }
        assert!(!want.is_empty(), "{name}: the oracle saw no contributions");

        let db = pdb::read(&data, &[]).expect("parses");
        assert_eq!(db.contributions.len(), want.len(), "{name}: count");
        for ((addr, size, module), got) in want.iter().zip(&db.contributions) {
            assert_eq!(got.range.start(), *addr, "{name}: contribution start");
            assert_eq!(got.range.len(), *size, "{name}: contribution size");
            assert_eq!(got.module, *module, "{name}: contribution module");
            assert!(
                (got.module as usize) < db.modules.len(),
                "{name}: a contribution names a module that is not listed"
            );
            checked += 1;
        }
    }
    assert!(checked > 0, "no corpus or no llvm-pdbutil: gate not run");
    println!("section contributions checked against llvm-pdbutil: {checked}");
}

#[test]
fn the_identity_is_the_one_the_image_asks_for() {
    let Some(dir) = corpus() else { return };
    let mut checked = 0;
    for arch in ["x64", "a64"] {
        for opt in ["O0", "O2"] {
            let Ok(image) = std::fs::read(dir.join(format!("pdb.{arch}.{opt}.exe"))) else {
                continue;
            };
            let Ok(data) = std::fs::read(dir.join(format!("pdb.{arch}.{opt}.pdb"))) else {
                continue;
            };
            // The debug directory's CodeView record: the signature, then the
            // GUID and the age the linker stamped into both files.
            let at = image
                .windows(4)
                .position(|w| w == b"RSDS")
                .expect("the image carries a CodeView record");
            let guid: [u8; 16] = image[at + 4..at + 20].try_into().expect("sixteen bytes");
            let age = u32::from_le_bytes(image[at + 20..at + 24].try_into().expect("four"));
            let id = pdb::identity(&data).expect("an identity");
            assert!(
                id.matches(&guid, age),
                "pdb.{arch}.{opt}: the database is not the one the image names"
            );
            assert_eq!(id.age, age);
            checked += 1;
        }
    }
    assert!(checked > 0, "no corpus: gate not run");
}

#[test]
fn hints_are_proven_and_name_what_the_records_named() {
    let mut checked = 0;
    for (name, data) in fixtures() {
        let db = pdb::read(&data, &[]).expect("parses");
        let hints = db.hints();
        assert!(!hints.is_empty(), "{name}: a database proves some entries");
        for h in &hints {
            assert_eq!(h.provenance.best, Evidence::Pdb);
            assert_eq!(h.provenance.strength(), Strength::Proven);
            let f = db.debug.functions.get(&h.addr).expect("a function");
            assert_eq!(h.name.as_deref(), Some(f.name.as_str()));
            assert!(!f.name.is_empty(), "{name}: a hint with no name");
            checked += 1;
        }
    }
    assert!(checked > 0, "no corpus: gate not run");
    println!("function hints from real databases: {checked}");
}

#[test]
fn a_real_database_fills_the_same_shape_dwarf_does() {
    let mut seen = 0;
    for (name, data) in fixtures() {
        let db = pdb::read(&data, &[]).expect("parses");
        assert!(!db.debug.is_empty(), "{name}: describes nothing");
        assert!(db.warnings.is_empty(), "{name}: {:?}", db.warnings);
        assert_eq!(db.debug.units, db.modules.len());
        // The producer string is the one fact that says which compiler wrote
        // it, and both modules of a fixture have one.
        assert!(
            db.modules.iter().any(|m| m.producer.is_some()),
            "{name}: no module named its producer"
        );
        // Types, line rows and locals: a reader that found the functions and
        // nothing else would still pass the boundary gates.
        assert!(db.debug.types.len() > 8, "{name}: no type graph");
        assert!(!db.debug.lines.is_empty(), "{name}: no line rows");
        let locals: usize = db.debug.functions.values().map(|f| f.locals.len()).sum();
        assert!(locals >= 7, "{name}: {locals} locals");
        // Every function the line table covers resolves back to itself.
        for (addr, f) in &db.debug.functions {
            assert_eq!(db.debug.function_at(*addr).map(|f| &f.name), Some(&f.name));
            for frame in &f.inlines {
                for r in &frame.ranges {
                    assert!(f.covers(r.start()), "{name}: {} inline outside", f.name);
                }
            }
        }
        seen += 1;
    }
    assert!(seen > 0, "no corpus: gate not run");
}

#[test]
fn hostile_databases_are_survived_in_bounded_time() {
    // The page directory, the stream directory and the symbol records are the
    // three places a count comes out of the file and decides an allocation.
    let Some((name, base)) = fixtures().into_iter().next() else {
        return;
    };
    let started = Instant::now();
    let mut cases = 0;

    // Truncation at every block boundary, and at a handful of byte offsets
    // inside the first block where the superblock's own fields live.
    for n in (0..base.len()).step_by(4096).chain(0..64) {
        let _ = pdb::read(&base[..n], &[]);
        let _ = pdb::identity(&base[..n]);
        cases += 1;
    }

    // Saturate every little endian word in the superblock and in the first two
    // blocks, which is where the page count, the directory size and the
    // directory's own block list are.
    for at in (0..8192.min(base.len() - 4)).step_by(2) {
        for word in [u32::MAX, u32::MAX / 2, 0, 1] {
            let mut case = base.clone();
            case[at..at + 4].copy_from_slice(&word.to_le_bytes());
            let _ = pdb::read(&case, &[]);
            cases += 1;
        }
    }

    // And the record streams: a length field that claims more than the stream
    // holds, or claims nothing at all, in every stream the file has.
    let msf = pdb::Msf::open(&base).expect("the fixture opens");
    for n in 0..msf.count() {
        let Some(stream) = msf.stream(n) else {
            continue;
        };
        if stream.is_empty() {
            continue;
        }
        // Where the stream's bytes sit in the file, so its record lengths can
        // be rewritten in place.
        let window = stream.len().min(256);
        let Some(at) = base.windows(window).position(|w| w == &stream[..window]) else {
            continue;
        };
        for word in [0u16, 1, 2, u16::MAX, 0x8000] {
            let mut case = base.clone();
            for step in (0..window - 2).step_by(4) {
                case[at + step..at + step + 2].copy_from_slice(&word.to_le_bytes());
            }
            let _ = pdb::read(&case, &[]);
            cases += 1;
        }
    }

    let took = started.elapsed();
    assert!(
        took < Duration::from_secs(20),
        "{name}: {cases} hostile cases took {took:?}"
    );
    println!("{cases} hostile cases in {took:?}");
}
