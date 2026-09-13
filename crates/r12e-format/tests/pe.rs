//! PE and COFF loading.
//!
//! There is no Windows linker on this machine, so the image tests build a PE
//! byte by byte. That is not a weakness: a synthesized image pins exactly what
//! the parser is supposed to read, and the fields that matter (the directories)
//! are the ones a real file would differ from only in scale. COFF objects come
//! from clang, which cross-compiles them without a sysroot.

use std::path::{Path, PathBuf};

use r12e_core::{Addr, Arch, Bits, Evidence};
use r12e_format::{Format, LoadOptions, load, pe};

/// A little-endian writer, so the builder reads like the layout it produces.
#[derive(Default)]
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
    fn u64(&mut self, v: u64) -> &mut Self {
        self.0.extend_from_slice(&v.to_le_bytes());
        self
    }
    fn bytes(&mut self, v: &[u8]) -> &mut Self {
        self.0.extend_from_slice(v);
        self
    }
    fn pad_to(&mut self, n: usize) -> &mut Self {
        while self.0.len() < n {
            self.0.push(0);
        }
        self
    }
    fn at(&mut self, off: usize, v: &[u8]) {
        self.0[off..off + v.len()].copy_from_slice(v);
    }
}

const IMAGE_BASE: u64 = 0x1_4000_0000;
const TEXT_RVA: u32 = 0x1000;
const RDATA_RVA: u32 = 0x2000;
const HEADERS: usize = 0x400;
const TEXT_OFF: usize = 0x400;
const RDATA_OFF: usize = 0x600;

/// A PE32+ executable with two sections, one import, one export and one
/// runtime function.
fn synth_pe() -> Vec<u8> {
    let mut b = Buf::default();
    // DOS header: the magic, then e_lfanew at 0x3c.
    b.bytes(b"MZ").pad_to(0x3c).u32(0x80).pad_to(0x80);
    b.bytes(b"PE\0\0");

    // COFF header.
    b.u16(0x8664) // AMD64
        .u16(2) // sections
        .u32(0) // timestamp
        .u32(0) // symbol table
        .u32(0) // symbols
        .u16(240) // optional header size
        .u16(0x0022); // executable, large address aware

    let opt_start = b.0.len();
    b.u16(0x20b) // PE32+
        .u8(14)
        .u8(0) // linker version
        .u32(0x200) // code size
        .u32(0x200) // initialized data
        .u32(0) // uninitialized
        .u32(TEXT_RVA) // entry point
        .u32(TEXT_RVA) // base of code
        .u64(IMAGE_BASE)
        .u32(0x1000) // section alignment
        .u32(0x200) // file alignment
        .u16(6)
        .u16(0)
        .u16(0)
        .u16(0)
        .u16(6)
        .u16(0) // versions
        .u32(0) // win32 version
        .u32(0x3000) // size of image
        .u32(HEADERS as u32)
        .u32(0) // checksum
        .u16(3) // console subsystem
        .u16(0x0160) // dynamic base, NX, guard CF
        .u64(0x100000)
        .u64(0x1000)
        .u64(0x100000)
        .u64(0x1000)
        .u32(0) // loader flags
        .u32(16); // directory count
    let dirs_at = b.0.len();
    for _ in 0..16 {
        b.u32(0).u32(0);
    }
    assert_eq!(b.0.len() - opt_start, 240, "optional header size");

    // Section headers.
    let sec = |b: &mut Buf, name: &[u8; 8], rva: u32, size: u32, off: u32, ch: u32| {
        b.bytes(name)
            .u32(size)
            .u32(rva)
            .u32(size.next_multiple_of(0x200))
            .u32(off)
            .u32(0)
            .u32(0)
            .u16(0)
            .u16(0)
            .u32(ch);
    };
    sec(
        &mut b,
        b".text\0\0\0",
        TEXT_RVA,
        0x20,
        TEXT_OFF as u32,
        0x6000_0020,
    );
    sec(
        &mut b,
        b".rdata\0\0",
        RDATA_RVA,
        0x140,
        RDATA_OFF as u32,
        0x4000_0040,
    );

    b.pad_to(TEXT_OFF);
    // Enough bytes that every referenced address is executable.
    b.bytes(&[0xc3; 0x200]);

    // .rdata holds the import, export and exception tables.
    b.pad_to(RDATA_OFF);
    let rdata = |off: usize| (RDATA_RVA as usize + (off - RDATA_OFF)) as u32;

    // Import descriptor, then a terminator.
    let import_dir = b.0.len();
    let thunks_rva_slot = import_dir; // filled in below
    b.u32(0).u32(0).u32(0).u32(0).u32(0); // descriptor, patched later
    b.u32(0).u32(0).u32(0).u32(0).u32(0); // terminator

    // Import name table: one thunk pointing at a hint/name entry, then zero.
    let int_at = b.0.len();
    b.u64(0).u64(0);
    // Import address table, same shape.
    let iat_at = b.0.len();
    b.u64(0).u64(0);
    // The hint/name entry and the DLL name.
    let hint_at = b.0.len();
    b.u16(0).bytes(b"CreateFileW\0");
    let dll_at = b.0.len();
    b.bytes(b"KERNEL32.dll\0");

    // Export directory.
    while b.0.len() % 4 != 0 {
        b.u8(0);
    }
    let export_dir = b.0.len();
    let export_names = export_dir + 40;
    let export_ordinals = export_names + 4;
    let export_functions = export_ordinals + 2 + 2;
    let export_name_str = export_functions + 4;
    b.u32(0).u32(0).u16(0).u16(0); // flags, stamp, versions
    b.u32(0); // module name RVA, patched
    b.u32(1); // ordinal base
    b.u32(1) // functions
        .u32(1) // names
        .u32(0) // address table RVA, patched
        .u32(0) // name pointer RVA, patched
        .u32(0); // ordinal table RVA, patched
    assert_eq!(b.0.len(), export_names);
    b.u32(0); // name pointer, patched
    b.u16(0); // ordinal
    b.u16(0); // padding
    assert_eq!(b.0.len(), export_functions);
    b.u32(TEXT_RVA + 8); // exported function RVA
    assert_eq!(b.0.len(), export_name_str);
    b.bytes(b"my.dll\0");
    let exported_name_at = b.0.len();
    b.bytes(b"DoThing\0");

    // Exception directory: two runtime functions.
    while b.0.len() % 4 != 0 {
        b.u8(0);
    }
    let exception_dir = b.0.len();
    b.u32(TEXT_RVA).u32(TEXT_RVA + 8).u32(0);
    b.u32(TEXT_RVA + 8).u32(TEXT_RVA + 0x20).u32(0);
    let exception_size = (b.0.len() - exception_dir) as u32;

    b.pad_to(RDATA_OFF + 0x200);

    // Patch the directory entries and the RVAs that were not known in order.
    let mut d = Buf::default();
    d.u32(rdata(export_dir)).u32(40 + 4 + 4 + 4 + 7 + 8);
    d.u32(rdata(import_dir)).u32(40);
    let import_bytes = d.0.clone();
    b.at(dirs_at, &import_bytes[..8]); // export
    b.at(dirs_at + 8, &import_bytes[8..]); // import
    let mut ex = Buf::default();
    ex.u32(rdata(exception_dir)).u32(exception_size);
    b.at(dirs_at + 24, &ex.0); // exception

    let mut desc = Buf::default();
    desc.u32(rdata(int_at)) // OriginalFirstThunk
        .u32(0)
        .u32(0)
        .u32(rdata(dll_at)) // Name
        .u32(rdata(iat_at)); // FirstThunk
    b.at(thunks_rva_slot, &desc.0);

    let mut thunk = Buf::default();
    thunk.u64(rdata(hint_at) as u64);
    b.at(int_at, &thunk.0);
    b.at(iat_at, &thunk.0);

    let mut ename = Buf::default();
    ename.u32(rdata(export_name_str));
    b.at(export_dir + 12, &ename.0);
    let mut tables = Buf::default();
    tables
        .u32(rdata(export_functions))
        .u32(rdata(export_names))
        .u32(rdata(export_ordinals));
    b.at(export_dir + 28, &tables.0);
    let mut np = Buf::default();
    np.u32(rdata(exported_name_at));
    b.at(export_names, &np.0);

    b.0
}

#[test]
fn a_pe_image_loads() {
    let data = synth_pe();
    let obj = load(&data, &LoadOptions::default()).expect("load");
    assert_eq!(obj.format, Format::Pe);
    assert_eq!(obj.arch, Arch::X86_64);
    assert_eq!(obj.bits, Bits::Bits64);
    assert_eq!(obj.image_base, Addr(IMAGE_BASE));
    assert_eq!(obj.entry, Some(Addr(IMAGE_BASE + TEXT_RVA as u64)));
    assert!(obj.section(".text").is_some());
    assert!(obj.section(".rdata").is_some());
    assert!(obj.memory.is_executable(obj.entry.unwrap()));
    assert_eq!(
        obj.metadata.get("pe.subsystem").map(String::as_str),
        Some("windows console")
    );
    assert_eq!(obj.metadata.get("pe.nx").map(String::as_str), Some("true"));
    assert_eq!(
        obj.metadata.get("pe.aslr").map(String::as_str),
        Some("true")
    );
}

#[test]
fn imports_carry_their_library_and_their_slot() {
    let obj = load(&synth_pe(), &LoadOptions::default()).unwrap();
    let imp = obj
        .imports
        .iter()
        .find(|i| i.name == "CreateFileW")
        .expect("import not found");
    assert_eq!(imp.library.as_deref(), Some("KERNEL32.dll"));
    // The slot is what an indirect call goes through, so it has to be there.
    assert!(imp.thunk.is_some(), "no IAT slot");
}

#[test]
fn exports_are_named_and_become_function_hints() {
    let obj = load(&synth_pe(), &LoadOptions::default()).unwrap();
    let exp = obj
        .exports
        .iter()
        .find(|e| e.name == "DoThing")
        .expect("export not found");
    assert_eq!(exp.addr, Addr(IMAGE_BASE + TEXT_RVA as u64 + 8));
    assert_eq!(exp.ordinal, Some(1));
    assert!(
        obj.function_hints
            .iter()
            .any(|h| h.addr == exp.addr && h.provenance.best == Evidence::Export),
        "the export did not become a hint"
    );
}

#[test]
fn the_exception_directory_gives_exact_boundaries() {
    let obj = load(&synth_pe(), &LoadOptions::default()).unwrap();
    let unwind: Vec<_> = obj
        .function_hints
        .iter()
        .filter(|h| {
            h.provenance.best == Evidence::PeUnwind
                || h.provenance.corroborating.contains(&Evidence::PeUnwind)
        })
        .collect();
    assert_eq!(unwind.len(), 2, "expected two runtime functions");
    assert!(
        unwind.iter().any(|h| h.size == Some(8)),
        "sizes were not recovered"
    );
}

#[test]
fn a_truncated_pe_never_panics() {
    let data = synth_pe();
    let mut n = 1;
    while n < data.len() {
        let _ = load(&data[..n], &LoadOptions::default());
        n = (n * 2).max(n + 37);
    }
}

#[test]
fn corrupted_headers_never_panic() {
    let mut data = synth_pe();
    for i in (0..0x200).step_by(3) {
        let old = data[i];
        for v in [0xff, 0x00, 0x80] {
            data[i] = v;
            let _ = load(&data, &LoadOptions::default());
        }
        data[i] = old;
    }
}

#[test]
fn e_lfanew_pointing_nowhere_is_an_error_not_a_panic() {
    let mut data = synth_pe();
    data[0x3c..0x40].copy_from_slice(&0xffff_fff0u32.to_le_bytes());
    assert!(load(&data, &LoadOptions::default()).is_err());
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

#[test]
fn coff_objects_load_and_get_laid_out() {
    let Some(dir) = corpus() else { return };
    let p = dir.join("wide.coff.o");
    let Ok(data) = std::fs::read(&p) else { return };
    let obj = load(&data, &LoadOptions::default()).expect("coff");
    assert_eq!(obj.arch, Arch::X86_64);
    assert_eq!(
        obj.metadata.get("pe.kind").map(String::as_str),
        Some("object")
    );
    // Sections in an object all claim RVA zero, so the loader has to place
    // them; otherwise every symbol lands on top of every other.
    let text = obj.section(".text").expect("no .text");
    assert!(text.range.start() != Addr::ZERO);
    assert!(obj.memory.is_executable(text.range.start()));
    // Function symbols must follow their section.
    let named: Vec<_> = obj
        .symbols
        .iter()
        .filter(|s| s.is_defined_function())
        .collect();
    assert!(named.len() > 5, "only {} function symbols", named.len());
    for s in named {
        assert!(
            obj.memory.is_executable(s.addr),
            "{} at {} is not executable",
            s.name,
            s.addr
        );
    }
}

#[test]
fn is_pe_does_not_claim_an_elf() {
    let elf = b"\x7fELF\x02\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\xb7\x00";
    assert!(!pe::is_pe(elf));
}
