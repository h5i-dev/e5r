//! Runtime metadata readers, measured against the binaries that carry them.
//!
//! Go is a real oracle: the same program is built twice, once stripped, and
//! every name the `pclntab` reader recovers from the stripped copy is compared
//! against the symbol table of the one that kept it. Rust is a real oracle
//! too: the fixture is compiled from a source file whose name and line numbers
//! the test knows. Objective-C has neither, because there is no macOS linker
//! here, so the image it reads is built by hand.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use r12e_core::Addr;
use r12e_format::metadata;
use r12e_format::{LoadOptions, Object, load};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Object> {
    let p = corpus()?.join(name);
    let data = std::fs::read(&p).ok()?;
    Some(load(&data, &LoadOptions::default()).unwrap_or_else(|e| panic!("loading {name}: {e}")))
}

#[test]
fn the_pclntab_names_what_stripping_removed() {
    let (Some(plain), Some(stripped)) = (open("hello.go"), open("hello.go.stripped")) else {
        return;
    };
    // Go's linker appends an ABI suffix to the ELF symbol of a wrapper; the
    // pclntab spells the same function without it.
    let want: BTreeMap<u64, String> = plain
        .symbols
        .iter()
        .filter(|s| s.is_defined_function())
        // `runtime.text` and its siblings are zero-size markers the linker
        // puts at the ends of the text section, not functions.
        .filter(|s| s.size != 0)
        .map(|s| {
            let n = s.name.trim_end_matches(".abi0").trim_end_matches(".abiinternal");
            (s.addr.get(), n.to_string())
        })
        .collect();
    assert!(want.len() > 500, "a Go binary has more functions than that");
    assert!(
        !stripped.symbols.iter().any(|s| s.is_defined_function()),
        "the stripped copy still has symbols, so this proves nothing"
    );

    let t = metadata::go_pclntab(&stripped).expect("no pclntab in a stripped Go binary");
    assert!(t.version.as_str().starts_with("go1."));
    let got: BTreeMap<u64, String> = t
        .functions
        .iter()
        .map(|f| (f.addr.get(), f.name.clone()))
        .collect();

    let mut agreed = 0usize;
    let mut disagreed = Vec::new();
    for (addr, name) in &want {
        match got.get(addr) {
            Some(g) if g == name => agreed += 1,
            Some(g) => disagreed.push(format!("{addr:#x}: symtab {name}, pclntab {g}")),
            None => {}
        }
    }
    assert!(disagreed.is_empty(), "{disagreed:#?}");
    assert!(
        agreed * 100 >= want.len() * 90,
        "recovered {agreed} of {} names",
        want.len()
    );
    assert_eq!(got.get(&0), None);
}

#[test]
fn the_pclntab_gives_every_function_an_end() {
    let Some(obj) = open("hello.go.stripped") else {
        return;
    };
    let t = metadata::go_pclntab(&obj).expect("no pclntab");
    for f in &t.functions {
        assert!(f.end > f.addr, "{} has no end", f.name);
    }
    for h in t.hints() {
        assert!(h.size.is_some_and(|n| n > 0));
        assert!(h.name.is_some());
    }
    // The table is in address order, which is what lets the end of one
    // function be the start of the next.
    assert!(t.functions.windows(2).all(|w| w[0].addr <= w[1].addr));
}

#[test]
fn the_build_info_says_which_go_built_it() {
    let Some(obj) = open("hello.go.stripped") else {
        return;
    };
    let t = metadata::go_pclntab(&obj).expect("no pclntab");
    let v = t.build_version.expect("no build version");
    assert!(v.starts_with("go1."), "{v}");
    assert!(
        t.module_info.is_some_and(|m| m.contains("r12efixture")),
        "the module line should name the fixture module"
    );
}

#[test]
fn panic_locations_name_the_file_and_line_they_are_in() {
    let Some(obj) = open("panicky") else {
        return;
    };
    let sites = metadata::rust_panic_sites(&obj);
    assert!(!sites.is_empty(), "no panic locations at all");
    for s in &sites {
        assert!(s.file.ends_with(".rs"), "{}", s.file);
        assert!(s.line >= 1 && s.column >= 1);
    }
    // The fixture is compiled from inside the fixture directory, so the name
    // the compiler recorded is the bare one.
    let ours: Vec<_> = sites.iter().filter(|s| s.file == "panicky.rs").collect();
    assert!(!ours.is_empty(), "found {} sites, none ours", sites.len());
    let lines: Vec<u32> = ours.iter().map(|s| s.line).collect();
    assert!(lines.contains(&2), "the indexing panic is on line 2: {lines:?}");
    // And the standard library's own panics come with it.
    assert!(
        sites.iter().any(|s| s.file.contains("core/src")),
        "no library locations, so the scan found only one object file's worth"
    );
}

#[test]
fn a_file_with_no_metadata_yields_none_of_it() {
    let Some(obj) = open("hello.a64.O2") else {
        return;
    };
    assert!(metadata::go_pclntab(&obj).is_none());
    assert!(metadata::objc_classes(&obj).is_empty());
    // A C binary has no Location records; anything found here would be a
    // false positive of the scan.
    assert!(metadata::rust_panic_sites(&obj).is_empty());
}

/// A `pclntab` built byte by byte.
///
/// The only Go on this machine emits one header shape, so the other three are
/// pinned the way `pe.rs` pins a PE: by writing the layout out and asserting
/// the reader recovers exactly what went in.
fn synth_pclntab(magic: u32, ptr: u64, text: u64, funcs: &[(u64, &str)], end: u64) -> Vec<u8> {
    let v118 = matches!(magic, 0xffff_fff0 | 0xffff_fff1);
    let v12 = magic == 0xffff_fffb;
    let field = if v118 { 4 } else { ptr };
    let n = funcs.len() as u64;

    let mut names = Vec::new();
    let mut name_off = Vec::new();
    for (_, name) in funcs {
        name_off.push(names.len() as u64);
        names.extend_from_slice(name.as_bytes());
        names.push(0);
    }
    let align = |v: u64| v.next_multiple_of(8);

    // Before 1.16 the function table sits right behind the count, so the name
    // blob has to follow it; after, the header says where everything is.
    let (header, names_at, functab_at) = if v12 {
        let functab_at = 8 + ptr;
        let names_at = align(functab_at + (n * 2 + 1) * ptr + 4);
        (8 + ptr, names_at, functab_at)
    } else if v118 {
        let names_at = align(8 + 8 * ptr);
        (8 + 8 * ptr, names_at, align(names_at + names.len() as u64))
    } else {
        let names_at = align(8 + 7 * ptr);
        (8 + 7 * ptr, names_at, align(names_at + names.len() as u64))
    };
    // Whichever of the two tables ends last, the `_func` records go behind it.
    let funcs_at = align((names_at + names.len() as u64).max(functab_at + (n * 2 + 1) * field + 4));
    let mut buf = vec![0u8; (funcs_at + n * 16) as usize];

    let put = |buf: &mut Vec<u8>, at: u64, b: &[u8]| {
        buf[at as usize..at as usize + b.len()].copy_from_slice(b);
    };
    let word = |buf: &mut Vec<u8>, at: u64, v: u64, size: u64| {
        if size == 4 {
            put(buf, at, &(v as u32).to_le_bytes());
        } else {
            put(buf, at, &v.to_le_bytes());
        }
    };

    put(&mut buf, 0, &magic.to_le_bytes());
    put(&mut buf, 6, &[1, ptr as u8]);
    word(&mut buf, 8, n, ptr);
    if !v12 {
        word(&mut buf, 8 + ptr, 0, ptr);
        let base = if v118 {
            word(&mut buf, 8 + 2 * ptr, text, ptr);
            3
        } else {
            2
        };
        word(&mut buf, 8 + base * ptr, names_at, ptr);
        word(&mut buf, header - ptr, functab_at, ptr);
    }
    put(&mut buf, names_at, &names);

    for (i, (addr, _)) in funcs.iter().enumerate() {
        let i = i as u64;
        let entry = if v118 { addr - text } else { *addr };
        let func_at = funcs_at + i * 16;
        word(&mut buf, functab_at + 2 * i * field, entry, field);
        word(
            &mut buf,
            functab_at + (2 * i + 1) * field,
            if v12 { func_at } else { func_at - functab_at },
            field,
        );
        // _func: the entry PC again, then the offset of the name.
        word(&mut buf, func_at, entry, field);
        let name_base = if v12 { names_at } else { 0 };
        word(
            &mut buf,
            func_at + field,
            name_base + name_off[i as usize],
            4,
        );
    }
    let last = if v118 { end - text } else { end };
    word(&mut buf, functab_at + 2 * n * field, last, field);
    buf
}

const MAGICS: [u32; 4] = [0xffff_fffb, 0xffff_fffa, 0xffff_fff0, 0xffff_fff1];

fn sample() -> ([(u64, &'static str); 3], u64) {
    (
        [
            (0x1100, "main.main"),
            (0x1180, "runtime.gcBgMarkWorker"),
            (0x1200, "internal/abi.Kind.String"),
        ],
        0x1280,
    )
}

#[test]
fn every_header_shape_round_trips() {
    let (funcs, end) = sample();
    for magic in MAGICS {
        for ptr in [4u64, 8] {
            // The 1.18 layout is 64-bit only in practice, but its entries are
            // 32-bit either way, so both widths have to parse.
            let bytes = synth_pclntab(magic, ptr, 0x1000, &funcs, end);
            let t = metadata::parse_pclntab(&bytes, Some(Addr(0x1000)))
                .unwrap_or_else(|e| panic!("{magic:#x}/{ptr}: {e}"));
            assert_eq!(t.ptr_size, ptr);
            assert_eq!(t.functions.len(), funcs.len(), "{magic:#x}/{ptr}");
            for (i, (addr, name)) in funcs.iter().enumerate() {
                assert_eq!(t.functions[i].addr, Addr(*addr), "{magic:#x}/{ptr}");
                assert_eq!(&t.functions[i].name, name, "{magic:#x}/{ptr}");
            }
            assert_eq!(t.functions[0].end, Addr(funcs[1].0));
            assert_eq!(t.functions[2].end, Addr(end));
            assert!(t.warnings.is_empty(), "{:?}", t.warnings);
        }
    }
}

#[test]
fn a_big_endian_table_reads_the_same_way() {
    let (funcs, end) = sample();
    let mut bytes = synth_pclntab(0xffff_fff1, 8, 0x1000, &funcs, end);
    // Only the magic distinguishes the two orders, so flipping it is enough
    // to prove the rest of the reader follows the magic and not the host.
    bytes[..4].copy_from_slice(&0xffff_fff1u32.to_be_bytes());
    let t = metadata::parse_pclntab(&bytes, Some(Addr(0x1000))).unwrap();
    // The body is still little-endian, so nothing should agree, and the
    // reader must say so rather than invent functions.
    assert!(t.functions.len() < funcs.len() || t.functions[0].addr != Addr(funcs[0].0));
}

#[test]
fn a_count_larger_than_the_table_is_clamped_and_reported() {
    let (funcs, end) = sample();
    for magic in MAGICS {
        let mut bytes = synth_pclntab(magic, 8, 0x1000, &funcs, end);
        bytes[8..16].copy_from_slice(&u64::MAX.to_le_bytes());
        let start = Instant::now();
        let t = metadata::parse_pclntab(&bytes, Some(Addr(0x1000)))
            .unwrap_or_else(|e| panic!("{magic:#x}: {e}"));
        assert!(start.elapsed() < Duration::from_secs(1));
        assert!(
            t.functions.len() < 64,
            "{magic:#x} produced {} functions from {} bytes",
            t.functions.len(),
            bytes.len()
        );
        assert!(
            t.warnings.iter().any(|w| w.contains("room for")),
            "{magic:#x}: no warning about the count"
        );
        for (addr, name) in &funcs {
            assert!(
                t.functions
                    .iter()
                    .any(|f| f.addr == Addr(*addr) && &f.name == name),
                "{magic:#x}: lost a real function while clamping"
            );
        }
    }
}

#[test]
fn a_truncated_or_corrupt_table_returns_and_never_hangs() {
    let (funcs, end) = sample();
    let real: Vec<&str> = funcs.iter().map(|(_, n)| *n).collect();
    let start = Instant::now();
    for magic in MAGICS {
        let full = synth_pclntab(magic, 8, 0x1000, &funcs, end);
        for cut in 0..full.len() {
            if let Ok(t) = metadata::parse_pclntab(&full[..cut], Some(Addr(0x1000))) {
                // A short table may name fewer functions, never other ones.
                for f in &t.functions {
                    assert!(real.contains(&f.name.as_str()), "invented {}", f.name);
                }
            }
        }
        for i in 0..full.len() {
            for bit in [0u32, 3, 7] {
                let mut bad = full.clone();
                bad[i] ^= 1 << bit;
                let _ = metadata::parse_pclntab(&bad, Some(Addr(0x1000)));
            }
        }
    }
    assert!(start.elapsed() < Duration::from_secs(30));
}

const MACHO_BASE: u64 = 0x1_0000_0000;
const TEXT: u64 = MACHO_BASE;
const DATA: u64 = MACHO_BASE + 0x1000;

/// A Mach-O executable carrying two Objective-C classes.
///
/// There is no macOS linker here and a relocatable object has nothing but
/// zeros where its class pointers belong, so the only honest way to test the
/// reader against resolved metadata is to write the resolved metadata out.
/// The section names and structure layouts are the ones clang emits, which the
/// relocatable fixture is checked against separately.
fn synth_objc() -> Vec<u8> {
    let mut f = vec![0u8; 0x2000];
    let put = |f: &mut Vec<u8>, at: u64, b: &[u8]| {
        f[at as usize..at as usize + b.len()].copy_from_slice(b);
    };
    let u32at = |f: &mut Vec<u8>, at: u64, v: u32| put(f, at, &v.to_le_bytes());
    let u64at = |f: &mut Vec<u8>, at: u64, v: u64| put(f, at, &v.to_le_bytes());
    let name16 = |s: &str| {
        let mut b = [0u8; 16];
        b[..s.len()].copy_from_slice(s.as_bytes());
        b
    };

    // mach_header_64: 64-bit little-endian arm64 executable.
    u32at(&mut f, 0, 0xfeed_facf);
    u32at(&mut f, 4, 0x0100_000c);
    u32at(&mut f, 12, 2);
    u32at(&mut f, 16, 2);
    u32at(&mut f, 20, 2 * (72 + 4 * 80));

    let seg = |f: &mut Vec<u8>,
                   at: u64,
                   name: &str,
                   vmaddr: u64,
                   fileoff: u64,
                   prot: u32,
                   sects: &[(&str, u64, u64, u32)]| {
        u32at(f, at, 0x19);
        u32at(f, at + 4, 72 + 80 * sects.len() as u32);
        put(f, at + 8, &name16(name));
        u64at(f, at + 24, vmaddr);
        u64at(f, at + 32, 0x1000);
        u64at(f, at + 40, fileoff);
        u64at(f, at + 48, 0x1000);
        u32at(f, at + 56, 7);
        u32at(f, at + 60, prot);
        u32at(f, at + 64, sects.len() as u32);
        for (i, (sn, addr, size, flags)) in sects.iter().enumerate() {
            let s = at + 72 + 80 * i as u64;
            put(f, s, &name16(sn));
            put(f, s + 16, &name16(name));
            u64at(f, s + 32, *addr);
            u64at(f, s + 40, *size);
            u32at(f, s + 48, (addr - MACHO_BASE) as u32);
            u32at(f, s + 64, *flags);
        }
    };
    seg(
        &mut f,
        32,
        "__TEXT",
        TEXT,
        0,
        5,
        &[
            ("__text", TEXT + 0x400, 0x100, 0x8000_0400),
            ("__objc_methname", TEXT + 0x600, 0x40, 2),
            ("__objc_classname", TEXT + 0x680, 0x20, 2),
            ("__objc_methtype", TEXT + 0x6c0, 0x20, 2),
        ],
    );
    seg(
        &mut f,
        32 + 72 + 4 * 80,
        "__DATA",
        DATA,
        0x1000,
        3,
        &[
            ("__objc_classlist", DATA, 0x10, 0),
            ("__objc_data", DATA + 0x40, 0x100, 0),
            ("__objc_const", DATA + 0x200, 0x400, 0),
            ("__objc_selrefs", DATA + 0x600, 8, 0),
        ],
    );

    put(&mut f, 0x600, b"count\0length\0make\0tiny\0");
    put(&mut f, 0x680, b"Greeter\0Small\0");
    put(&mut f, 0x6c0, b"i16@0:8\0");
    let sel = |off: u64| TEXT + 0x600 + off;
    let types = TEXT + 0x6c0;

    // classlist, then the four class objects it reaches.
    u64at(&mut f, 0x1000, DATA + 0x40);
    u64at(&mut f, 0x1008, DATA + 0x90);
    for (class, meta, ro_at) in [(0x40u64, 0x68u64, 0x200u64), (0x90, 0xb8, 0x300)] {
        u64at(&mut f, 0x1000 + class, DATA + meta);
        u64at(&mut f, 0x1000 + class + 32, DATA + ro_at);
        u64at(&mut f, 0x1000 + meta + 32, DATA + ro_at + 0x80);
    }
    // class_ro_t: flags, then the name and method list behind the fixed head.
    for (ro, meta_flag, name, methods) in [
        (0x200u64, 0u32, 0u64, Some(0x400u64)),
        (0x280, 1, 0, Some(0x480)),
        (0x300, 0, 8, Some(0x500)),
        (0x380, 1, 8, None),
    ] {
        u32at(&mut f, 0x1000 + ro, meta_flag);
        u64at(&mut f, 0x1000 + ro + 24, TEXT + 0x680 + name);
        if let Some(m) = methods {
            u64at(&mut f, 0x1000 + ro + 32, DATA + m);
        }
    }
    // Two pointer-sized method lists.
    for (list, entries) in [
        (0x400u64, vec![(0u64, 0x400u64), (6, 0x420)]),
        (0x480, vec![(13, 0x440)]),
    ] {
        u32at(&mut f, 0x1000 + list, 24);
        u32at(&mut f, 0x1000 + list + 4, entries.len() as u32);
        for (i, (name, imp)) in entries.iter().enumerate() {
            let e = 0x1000 + list + 8 + 24 * i as u64;
            u64at(&mut f, e, sel(*name));
            u64at(&mut f, e + 8, types);
            u64at(&mut f, e + 16, TEXT + imp);
        }
    }
    // One small method list, whose fields are displacements from themselves
    // and whose name field reaches a selector reference rather than the text.
    u32at(&mut f, 0x1500, 12 | 0x8000_0000);
    u32at(&mut f, 0x1504, 1);
    u64at(&mut f, 0x1600, sel(18));
    let entry = DATA + 0x508;
    u32at(&mut f, 0x1508, (DATA + 0x600).wrapping_sub(entry) as u32);
    u32at(&mut f, 0x150c, types.wrapping_sub(entry + 4) as u32);
    u32at(&mut f, 0x1510, (TEXT + 0x460).wrapping_sub(entry + 8) as u32);
    f
}

#[test]
fn objc_class_lists_name_every_implementation() {
    let bytes = synth_objc();
    let obj = load(&bytes, &LoadOptions::default()).expect("the synthesized image does not load");
    let classes = metadata::objc_classes(&obj);
    assert_eq!(classes.len(), 2);
    assert_eq!(classes[0].name, "Greeter");
    assert_eq!(classes[1].name, "Small");

    let hints: BTreeMap<u64, String> = classes
        .iter()
        .flat_map(|c| c.hints())
        .map(|h| (h.addr.get(), h.name.unwrap()))
        .collect();
    let want = [
        (TEXT + 0x400, "-[Greeter count]"),
        (TEXT + 0x420, "-[Greeter length]"),
        (TEXT + 0x440, "+[Greeter make]"),
        (TEXT + 0x460, "-[Small tiny]"),
    ];
    assert_eq!(hints.len(), want.len(), "{hints:#?}");
    for (addr, name) in want {
        assert_eq!(hints.get(&addr).map(String::as_str), Some(name));
    }
    assert!(
        classes[0].methods.iter().all(|m| m.types == "i16@0:8"),
        "the type encodings did not come through"
    );
    assert!(
        metadata::read(&obj).notes.get("objc.methods").is_some_and(|n| n == "4"),
        "the summary disagrees with the class list"
    );
}

#[test]
fn a_relocatable_objc_object_yields_nothing_rather_than_zeros() {
    let Some(obj) = open("greeter.macho.a64.o") else {
        return;
    };
    assert!(
        obj.sections
            .iter()
            .any(|s| s.name.ends_with("__objc_classlist")),
        "the fixture has no ObjC metadata to be careful about"
    );
    // Every pointer in a relocatable object is still a relocation, so the
    // class list is all zeros and the honest answer is no classes at all.
    assert!(metadata::objc_classes(&obj).is_empty());
}

#[test]
fn a_corrupt_objc_image_never_hangs() {
    let full = synth_objc();
    let start = Instant::now();
    for i in (0x1000..full.len()).step_by(7) {
        let mut bad = full.clone();
        bad[i] = 0xff;
        bad[i - 1] = 0xff;
        if let Ok(obj) = load(&bad, &LoadOptions::default()) {
            let _ = metadata::read(&obj);
        }
    }
    assert!(start.elapsed() < Duration::from_secs(30));
}

#[test]
fn mutated_real_files_are_read_or_refused_but_never_hang() {
    // The loader-level fuzz gate cannot reach these readers until a loader
    // calls them, so the same contract is checked here: any bytes in, a value
    // or nothing out, inside a budget.
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let mut rng = move || {
        seed ^= seed >> 12;
        seed ^= seed << 25;
        seed ^= seed >> 27;
        seed.wrapping_mul(0x2545_f491_4f6c_dd1d)
    };
    let start = Instant::now();
    for name in ["hello.go.stripped", "panicky", "greeter.macho.a64.o"] {
        let Some(path) = corpus().map(|d| d.join(name)) else {
            return;
        };
        let Ok(data) = std::fs::read(&path) else {
            continue;
        };
        // Debug information is off: parsing a megabyte of DWARF on every
        // iteration would make this a test of `dwarf.rs` instead.
        let opts = LoadOptions {
            debug_info: false,
            ..LoadOptions::default()
        };
        for _ in 0..32 {
            let mut bad = data.clone();
            for _ in 0..16 {
                let i = (rng() % bad.len() as u64) as usize;
                bad[i] = rng() as u8;
            }
            if let Ok(obj) = load(&bad, &opts) {
                let found = metadata::read(&obj);
                for p in &found.panics {
                    assert!(p.file.ends_with(".rs"));
                }
            }
            assert!(start.elapsed() < Duration::from_secs(60), "{name} is too slow");
        }
    }
}

#[test]
fn a_binary_with_no_section_headers_still_gives_up_its_table() {
    let Some(path) = corpus().map(|d| d.join("hello.go.stripped")) else {
        return;
    };
    let Ok(mut data) = std::fs::read(&path) else {
        return;
    };
    // Remove the section headers the way a packer does: the segments still
    // map, so a scan is the only way left to find anything.
    data[0x28..0x30].copy_from_slice(&0u64.to_le_bytes());
    data[0x3c..0x3e].copy_from_slice(&0u16.to_le_bytes());
    data[0x3e..0x40].copy_from_slice(&0u16.to_le_bytes());
    let obj = load(&data, &LoadOptions::default()).expect("headerless ELF does not load");
    assert!(obj.sections.is_empty(), "the section headers are still there");

    let t = metadata::go_pclntab(&obj).expect("the scan missed the table");
    assert!(t.functions.len() > 500);
    assert!(t.functions.iter().any(|f| f.name == "main.main"));
    assert!(t.build_version.is_some_and(|v| v.starts_with("go1.")));
}
