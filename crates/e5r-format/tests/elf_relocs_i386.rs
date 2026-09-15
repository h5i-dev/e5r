//! i386 relocations, against readelf entry for entry.
//!
//! The oracle is not a count. For every relocation `readelf -r` lists, this
//! recomputes the psABI formula from `readelf -s` and the addresses the loader
//! chose, then reads back the bytes the loader wrote and demands they agree.
//! A count would pass while every displacement was off by the addend, which is
//! precisely the mistake `REL` invites: i386 has no `r_addend` field, so the
//! addend is whatever the assembler already encoded at the place.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use e5r_core::{Addr, Arch, Bits};
use e5r_format::{LoadOptions, Object, load};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<(Object, Vec<u8>)> {
    let p = corpus()?.join(name);
    let data = std::fs::read(&p).ok()?;
    let obj = load(&data, &LoadOptions::default())
        .unwrap_or_else(|e| panic!("loading {}: {e}", p.display()));
    Some((obj, data))
}

fn tool(name: &str, fixture: &str, args: &[&str]) -> Option<String> {
    let p = corpus()?.join(fixture);
    let out = Command::new(name).args(args).arg(&p).output().ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The fixtures this file is about. Both memory models, because the relocation
/// types barely overlap between them.
const FIXTURES: [&str; 4] = [
    "relocs32.nopic.O0.o",
    "relocs32.nopic.O2.o",
    "relocs32.pic.O0.o",
    "relocs32.pic.O2.o",
];

/// One row of `readelf -s`: what the symbol table says about a symbol.
struct OracleSym {
    /// `st_value`, before any layout is applied.
    value: u64,
    /// The section index, or `None` for UND, ABS and COMMON.
    section: Option<usize>,
    name: String,
}

fn oracle_symbols(fixture: &str) -> HashMap<u64, OracleSym> {
    let mut out = HashMap::new();
    let Some(txt) = tool("readelf", fixture, &["-sW"]) else {
        return out;
    };
    let mut in_symtab = false;
    for line in txt.lines() {
        if line.contains("Symbol table") {
            in_symtab = line.contains(".symtab");
            continue;
        }
        if !in_symtab {
            continue;
        }
        // "    12: 00000000    17 FUNC    GLOBAL DEFAULT    2 leaf"
        let Some((idx, rest)) = line.trim().split_once(':') else {
            continue;
        };
        let Ok(index) = idx.trim().parse::<u64>() else {
            continue;
        };
        let f: Vec<&str> = rest.split_whitespace().collect();
        if f.len() < 6 {
            continue;
        }
        let Ok(value) = u64::from_str_radix(f[0], 16) else {
            continue;
        };
        let section = f[5].parse::<usize>().ok();
        out.insert(
            index,
            OracleSym {
                value,
                section,
                name: f.get(6).unwrap_or(&"").to_string(),
            },
        );
    }
    out
}

/// One row of `readelf -r`, with the section the entries apply to.
struct OracleRel {
    /// The section the relocations patch, as readelf names the table.
    applies_to: String,
    offset: u64,
    kind: u64,
    symbol: u64,
    type_name: String,
}

fn oracle_relocations(fixture: &str) -> Vec<OracleRel> {
    let mut out = Vec::new();
    let Some(txt) = tool("readelf", fixture, &["-rW"]) else {
        return out;
    };
    let mut applies_to = String::new();
    for line in txt.lines() {
        if let Some(rest) = line.strip_prefix("Relocation section '") {
            // "Relocation section '.rel.text' at offset 0x664 contains 6 ..."
            let table = rest.split('\'').next().unwrap_or("");
            applies_to = table
                .trim_start_matches(".rel")
                .trim_start_matches('a')
                .to_string();
            continue;
        }
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() < 3 || !f[1].chars().all(|c| c.is_ascii_hexdigit()) {
            continue;
        }
        let (Ok(offset), Ok(info)) = (u64::from_str_radix(f[0], 16), u64::from_str_radix(f[1], 16))
        else {
            continue;
        };
        if !f[2].starts_with("R_386_") {
            continue;
        }
        out.push(OracleRel {
            applies_to: applies_to.clone(),
            offset,
            kind: info & 0xff,
            symbol: info >> 8,
            type_name: f[2].to_string(),
        });
    }
    out
}

/// Where the loader put the section readelf refers to by index.
fn base_of_index(obj: &Object, index: usize) -> Option<u64> {
    obj.sections
        .get(index)
        .filter(|s| !s.range.is_empty())
        .map(|s| s.range.start().get())
}

fn read_u32(obj: &Object, at: u64) -> Option<u32> {
    let b = obj.memory.slice(Addr(at), 4)?;
    Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

/// The addend the assembler encoded, read out of the file rather than out of
/// the relocated image.
fn file_addend(obj: &Object, data: &[u8], section: &str, offset: u64) -> Option<i32> {
    let s = obj.section(section)?;
    let at = usize::try_from(s.file_offset + offset).ok()?;
    let b = data.get(at..at + 4)?;
    Some(i32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

#[test]
fn every_relocation_matches_readelf_entry_for_entry() {
    let Some(_) = corpus() else { return };
    let mut total = 0usize;
    for fixture in FIXTURES {
        let Some((obj, data)) = open(fixture) else {
            continue;
        };
        assert_eq!(obj.arch, Arch::X86, "{fixture}: not an i386 object");
        assert_eq!(obj.bits, Bits::Bits32);
        let syms = oracle_symbols(fixture);
        let rels = oracle_relocations(fixture);
        if syms.is_empty() || rels.is_empty() {
            // No readelf here; the gate is skipped rather than faked.
            return;
        }
        let got = obj
            .metadata
            .get("elf.got_base")
            .map(|v| u64::from_str_radix(v.trim_start_matches("0x"), 16).unwrap());

        let mut checked = 0usize;
        for rel in &rels {
            // Debug sections are relocated into a private copy for the DWARF
            // reader, not into the image, so there is nothing to read back.
            if rel.applies_to.starts_with(".debug") || rel.applies_to.is_empty() {
                continue;
            }
            let Some(sec) = obj.section(&rel.applies_to) else {
                continue;
            };
            if sec.range.is_empty() {
                continue;
            }
            let place = sec.range.start().get() + rel.offset;
            let addend =
                file_addend(&obj, &data, &rel.applies_to, rel.offset).unwrap_or_else(|| {
                    panic!(
                        "{fixture}: no bytes at {}+{:#x}",
                        rel.applies_to, rel.offset
                    )
                }) as i64 as u64;
            let sym = syms
                .get(&rel.symbol)
                .unwrap_or_else(|| panic!("{fixture}: readelf lists no symbol {}", rel.symbol));
            let defined = sym.section.and_then(|i| base_of_index(&obj, i));
            let s = defined.map(|b| b + sym.value);
            let actual = read_u32(&obj, place)
                .unwrap_or_else(|| panic!("{fixture}: {place:#x} is not mapped"));

            let want: u64 = match rel.kind {
                // R_386_32: S + A.
                1 => match s {
                    Some(s) => s.wrapping_add(addend),
                    // Undefined: the loader must leave what was there, not
                    // write a confident zero.
                    None => addend,
                },
                // R_386_PC32 and R_386_PLT32: S + A - P.
                2 | 4 => match s {
                    Some(s) => s.wrapping_add(addend).wrapping_sub(place),
                    None => addend,
                },
                // R_386_GOTOFF: S + A - GOT.
                9 => {
                    let got = got.expect("a GOTOFF relocation but no GOT base");
                    s.expect("GOTOFF against an undefined symbol")
                        .wrapping_add(addend)
                        .wrapping_sub(got)
                }
                // R_386_GOTPC: GOT + A - P.
                10 => got
                    .expect("a GOTPC relocation but no GOT base")
                    .wrapping_add(addend)
                    .wrapping_sub(place),
                // R_386_GOT32 and R_386_GOT32X write a slot offset, whose
                // value is checked through the slot below rather than here.
                3 | 43 => {
                    let got = got.expect("a GOT32 relocation but no GOT base");
                    let slot = got.wrapping_add(actual as u64).wrapping_sub(addend);
                    let held = read_u32(&obj, slot)
                        .unwrap_or_else(|| panic!("{fixture}: GOT slot {slot:#x} is not mapped"));
                    assert_eq!(
                        held as u64,
                        s.unwrap_or(0),
                        "{fixture}: {} at {:#x} names {}, whose GOT slot holds the wrong address",
                        rel.type_name,
                        rel.offset,
                        sym.name
                    );
                    checked += 1;
                    continue;
                }
                other => panic!("{fixture}: unexpected relocation type {other} in a fixture"),
            };
            assert_eq!(
                actual as u64, want as u32 as u64,
                "{fixture}: {} at {}+{:#x} against {} (place {place:#x}, addend {:#x})",
                rel.type_name, rel.applies_to, rel.offset, sym.name, addend as u32
            );
            checked += 1;
        }
        assert!(
            checked >= 5,
            "{fixture}: only {checked} relocations compared against readelf"
        );
        total += checked;
    }
    assert!(total >= 20, "only {total} relocations compared in total");
}

/// The implicit addend is the whole difference between `REL` and `RELA`, so it
/// gets its own assertion: the fixtures really do carry non-zero addends, and
/// ignoring them would change the answer.
#[test]
fn the_implicit_addend_is_not_zero_and_is_used() {
    let Some(_) = corpus() else { return };
    let Some((obj, data)) = open("relocs32.nopic.O2.o") else {
        return;
    };
    let rels = oracle_relocations("relocs32.nopic.O2.o");
    if rels.is_empty() {
        return;
    }
    let mut nonzero = 0;
    for rel in rels.iter().filter(|r| r.applies_to == ".text") {
        let a = file_addend(&obj, &data, ".text", rel.offset).unwrap();
        if a != 0 {
            nonzero += 1;
        }
    }
    assert!(
        nonzero > 0,
        "no relocation in .text carries an implicit addend; the fixture proves nothing"
    );
}

/// The call that stays inside the file must land on the function it names.
#[test]
fn an_intra_file_call_reaches_its_target() {
    let Some(_) = corpus() else { return };
    for fixture in FIXTURES {
        let Some((obj, _)) = open(fixture) else {
            continue;
        };
        let Some(leaf) = obj.symbols.iter().find(|s| s.name == "leaf") else {
            continue;
        };
        let Some(text) = obj.section(".text") else {
            continue;
        };
        // Find the `e8 rel32` whose target is `leaf`. Before relocations were
        // applied every one of these pointed at the byte after itself.
        let bytes = obj
            .memory
            .slice(text.range.start(), text.range.len())
            .expect(".text is not mapped");
        let mut hit = false;
        for (i, w) in bytes.windows(5).enumerate() {
            if w[0] != 0xe8 {
                continue;
            }
            let disp = i32::from_le_bytes([w[1], w[2], w[3], w[4]]) as i64;
            let target = text.range.start().get() as i64 + i as i64 + 5 + disp;
            if target as u64 == leaf.addr.get() {
                hit = true;
            }
        }
        assert!(
            hit,
            "{fixture}: no call reaches leaf at {:#x}",
            leaf.addr.get()
        );
    }
}

/// A call out of the file has no address here. It must stay as the compiler
/// left it rather than be relocated to point at address zero.
#[test]
fn an_external_call_is_left_alone_rather_than_pointed_at_zero() {
    let Some(_) = corpus() else { return };
    let Some((obj, data)) = open("relocs32.nopic.O2.o") else {
        return;
    };
    let syms = oracle_symbols("relocs32.nopic.O2.o");
    let rels = oracle_relocations("relocs32.nopic.O2.o");
    if syms.is_empty() || rels.is_empty() {
        return;
    }
    let mut checked = 0;
    for rel in rels.iter().filter(|r| r.applies_to == ".text") {
        let Some(sym) = syms.get(&rel.symbol) else {
            continue;
        };
        if sym.section.is_some() {
            continue;
        }
        let sec = obj.section(".text").unwrap();
        let place = sec.range.start().get() + rel.offset;
        let before = file_addend(&obj, &data, ".text", rel.offset).unwrap();
        assert_eq!(
            read_u32(&obj, place).unwrap() as i32,
            before,
            "{} against the undefined {} was patched anyway",
            rel.type_name,
            sym.name
        );
        checked += 1;
    }
    assert!(checked > 0, "the fixture has no undefined symbol to check");
    assert!(
        obj.metadata.contains_key("elf.relocations.unresolved"),
        "unresolved relocations were not reported"
    );
}

/// Nothing may be dropped without being counted.
#[test]
fn what_is_not_applied_is_reported_by_type() {
    let Some(_) = corpus() else { return };
    for fixture in FIXTURES {
        let Some((obj, _)) = open(fixture) else {
            continue;
        };
        let applied: u64 = obj
            .metadata
            .get("elf.relocations.applied")
            .expect("no applied count")
            .parse()
            .unwrap();
        assert!(applied > 0, "{fixture}: nothing was applied");
        // These fixtures use only implemented types, so the unhandled list
        // must be absent rather than merely small.
        assert!(
            !obj.metadata.contains_key("elf.relocations.unhandled"),
            "{fixture}: {:?}",
            obj.metadata.get("elf.relocations.unhandled")
        );
    }
}

/// Thread-local relocations are the ones deliberately left alone, and leaving
/// them alone has to be visible.
#[test]
fn tls_relocations_are_recorded_as_unhandled() {
    let obj = load(&synth::tls_object(), &LoadOptions::default()).expect("load");
    let listed = obj
        .metadata
        .get("elf.relocations.unhandled")
        .expect("a TLS relocation was dropped silently");
    // R_386_TLS_LE is 17, R_386_TLS_IE_32 is 33.
    assert!(listed.contains("type 17"), "{listed}");
    assert!(listed.contains("type 33"), "{listed}");
    assert!(
        obj.warnings.iter().any(|w| w.contains("not applied")),
        "{:?}",
        obj.warnings
    );
}

/// The debug sections are relocated into a private copy for the DWARF reader,
/// and they are `REL` tables too. Without them every function in the unit
/// resolves to the same address.
#[test]
fn debug_information_agrees_with_the_symbol_table() {
    let Some(_) = corpus() else { return };
    for fixture in FIXTURES {
        let Some((obj, _)) = open(fixture) else {
            continue;
        };
        let Some(debug) = &obj.debug else {
            panic!("{fixture}: no debug information was read at all");
        };
        let mut checked = 0;
        for f in debug.functions.values() {
            let Some(sym) = obj
                .symbols
                .iter()
                .find(|s| s.name == f.name && s.kind == e5r_format::SymbolKind::Function)
            else {
                continue;
            };
            assert_eq!(
                f.low_pc,
                sym.addr,
                "{fixture}: DWARF puts {} at {:#x}, the symbol table at {:#x}",
                f.name,
                f.low_pc.get(),
                sym.addr.get()
            );
            checked += 1;
        }
        assert!(checked >= 3, "{fixture}: only {checked} functions compared");
    }
}

// ---------------------------------------------------------------------------
// The PLT, in both of its i386 shapes.
//
// There is no i386 linker on this machine, so the dynamic images are built
// here: a header, one PT_LOAD, a `.dynsym`/`.dynstr` pair, a `.rel.plt` of
// R_386_JMP_SLOT entries, a `.got.plt`, and a `.plt` whose entries jump
// through those slots. Synthesising them is also the only way to get the two
// forms side by side from one toolchain.
// ---------------------------------------------------------------------------

#[test]
fn a_position_dependent_plt_resolves_to_names() {
    let obj = load(&synth::dynamic_plt(false), &LoadOptions::default()).expect("load");
    let names: Vec<&str> = obj
        .function_hints
        .iter()
        .filter_map(|h| h.name.as_deref())
        .filter(|n| n.ends_with("@plt"))
        .collect();
    assert_eq!(names, ["puts@plt", "strlen@plt"], "{:?}", obj.warnings);
    assert_eq!(
        obj.metadata.get("elf.plt.form").map(String::as_str),
        Some("decoded"),
        "the absolute form went through the index-order fallback"
    );
    for imp in &obj.imports {
        assert!(imp.thunk.is_some(), "{} has no thunk", imp.name);
    }
}

#[test]
fn a_position_independent_plt_resolves_to_names() {
    let obj = load(&synth::dynamic_plt(true), &LoadOptions::default()).expect("load");
    let names: Vec<&str> = obj
        .function_hints
        .iter()
        .filter_map(|h| h.name.as_deref())
        .filter(|n| n.ends_with("@plt"))
        .collect();
    assert_eq!(names, ["puts@plt", "strlen@plt"], "{:?}", obj.warnings);
    assert_eq!(
        obj.metadata.get("elf.plt.form").map(String::as_str),
        Some("decoded")
    );
}

/// The reason to decode rather than count: an entry no relocation names shifts
/// every later slot, and the index-order rule then labels the wrong bytes.
#[test]
fn an_unnamed_plt_entry_does_not_shift_the_names() {
    let obj = load(&synth::plt_with_ifunc_gap(), &LoadOptions::default()).expect("load");
    let plt = obj.section(".plt").expect(".plt").range.start().get();
    let named: Vec<(u64, &str)> = obj
        .function_hints
        .iter()
        .filter_map(|h| Some((h.addr.get(), h.name.as_deref()?)))
        .filter(|(_, n)| n.ends_with("@plt"))
        .collect();
    // Entry 0 is the resolver, entry 1 is the unnamed IFUNC, so the two named
    // entries are 2 and 3. Counting would have put them at 1 and 2.
    assert_eq!(
        named,
        [(plt + 0x20, "puts@plt"), (plt + 0x30, "strlen@plt")],
        "{:?}",
        obj.warnings
    );
}

// ---------------------------------------------------------------------------
// Hostile input.
// ---------------------------------------------------------------------------

/// Truncations and targeted corruptions of the relocation tables, in the style
/// of `fuzz.rs`: a loader given any bytes returns a value or an error, and
/// never panics, hangs or allocates without bound.
#[test]
fn corrupted_relocation_tables_neither_panic_nor_hang() {
    let Some(_) = corpus() else { return };
    let mut seeds: Vec<Vec<u8>> = Vec::new();
    for fixture in FIXTURES {
        if let Some(p) = corpus().map(|d| d.join(fixture)) {
            if let Ok(d) = std::fs::read(p) {
                seeds.push(d);
            }
        }
    }
    seeds.push(synth::dynamic_plt(true));
    seeds.push(synth::tls_object());
    if seeds.is_empty() {
        return;
    }

    // The budget stops the sweep; the hang is caught per file.
    //
    // How long the whole sweep takes is a fact about the build profile and the
    // machine -- it is 3s optimized here and ten times that unoptimized on a
    // shared runner, with nothing hanging in either -- so the sweep spends a
    // budget and stops, and what is asserted is the worst single load. One
    // small file taking seconds to refuse is a hang whatever built it.
    const BUDGET: Duration = Duration::from_secs(20);
    const ONE_FILE: Duration = Duration::from_secs(10);

    let started = Instant::now();
    let mut worst = Duration::ZERO;
    let mut slowest = String::new();
    let mut tried = 0u64;
    let mut time = |what: String, f: &mut dyn FnMut()| {
        let at = Instant::now();
        f();
        let took = at.elapsed();
        tried += 1;
        if took > worst {
            worst = took;
            slowest = what;
        }
    };
    'sweep: for (n, seed) in seeds.iter().enumerate() {
        // Every truncation, at a stride that still lands inside every table.
        for cut in (0..seed.len()).step_by(7) {
            time(format!("seed {n} truncated to {cut}"), &mut || {
                let _ = load(&seed[..cut], &LoadOptions::default());
            });
            if started.elapsed() > BUDGET {
                break 'sweep;
            }
        }
        // Every byte of every section header, saturated. That is how a
        // relocation count becomes 7x10^17: `sh_size` is a number from the
        // file and nothing else bounds the walk.
        for i in 0..seed.len() {
            let mut v = seed.clone();
            for b in v[i..(i + 8).min(seed.len())].iter_mut() {
                *b = 0xff;
            }
            time(format!("seed {n} saturated at {i}"), &mut || {
                let _ = load(&v, &LoadOptions::default());
            });
            if started.elapsed() > BUDGET {
                break 'sweep;
            }
        }
    }
    // Not a silent pass: a sweep that tried almost nothing proves nothing.
    assert!(tried > 100, "the sweep only loaded {tried} files");
    assert!(
        worst < ONE_FILE,
        "{slowest} took {worst:?} to load, which is a hang, not slowness \
         ({tried} files in {:?})",
        started.elapsed()
    );
}

/// The specific shape that cost 87 seconds once: a declared count that no file
/// could hold. It must warn and clamp, not allocate and not error.
#[test]
fn an_enormous_declared_relocation_count_is_clamped_and_reported() {
    let mut data = synth::tls_object();
    // Section header 2 is `.rel.text`; sh_size is its sixth word.
    let shoff = u32::from_le_bytes([data[32], data[33], data[34], data[35]]) as usize;
    let off = shoff + 2 * 40;
    data[off + 20..off + 24].copy_from_slice(&0xffff_fff0u32.to_le_bytes());
    let started = Instant::now();
    let obj = load(&data, &LoadOptions::default()).expect("a silly size must not fail the load");
    assert!(
        started.elapsed() < Duration::from_secs(2),
        "took {:?}",
        started.elapsed()
    );
    assert!(
        obj.warnings.iter().any(|w| w.contains("declares")),
        "the clamp was silent: {:?}",
        obj.warnings
    );
}

// ---------------------------------------------------------------------------
// Synthesised ELF32 images.
// ---------------------------------------------------------------------------

mod synth {
    const EHDR: usize = 52;
    const SHDR: usize = 40;
    const PHDR: usize = 32;

    struct Sec {
        name: &'static str,
        kind: u32,
        flags: u32,
        addr: u32,
        offset: u32,
        size: u32,
        link: u32,
        info: u32,
        entsize: u32,
    }

    fn put(v: &mut Vec<u8>, b: &[u8]) {
        v.extend_from_slice(b);
    }

    fn build(
        e_type: u16,
        entry: u32,
        secs: &[Sec],
        shstrtab: &[u8],
        body: &[u8],
        body_offset: u32,
        load: Option<(u32, u32, u32)>,
    ) -> Vec<u8> {
        let phnum = load.iter().len() as u16;
        let shoff = body_offset as usize + body.len();
        let mut v: Vec<u8> = Vec::new();
        put(&mut v, &[0x7f, b'E', b'L', b'F', 1, 1, 1, 0]);
        put(&mut v, &[0u8; 8]);
        put(&mut v, &e_type.to_le_bytes());
        put(&mut v, &3u16.to_le_bytes()); // EM_386
        put(&mut v, &1u32.to_le_bytes());
        put(&mut v, &entry.to_le_bytes());
        put(
            &mut v,
            &(if phnum > 0 { EHDR as u32 } else { 0 }).to_le_bytes(),
        );
        put(&mut v, &(shoff as u32).to_le_bytes());
        put(&mut v, &0u32.to_le_bytes()); // e_flags
        put(&mut v, &(EHDR as u16).to_le_bytes());
        put(&mut v, &(PHDR as u16).to_le_bytes());
        put(&mut v, &phnum.to_le_bytes());
        put(&mut v, &(SHDR as u16).to_le_bytes());
        // One null header, one per section, one for the string table itself.
        put(&mut v, &(secs.len() as u16 + 2).to_le_bytes());
        put(&mut v, &(secs.len() as u16 + 1).to_le_bytes()); // shstrndx
        assert_eq!(v.len(), EHDR);

        if let Some((vaddr, offset, size)) = load {
            put(&mut v, &1u32.to_le_bytes()); // PT_LOAD
            put(&mut v, &offset.to_le_bytes());
            put(&mut v, &vaddr.to_le_bytes());
            put(&mut v, &vaddr.to_le_bytes());
            put(&mut v, &size.to_le_bytes());
            put(&mut v, &size.to_le_bytes());
            put(&mut v, &7u32.to_le_bytes()); // p_flags last on ELF32
            put(&mut v, &0x1000u32.to_le_bytes());
            assert_eq!(v.len(), EHDR + PHDR);
        }
        v.resize(body_offset as usize, 0);
        put(&mut v, body);

        // Section header 0, then one per section, then the string table's own.
        put(&mut v, &[0u8; SHDR]);
        let mut name_off = 1u32;
        for s in secs {
            put(&mut v, &name_off.to_le_bytes());
            put(&mut v, &s.kind.to_le_bytes());
            put(&mut v, &s.flags.to_le_bytes());
            put(&mut v, &s.addr.to_le_bytes());
            put(&mut v, &s.offset.to_le_bytes());
            put(&mut v, &s.size.to_le_bytes());
            put(&mut v, &s.link.to_le_bytes());
            put(&mut v, &s.info.to_le_bytes());
            put(&mut v, &4u32.to_le_bytes());
            put(&mut v, &s.entsize.to_le_bytes());
            name_off += s.name.len() as u32 + 1;
        }
        // The string table sits after the headers.
        let strtab_off = v.len() + SHDR;
        put(&mut v, &name_off.to_le_bytes());
        put(&mut v, &3u32.to_le_bytes()); // SHT_STRTAB
        put(&mut v, &0u32.to_le_bytes());
        put(&mut v, &0u32.to_le_bytes());
        put(&mut v, &(strtab_off as u32).to_le_bytes());
        put(&mut v, &(shstrtab.len() as u32).to_le_bytes());
        put(&mut v, &0u32.to_le_bytes());
        put(&mut v, &0u32.to_le_bytes());
        put(&mut v, &1u32.to_le_bytes());
        put(&mut v, &0u32.to_le_bytes());
        put(&mut v, shstrtab);
        v
    }

    fn names(secs: &[Sec]) -> Vec<u8> {
        let mut t = vec![0u8];
        for s in secs {
            t.extend_from_slice(s.name.as_bytes());
            t.push(0);
        }
        t.push(0);
        t
    }

    /// A `.dynsym`/`.dynstr` pair naming `puts` and `strlen` as undefined.
    fn dynsym(strtab: &mut Vec<u8>) -> Vec<u8> {
        let mut syms = vec![0u8; 16];
        for name in ["puts", "strlen"] {
            let off = strtab.len() as u32;
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
            syms.extend_from_slice(&off.to_le_bytes());
            syms.extend_from_slice(&0u32.to_le_bytes()); // st_value
            syms.extend_from_slice(&0u32.to_le_bytes()); // st_size
            syms.push(0x12); // GLOBAL FUNC
            syms.push(0);
            syms.extend_from_slice(&0u16.to_le_bytes()); // SHN_UNDEF
        }
        syms
    }

    /// One i386 PLT entry: the indirect jump, the relocation index push and
    /// the branch back to the resolver, padded to sixteen bytes.
    fn plt_entry(pic: bool, operand: u32, index: u32) -> Vec<u8> {
        let mut e = Vec::new();
        e.extend_from_slice(if pic { &[0xff, 0xa3] } else { &[0xff, 0x25] });
        e.extend_from_slice(&operand.to_le_bytes());
        e.push(0x68); // push imm32
        e.extend_from_slice(&index.to_le_bytes());
        e.push(0xe9); // jmp rel32
        e.extend_from_slice(&0u32.to_le_bytes());
        e.resize(16, 0x90);
        e
    }

    /// A dynamic executable with a two-entry PLT, in whichever form.
    pub fn dynamic_plt(pic: bool) -> Vec<u8> {
        image(pic, false)
    }

    /// The same, with an extra entry that no relocation names sitting in front
    /// of the two that do.
    pub fn plt_with_ifunc_gap() -> Vec<u8> {
        image(false, true)
    }

    fn image(pic: bool, gap: bool) -> Vec<u8> {
        const BASE: u32 = 0x0804_8000;
        let body_offset: u32 = 0x1000;

        let mut dynstr = vec![0u8];
        let dynsyms = dynsym(&mut dynstr);

        // Layout inside the loaded image, all in one PT_LOAD.
        let dynsym_addr = BASE + body_offset;
        let dynstr_addr = dynsym_addr + dynsyms.len() as u32;
        let relplt_addr = (dynstr_addr + dynstr.len() as u32).next_multiple_of(4);
        let relplt_len = 2 * 8;
        let gotplt_addr = relplt_addr + relplt_len;
        // Three reserved slots, then one per PLT entry.
        let slots = if gap { 4 } else { 2 };
        let gotplt_len = (3 + slots) * 4;
        let plt_addr = (gotplt_addr + gotplt_len).next_multiple_of(16);
        let entries = if gap { 4 } else { 3 };
        let plt_len = entries * 16;

        // `.rel.plt`: one R_386_JMP_SLOT per named entry, pointing at the
        // GOT slot that entry jumps through.
        let named_slot = |i: u32| gotplt_addr + (3 + if gap { i + 1 } else { i }) * 4;
        let mut relplt = Vec::new();
        for i in 0..2u32 {
            relplt.extend_from_slice(&named_slot(i).to_le_bytes());
            // r_info: symbol index i+1, type 7 (R_386_JMP_SLOT).
            relplt.extend_from_slice(&(((i + 1) << 8) | 7).to_le_bytes());
        }

        let gotplt = vec![0u8; gotplt_len as usize];

        let mut plt = Vec::new();
        // Entry 0 is the resolver stub, which names no symbol.
        plt.extend_from_slice(&plt_entry(pic, 4, 0));
        if gap {
            // An IFUNC entry: a real jump through a slot no relocation names.
            let slot = gotplt_addr + 3 * 4;
            plt.extend_from_slice(&plt_entry(
                pic,
                if pic { slot - gotplt_addr } else { slot },
                0,
            ));
        }
        for i in 0..2u32 {
            let slot = named_slot(i);
            plt.extend_from_slice(&plt_entry(
                pic,
                if pic { slot - gotplt_addr } else { slot },
                i * 8,
            ));
        }
        assert_eq!(plt.len() as u32, plt_len);

        // `.dynamic`, for DT_PLTGOT: the GOT base the `%ebx` form measures
        // from. Without it the position-independent entries name nothing.
        let dynamic_addr = plt_addr + plt_len;
        let mut dynamic = Vec::new();
        dynamic.extend_from_slice(&3u32.to_le_bytes()); // DT_PLTGOT
        dynamic.extend_from_slice(&gotplt_addr.to_le_bytes());
        dynamic.extend_from_slice(&0u32.to_le_bytes()); // DT_NULL
        dynamic.extend_from_slice(&0u32.to_le_bytes());

        let end = dynamic_addr + dynamic.len() as u32;
        let mut body = vec![0u8; (end - dynsym_addr) as usize];
        let mut place = |addr: u32, bytes: &[u8]| {
            let at = (addr - dynsym_addr) as usize;
            body[at..at + bytes.len()].copy_from_slice(bytes);
        };
        place(dynsym_addr, &dynsyms);
        place(dynstr_addr, &dynstr);
        place(relplt_addr, &relplt);
        place(gotplt_addr, &gotplt);
        place(plt_addr, &plt);
        place(dynamic_addr, &dynamic);

        let off = |addr: u32| body_offset + (addr - dynsym_addr);
        let secs = vec![
            Sec {
                name: ".dynsym",
                kind: 11,
                flags: 2,
                addr: dynsym_addr,
                offset: off(dynsym_addr),
                size: dynsyms.len() as u32,
                link: 2,
                info: 1,
                entsize: 16,
            },
            Sec {
                name: ".dynstr",
                kind: 3,
                flags: 2,
                addr: dynstr_addr,
                offset: off(dynstr_addr),
                size: dynstr.len() as u32,
                link: 0,
                info: 0,
                entsize: 0,
            },
            Sec {
                name: ".rel.plt",
                kind: 9,
                flags: 2,
                addr: relplt_addr,
                offset: off(relplt_addr),
                size: relplt_len,
                link: 1,
                info: 4,
                entsize: 8,
            },
            Sec {
                name: ".got.plt",
                kind: 1,
                flags: 3,
                addr: gotplt_addr,
                offset: off(gotplt_addr),
                size: gotplt_len,
                link: 0,
                info: 0,
                entsize: 4,
            },
            Sec {
                name: ".plt",
                kind: 1,
                flags: 6,
                addr: plt_addr,
                offset: off(plt_addr),
                size: plt_len,
                link: 0,
                info: 0,
                entsize: 16,
            },
            Sec {
                name: ".dynamic",
                kind: 6,
                flags: 3,
                addr: dynamic_addr,
                offset: off(dynamic_addr),
                size: dynamic.len() as u32,
                link: 2,
                info: 0,
                entsize: 8,
            },
        ];
        // `.dynsym` links to section index 2, which is `.dynstr`.
        let shstr = names(&secs);
        build(
            2,
            plt_addr,
            &secs,
            &shstr,
            &body,
            body_offset,
            Some((dynsym_addr, body_offset, body.len() as u32)),
        )
    }

    /// A relocatable object whose `.rel.text` holds only thread-local
    /// relocations, which is what "recorded rather than applied" is about.
    pub fn tls_object() -> Vec<u8> {
        let body_offset: u32 = 0x100;
        // Two instructions' worth of bytes to patch, and a symbol table.
        let text = vec![0x90u8; 16];
        let mut strtab = vec![0u8];
        let mut symtab = vec![0u8; 16];
        for (name, shndx) in [("tls_a", 1u16), ("tls_b", 1u16)] {
            let off = strtab.len() as u32;
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
            symtab.extend_from_slice(&off.to_le_bytes());
            symtab.extend_from_slice(&0u32.to_le_bytes());
            symtab.extend_from_slice(&4u32.to_le_bytes());
            symtab.push(0x16); // GLOBAL TLS
            symtab.push(0);
            symtab.extend_from_slice(&shndx.to_le_bytes());
        }
        // R_386_TLS_LE (17) and R_386_TLS_IE_32 (33).
        let mut rel = Vec::new();
        rel.extend_from_slice(&0u32.to_le_bytes());
        rel.extend_from_slice(&((1u32 << 8) | 17).to_le_bytes());
        rel.extend_from_slice(&8u32.to_le_bytes());
        rel.extend_from_slice(&((2u32 << 8) | 33).to_le_bytes());

        let mut body = Vec::new();
        let text_off = body_offset;
        body.extend_from_slice(&text);
        let rel_off = text_off + body.len() as u32;
        body.extend_from_slice(&rel);
        let symtab_off = text_off + body.len() as u32;
        body.extend_from_slice(&symtab);
        let strtab_off = text_off + body.len() as u32;
        body.extend_from_slice(&strtab);

        let secs = vec![
            Sec {
                name: ".text",
                kind: 1,
                flags: 6,
                addr: 0,
                offset: text_off,
                size: text.len() as u32,
                link: 0,
                info: 0,
                entsize: 0,
            },
            Sec {
                name: ".rel.text",
                kind: 9,
                flags: 0,
                addr: 0,
                offset: rel_off,
                size: rel.len() as u32,
                link: 3,
                info: 1,
                entsize: 8,
            },
            Sec {
                name: ".symtab",
                kind: 2,
                flags: 0,
                addr: 0,
                offset: symtab_off,
                size: symtab.len() as u32,
                link: 4,
                info: 1,
                entsize: 16,
            },
            Sec {
                name: ".strtab",
                kind: 3,
                flags: 0,
                addr: 0,
                offset: strtab_off,
                size: strtab.len() as u32,
                link: 0,
                info: 0,
                entsize: 0,
            },
        ];
        let shstr = names(&secs);
        build(1, 0, &secs, &shstr, &body, body_offset, None)
    }
}

/// A section that claims more than the image holds must not become a loop.
///
/// Found by the sweep above, which named the file it choked on: eight bytes
/// saturated at 4488 of a 4,642-byte dynamic object lands in a section header,
/// and `.plt` then claimed a size the file could not hold. The PLT readers
/// divided that size by an entry width and walked a quarter of a billion
/// slots, every one of them outside the image -- 309ms optimized here, and the
/// eighteen seconds a dev build took on a runner.
///
/// Pinned by name rather than left to the sweep, which spends a budget and may
/// stop before reaching this input again. The bound is loose on purpose: the
/// gap between a bounded read and an unbounded one here is four orders of
/// magnitude, so nothing turns on where inside that gap the line sits.
#[test]
fn a_section_larger_than_the_image_is_not_a_loop() {
    let mut v = synth::dynamic_plt(true);
    let end = (4488 + 8).min(v.len());
    assert!(
        end > 4488,
        "the synthetic object is too short to corrupt there"
    );
    for b in v[4488..end].iter_mut() {
        *b = 0xff;
    }
    let started = Instant::now();
    let _ = load(&v, &LoadOptions::default());
    let took = started.elapsed();
    assert!(
        took < Duration::from_secs(2),
        "loading {} bytes took {took:?}: a size from the file became a walk",
        v.len()
    );
}
