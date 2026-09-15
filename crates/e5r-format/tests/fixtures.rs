//! Loader tests against the built fixture corpus, with readelf as the oracle.
//!
//! Skipped when the corpus is absent so a fresh checkout still passes; run
//! `scripts/build-fixtures.sh` to enable them.

use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_core::{Addr, Arch, Bits, Evidence, Strength};
use e5r_format::{LoadOptions, Object, SymbolKind, load};

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

/// Ask readelf, so the expectations are not our own parser's opinion.
fn readelf(name: &str, args: &[&str]) -> Option<String> {
    let p = corpus()?.join(name);
    let out = Command::new("readelf").args(args).arg(&p).output().ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

#[test]
fn aarch64_executable_loads() {
    let Some((obj, _)) = open("hello.a64.O0") else {
        return;
    };
    assert_eq!(obj.arch, Arch::AArch64);
    assert_eq!(obj.bits, Bits::Bits64);
    assert!(obj.entry.is_some());
    assert!(!obj.memory.is_empty());
    assert!(obj.section(".text").is_some(), "no .text");
    assert!(obj.memory.is_executable(obj.entry.unwrap()));
}

#[test]
fn entry_point_matches_readelf() {
    let Some((obj, _)) = open("hello.a64.O0") else {
        return;
    };
    let Some(txt) = readelf("hello.a64.O0", &["-h"]) else {
        return;
    };
    let want = txt
        .lines()
        .find(|l| l.contains("Entry point address"))
        .and_then(|l| l.split("0x").nth(1))
        .and_then(|h| u64::from_str_radix(h.trim(), 16).ok())
        .expect("readelf printed no entry point");
    assert_eq!(obj.entry, Some(Addr(want)));
}

#[test]
fn section_addresses_match_readelf() {
    let Some((obj, _)) = open("hello.a64.O0") else {
        return;
    };
    let Some(txt) = readelf("hello.a64.O0", &["-S", "-W"]) else {
        return;
    };
    let mut checked = 0;
    for line in txt.lines() {
        // "  [ 14] .text             PROGBITS        0000000000000640 000640 000174 00  AX  0   0 64"
        let Some(rest) = line.split(']').nth(1) else {
            continue;
        };
        let f: Vec<&str> = rest.split_whitespace().collect();
        if f.len() < 4 || !f[0].starts_with('.') {
            continue;
        }
        let Ok(addr) = u64::from_str_radix(f[2], 16) else {
            continue;
        };
        if addr == 0 {
            continue;
        }
        let ours = obj
            .section(f[0])
            .unwrap_or_else(|| panic!("missing {}", f[0]));
        assert_eq!(ours.range.start(), Addr(addr), "{}", f[0]);
        checked += 1;
    }
    assert!(checked > 5, "only checked {checked} sections");
}

#[test]
fn every_readelf_function_symbol_is_found() {
    let Some((obj, _)) = open("hello.a64.O0") else {
        return;
    };
    let Some(txt) = readelf("hello.a64.O0", &["-sW"]) else {
        return;
    };
    let mut want = 0;
    let mut found = 0;
    for line in txt.lines() {
        let f: Vec<&str> = line.split_whitespace().collect();
        // "  57: 0000000000000754   112 FUNC    GLOBAL DEFAULT   14 main"
        if f.len() < 8 || f[3] != "FUNC" || f[6] == "UND" {
            continue;
        }
        let Ok(addr) = u64::from_str_radix(f[1], 16) else {
            continue;
        };
        if addr == 0 {
            continue;
        }
        want += 1;
        let name = f[7].split('@').next().unwrap();
        if obj
            .symbols
            .iter()
            .any(|s| s.name == name && s.addr == Addr(addr) && s.kind == SymbolKind::Function)
        {
            found += 1;
        }
    }
    assert!(want > 0, "readelf listed no defined functions");
    assert_eq!(
        found,
        want,
        "missed {} of {want} function symbols",
        want - found
    );
}

#[test]
fn eh_frame_agrees_with_the_symbol_table() {
    // Both are proven evidence for the same functions, so on a binary with
    // both, .eh_frame should not be inventing entries the symbols deny.
    let Some((obj, _)) = open("hello.a64.O0") else {
        return;
    };
    let eh: Vec<Addr> = obj
        .function_hints
        .iter()
        .filter(|h| {
            h.provenance.best == Evidence::EhFrame
                || h.provenance.corroborating.contains(&Evidence::EhFrame)
        })
        .map(|h| h.addr)
        .collect();
    assert!(!eh.is_empty(), "no .eh_frame hints at all");
    for a in &eh {
        assert!(obj.memory.is_executable(*a), "{a} is not executable");
    }
    // The symbol table's functions should nearly all be corroborated by an FDE.
    let syms: Vec<Addr> = obj
        .symbols
        .iter()
        .filter(|s| s.is_defined_function() && !s.dynamic)
        .map(|s| s.addr)
        .collect();
    let overlap = syms.iter().filter(|a| eh.contains(a)).count();
    assert!(
        overlap * 2 >= syms.len(),
        "only {overlap} of {} symbol functions have an FDE",
        syms.len()
    );
}

#[test]
fn hints_are_sorted_by_evidence_strength() {
    let Some((obj, _)) = open("hello.a64.O0") else {
        return;
    };
    let mut last = Strength::Asserted;
    for h in &obj.function_hints {
        assert!(h.provenance.strength() <= last, "hints are out of order");
        last = h.provenance.strength();
    }
}

#[test]
fn relocatable_objects_get_synthetic_addresses() {
    let Some((obj, _)) = open("shapes.a64.O2.o") else {
        return;
    };
    assert_eq!(obj.arch, Arch::AArch64);
    // Every section sits at zero in the file; the loader must lay them out.
    let text = obj.section(".text").expect("no .text");
    assert!(text.range.start() != Addr::ZERO, "text was not relocated");
    assert!(!text.range.is_empty());
    // Function symbols must follow their section.
    for want in ["sum_to", "branchy", "dense_switch", "recursive"] {
        let s = obj
            .symbols
            .iter()
            .find(|s| s.name == want)
            .unwrap_or_else(|| panic!("no symbol {want}"));
        assert!(
            obj.memory.is_executable(s.addr),
            "{want} at {} is not in executable memory",
            s.addr
        );
    }
}

#[test]
fn x86_64_objects_load_on_an_aarch64_host() {
    let Some((obj, _)) = open("shapes.x64.O2.o") else {
        return;
    };
    assert_eq!(obj.arch, Arch::X86_64);
    assert_eq!(obj.bits, Bits::Bits64);
    assert!(obj.symbols.iter().any(|s| s.name == "dense_switch"));
}

#[test]
fn stripped_binaries_still_yield_functions() {
    let Some((stripped, _)) = open("hello.a64.O2.stripped") else {
        return;
    };
    let Some((full, _)) = open("hello.a64.O2") else {
        return;
    };
    assert!(
        stripped.symbols.len() < full.symbols.len(),
        "stripping removed nothing"
    );
    // .eh_frame survives stripping, which is the point of preferring it.
    assert!(
        !stripped.function_hints.is_empty(),
        "no function hints left after stripping"
    );
}

#[test]
fn loading_is_deterministic() {
    let Some((a, data)) = open("hello.a64.O0") else {
        return;
    };
    let b = load(&data, &LoadOptions::default()).unwrap();
    assert_eq!(a.symbols, b.symbols);
    assert_eq!(
        a.function_hints.iter().map(|h| h.addr).collect::<Vec<_>>(),
        b.function_hints.iter().map(|h| h.addr).collect::<Vec<_>>()
    );
    assert_eq!(a.metadata, b.metadata);
}

#[test]
fn truncation_at_every_length_never_panics() {
    let Some((_, data)) = open("hello.a64.O0") else {
        return;
    };
    // Every prefix of a real file is a plausible truncated download and a
    // plausible fuzz case.
    let mut n = 1;
    while n < data.len() {
        let _ = load(&data[..n], &LoadOptions::default());
        n = (n * 2).max(n + 97);
    }
}

#[test]
fn single_byte_corruption_never_panics() {
    let Some((_, data)) = open("hello.a64.O0") else {
        return;
    };
    let mut buf = data.clone();
    // Headers are where a hostile file does its damage, so hit them hardest.
    for i in (0..0x400.min(buf.len())).step_by(3) {
        let old = buf[i];
        for v in [0xff, 0x00, 0x80] {
            buf[i] = v;
            let _ = load(&buf, &LoadOptions::default());
        }
        buf[i] = old;
    }
}

#[test]
fn plt_thunks_are_named_where_objdump_names_them() {
    // objdump prints `<name@plt>` at each PLT entry, which is the oracle for
    // whether the layout arithmetic is right. An off-by-one here names every
    // indirect call after the wrong import.
    // Whatever this machine has: the oracle is objdump, not a recorded list,
    // so any dynamically linked system binary will do and the architecture
    // does not have to be this one.
    let mut compared_somewhere = false;
    for path in [
        "/bin/bash",
        "/usr/lib/aarch64-linux-gnu/libc.so.6",
        "/usr/lib/x86_64-linux-gnu/libc.so.6",
    ] {
        let p = Path::new(path);
        if !p.is_file() {
            continue;
        }
        let data = std::fs::read(p).unwrap();
        let Ok(obj) = load(&data, &LoadOptions::default()) else {
            continue;
        };
        // `.plt.sec` as well: with indirect-branch tracking on, that is where
        // the entry a call reaches lives, and it is the one objdump labels.
        let Ok(out) = Command::new("objdump")
            .args(["-d", "--section=.plt", "--section=.plt.sec"])
            .arg(p)
            .output()
        else {
            continue;
        };
        let text = String::from_utf8_lossy(&out.stdout);
        let mut checked = 0;
        for line in text.lines() {
            // "0000000000032b80 <mbrtowc@plt>:"
            let Some((addr, rest)) = line.split_once(" <") else {
                continue;
            };
            let Some(name) = rest.strip_suffix(">:") else {
                continue;
            };
            if !name.ends_with("@plt") {
                continue;
            }
            // objdump synthesizes `*ABS*+0x...@plt` for an IFUNC entry whose
            // relocation names no symbol. That is its own invention, not a
            // name in the file, so there is nothing to match.
            if name.starts_with('*') {
                continue;
            }
            let Ok(addr) = u64::from_str_radix(addr.trim(), 16) else {
                continue;
            };
            let ours = obj
                .function_hints
                .iter()
                .find(|h| h.addr == Addr(addr) && h.name.as_deref() == Some(name));
            assert!(
                ours.is_some(),
                "{path}: objdump names {name} at {addr:#x}, we do not"
            );
            checked += 1;
        }
        // Not per path: a machine need not have all three, and one that names
        // none of them is a machine where this gate did not run, which is
        // worth failing over rather than passing quietly.
        if checked > 10 {
            compared_somewhere = true;
        }
    }
    assert!(
        compared_somewhere,
        "no system binary here offered a PLT objdump would name; this gate \
         compared nothing"
    );
}
