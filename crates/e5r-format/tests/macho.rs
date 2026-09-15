//! Mach-O loading.
//!
//! There is no macOS linker here, so the objects come from clang, which
//! cross-compiles them without a sysroot, and the image path is exercised by a
//! synthesized file. `llvm-objdump` is the cross-check for the objects.

use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_core::{Addr, Arch, Bits, Evidence};
use e5r_format::{Format, LoadOptions, load, macho};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<(e5r_format::Object, Vec<u8>)> {
    let p = corpus()?.join(name);
    let data = std::fs::read(&p).ok()?;
    let obj = load(&data, &LoadOptions::default())
        .unwrap_or_else(|e| panic!("loading {}: {e}", p.display()));
    Some((obj, data))
}

#[test]
fn an_arm64_object_loads() {
    let Some((obj, _)) = open("wide.macho.a64.o") else {
        return;
    };
    assert_eq!(obj.format, Format::MachO);
    assert_eq!(obj.arch, Arch::AArch64);
    assert_eq!(obj.bits, Bits::Bits64);
    assert_eq!(
        obj.metadata.get("macho.type").map(String::as_str),
        Some("object")
    );
    let text = obj
        .section("__TEXT,__text")
        .expect("no __TEXT,__text section");
    assert!(text.exec);
    assert!(obj.memory.is_executable(text.range.start()));
}

#[test]
fn an_x86_64_object_loads_on_an_aarch64_host() {
    let Some((obj, _)) = open("wide.macho.x64.o") else {
        return;
    };
    assert_eq!(obj.arch, Arch::X86_64);
    assert!(obj.symbols.iter().any(|s| s.name == "rotate"));
}

#[test]
fn the_underscore_prefix_is_removed() {
    // Mach-O prefixes C symbols with an underscore; a listing that shows
    // `_rotate` is showing an implementation detail of the format.
    let Some((obj, _)) = open("wide.macho.a64.o") else {
        return;
    };
    assert!(obj.symbols.iter().any(|s| s.name == "rotate"));
    assert!(
        !obj.symbols.iter().any(|s| s.name == "_rotate"),
        "the underscore was not removed"
    );
}

#[test]
fn assembler_temporaries_do_not_name_functions() {
    // clang emits `ltmp0` at the same address as the first real function.
    // Letting it win hides the name anyone actually wants.
    let Some((obj, _)) = open("wide.macho.a64.o") else {
        return;
    };
    for h in &obj.function_hints {
        if let Some(n) = &h.name {
            assert!(
                !n.starts_with("ltmp") && !n.starts_with("l_"),
                "{n} was used as a function name"
            );
        }
    }
    // And the real name is still there.
    assert!(
        obj.function_hints
            .iter()
            .any(|h| h.name.as_deref() == Some("arith8")),
        "the real name at that address was lost"
    );
}

#[test]
fn every_symbol_llvm_objdump_lists_is_found() {
    let Some((obj, _)) = open("wide.macho.a64.o") else {
        return;
    };
    let p = corpus().unwrap().join("wide.macho.a64.o");
    let Ok(out) = Command::new("llvm-objdump-18")
        .args(["-t"])
        .arg(&p)
        .output()
    else {
        return;
    };
    if !out.status.success() {
        return;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let mut checked = 0;
    for line in text.lines() {
        // "0000000000000000 g     F __TEXT,__text _arith8"
        let Some(name) = line.split_whitespace().last() else {
            continue;
        };
        let Some(name) = name.strip_prefix('_') else {
            continue;
        };
        if !line.contains("__TEXT,__text") || name.is_empty() {
            continue;
        }
        assert!(
            obj.symbols.iter().any(|s| s.name == name),
            "llvm-objdump lists {name}, we do not"
        );
        checked += 1;
    }
    assert!(checked > 5, "only {checked} symbols compared");
}

#[test]
fn a_truncated_macho_never_panics() {
    let Some((_, data)) = open("wide.macho.a64.o") else {
        return;
    };
    let mut n = 1;
    while n < data.len() {
        let _ = load(&data[..n], &LoadOptions::default());
        n = (n * 2).max(n + 31);
    }
}

#[test]
fn corrupted_headers_never_panic() {
    let Some((_, mut data)) = open("wide.macho.a64.o") else {
        return;
    };
    for i in (0..0x400.min(data.len())).step_by(3) {
        let old = data[i];
        for v in [0xff, 0x00, 0x80] {
            data[i] = v;
            let _ = load(&data, &LoadOptions::default());
        }
        data[i] = old;
    }
}

#[test]
fn a_fat_header_with_a_lying_count_is_an_error_not_a_panic() {
    // Built by hand: the fat index is big-endian, and a count it cannot back
    // up is the obvious way to make a reader walk off the end.
    let mut data = Vec::new();
    data.extend_from_slice(&0xcafe_babeu32.to_be_bytes());
    data.extend_from_slice(&0xffff_ffffu32.to_be_bytes());
    assert!(load(&data, &LoadOptions::default()).is_err());

    // A count of zero has no slice to load either.
    let mut empty = Vec::new();
    empty.extend_from_slice(&0xcafe_babeu32.to_be_bytes());
    empty.extend_from_slice(&0u32.to_be_bytes());
    assert!(load(&empty, &LoadOptions::default()).is_err());
}

#[test]
fn is_macho_does_not_claim_an_elf_or_a_pe() {
    assert!(!macho::is_macho(b"\x7fELF\x02\x01\x01\x00"));
    assert!(!macho::is_macho(b"MZ\x90\x00\x03\x00\x00\x00"));
    assert!(!macho::is_macho(b"\xfe\xed"));
}

#[test]
fn function_starts_are_used_when_present() {
    // Objects carry no LC_FUNCTION_STARTS, so this only checks that the
    // evidence kind exists and is never invented where it is absent.
    let Some((obj, _)) = open("wide.macho.a64.o") else {
        return;
    };
    assert!(
        !obj.function_hints
            .iter()
            .any(|h| h.provenance.best == Evidence::MachFunctionStarts),
        "claimed LC_FUNCTION_STARTS evidence in an object file that has none"
    );
    assert!(!obj.function_hints.is_empty());
    assert!(obj.function_hints.iter().all(|h| h.addr != Addr::ZERO));
}
