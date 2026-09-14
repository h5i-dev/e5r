//! Which instruction set an ARM image holds, which the bytes never say.
//!
//! A32 and T32 share one `e_machine`, so a loader that does not decide reads
//! every Thumb image as A32 and produces plausible nonsense from the first
//! halfword on. Two things decide it, and both are checked here against real
//! images: the low bit of a code address, which is what `bx` reads to switch,
//! and the CPU profile an `.ARM.attributes` section declares.

use std::path::{Path, PathBuf};

use r12e_core::Arch;
use r12e_format::LoadOptions;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn load(name: &str) -> Option<r12e_format::Object> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    r12e_format::load(&data, &LoadOptions::default()).ok()
}

/// A Thumb object's function symbols carry the Thumb bit, and that is what
/// says the image is Thumb.
#[test]
fn a_thumb_object_is_read_as_thumb() {
    for name in [
        "shapes.thumb.O0.o",
        "shapes.thumb.O1.o",
        "shapes.thumb.O2.o",
    ] {
        let Some(obj) = load(name) else {
            continue; // the corpus has not been built
        };
        assert_eq!(obj.arch, Arch::Thumb, "{name}");
        assert_eq!(
            obj.metadata.get("arm.mode").map(String::as_str),
            Some("thumb")
        );
    }
}

/// And an A32 object is not, which is the half that would pass by accident if
/// the answer were always Thumb.
#[test]
fn an_a32_object_is_read_as_a32() {
    for name in ["shapes.arm.O0.o", "shapes.arm.O1.o", "shapes.arm.O2.o"] {
        let Some(obj) = load(name) else {
            continue;
        };
        assert_eq!(obj.arch, Arch::Arm, "{name}");
        assert_eq!(
            obj.metadata.get("arm.mode").map(String::as_str),
            Some("a32")
        );
    }
}

/// The Thumb bit is not part of the address.
///
/// Leaving it on puts every function one byte past where it starts, and the
/// decode then runs from the wrong offset for the rest of the file.
#[test]
fn the_thumb_bit_is_not_part_of_a_symbol_address() {
    let Some(obj) = load("shapes.thumb.O1.o") else {
        return;
    };
    let functions: Vec<_> = obj
        .symbols
        .iter()
        .filter(|s| s.kind == r12e_format::SymbolKind::Function)
        .collect();
    assert!(!functions.is_empty(), "the fixture names no functions");
    for s in functions {
        assert_eq!(
            s.addr.get() & 1,
            0,
            "{} is at {:#x}, which is not an address",
            s.name,
            s.addr.get()
        );
    }
}
