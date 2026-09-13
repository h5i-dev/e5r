//! Virtual table recovery, measured against the symbols that name them.
//!
//! A C++ compiler emits a `_ZTV` symbol for every class with virtual
//! functions, so the fixture's own symbol table says which tables exist and
//! what they are called. The scan is then run over the same binary with those
//! symbols ignored, and has to find the same tables in the same places: that
//! is the case that matters, because a stripped binary is where a scan is the
//! only thing there is.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::Addr;
use r12e_format::LoadOptions;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// The same program with every vtable symbol taken away.
fn without_symbols(mut p: Program) -> Program {
    p.object.symbols.retain(|s| !s.name.starts_with("_ZTV"));
    p
}

#[test]
fn every_named_table_is_found_and_named() {
    for fixture in [
        "shapes.a64.O0.cpp.o",
        "shapes.a64.O2.cpp.o",
        "shapes.a64.O0.cpp",
        "shapes.a64.O2.cpp",
    ] {
        let Some(p) = open(fixture) else { continue };
        let expected: BTreeMap<u64, String> = p
            .object
            .symbols
            .iter()
            .filter(|s| s.name.starts_with("_ZTV") && s.addr != Addr::ZERO)
            .map(|s| (s.addr.get(), s.name.clone()))
            .collect();
        assert!(!expected.is_empty(), "{fixture}: no vtable symbols at all");

        let found = r12e_api::vtables(&p);
        for (addr, symbol) in &expected {
            let table = found
                .iter()
                .find(|t| t.addr.get() == *addr)
                .unwrap_or_else(|| panic!("{fixture}: no table at {addr:#x} for {symbol}"));
            let class = table
                .class
                .as_deref()
                .unwrap_or_else(|| panic!("{fixture}: the table at {addr:#x} has no class"));
            // `_ZTV4Cube` is the table for `Cube`.
            assert!(
                symbol.contains(class),
                "{fixture}: {symbol} came out as {class:?}"
            );
            assert!(
                !table.methods.is_empty(),
                "{fixture}: {class} has no methods"
            );
        }
    }
}

#[test]
fn the_scan_finds_the_same_tables_without_the_symbols() {
    // The linked binaries: in an object file a pure virtual slot has no value
    // yet, so a scan with nothing to go on cannot know the table continues
    // past it. Once linked, every slot points at something.
    for fixture in ["shapes.a64.O0.cpp", "shapes.a64.O2.cpp"] {
        let Some(p) = open(fixture) else { continue };
        // Only the tables whose first slot holds a real function. An abstract
        // class whose destructor was never emitted has an empty slot there,
        // and a scan with nothing to go on cannot tell that from data: the
        // symbol is the only thing that says a table starts here.
        let named: BTreeMap<u64, usize> = r12e_api::vtables(&p)
            .into_iter()
            .filter(|t| t.class.is_some() && t.methods.first() != Some(&Addr::ZERO))
            .map(|t| (t.addr.get(), t.methods.len()))
            .collect();
        assert!(!named.is_empty(), "{fixture}: nothing to compare against");

        let scanned: BTreeMap<u64, usize> = r12e_api::vtables(&without_symbols(p))
            .into_iter()
            .map(|t| (t.addr.get(), t.methods.len()))
            .collect();

        for (addr, methods) in &named {
            let found = scanned.get(addr).unwrap_or_else(|| {
                panic!("{fixture}: the scan missed the table at {addr:#x}")
            });
            assert_eq!(
                found, methods,
                "{fixture}: the table at {addr:#x} came out with {found} methods, not {methods}"
            );
        }
    }
}

#[test]
fn every_slot_points_at_something_executable() {
    for fixture in [
        "shapes.a64.O0.cpp.o",
        "shapes.a64.O2.cpp.o",
        "shapes.a64.O0.cpp",
        "shapes.a64.O2.cpp",
    ] {
        let Some(p) = open(fixture) else { continue };
        for table in r12e_api::vtables(&p) {
            for (slot, method) in table.methods.iter().enumerate() {
                // A slot can be empty: a pure virtual function in an object
                // file has no address until it is linked.
                if *method == Addr::ZERO {
                    continue;
                }
                let executable = p
                    .object
                    .sections
                    .iter()
                    .any(|s| s.exec && s.range.contains(*method));
                assert!(
                    executable,
                    "{fixture}: slot {slot} of the table at {} points at {method}, \
                     which is not code",
                    table.addr
                );
            }
        }
    }
}

#[test]
fn a_binary_with_no_classes_has_no_tables() {
    let Some(p) = open("wide.a64.O2.o") else { return };
    let found = r12e_api::vtables(&p);
    assert!(
        found.is_empty(),
        "found {} tables in a C program: {:?}",
        found.len(),
        found.iter().map(|t| t.addr).collect::<Vec<_>>()
    );
}

/// Virtual dispatch, run in the interpreter and compared against the processor.
///
/// The fixture writes its own answer when it runs, so the expected value came
/// out of hardware. Getting it right means the indirect calls through the
/// vtables went where the machine sent them.
#[test]
fn virtual_dispatch_interprets_to_the_same_answer() {
    for fixture in ["shapes.a64.O0.cpp", "shapes.a64.O2.cpp"] {
        let Some(dir) = corpus() else { return };
        let Ok(recorded) = std::fs::read(dir.join(format!("{fixture}.out"))) else {
            continue;
        };
        let Some(expected) = recorded
            .get(..8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
        else {
            continue;
        };
        let Some(p) = open(fixture) else { continue };
        let Some(f) = p
            .functions_by_address()
            .find(|f| f.name.as_deref() == Some("run_shapes"))
        else {
            continue;
        };
        let setup = r12e_api::Setup {
            depth: 256,
            ..Default::default()
        };
        let run = r12e_api::emulate::run(&p, f, &setup);
        assert_eq!(
            run.stop,
            r12e_ir::Stop::Returned,
            "{fixture}: the run stopped with {:?}",
            run.stop
        );
        assert_eq!(
            run.result, expected,
            "{fixture}: interpreted {:#x}, the processor produced {expected:#x}",
            run.result
        );
    }
}
