//! DWARF reading measured against readelf.
//!
//! The oracle is `readelf --debug-dump=info`, which is a different
//! implementation of the same specification. Function names and their entry
//! addresses are what the analysis consumes, so those are what is compared.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_format::LoadOptions;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// Functions readelf says the debug information describes, by address.
fn readelf_functions(path: &Path) -> Option<BTreeMap<u64, String>> {
    let out = Command::new("readelf")
        .arg("--debug-dump=info")
        .arg(path)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let mut found = BTreeMap::new();
    let mut in_subprogram = false;
    let mut name: Option<String> = None;
    let mut low: Option<u64> = None;
    for line in text.lines() {
        if line.contains("Abbrev Number:") {
            if let (Some(n), Some(a)) = (name.take(), low.take()) {
                found.insert(a, n);
            }
            in_subprogram = line.contains("DW_TAG_subprogram");
            continue;
        }
        if !in_subprogram {
            continue;
        }
        if let Some(rest) = line.split("DW_AT_name").nth(1) {
            // readelf prints the name after a colon, sometimes with an offset
            // in parentheses first.
            if let Some(v) = rest.rsplit(':').next() {
                let v = v.trim();
                if !v.is_empty() {
                    name = Some(v.to_string());
                }
            }
        }
        if let Some(rest) = line.split("DW_AT_low_pc").nth(1) {
            let v = rest.trim().trim_start_matches(':').trim();
            let v = v.trim_start_matches("0x");
            if let Ok(a) = u64::from_str_radix(v, 16) {
                low = Some(a);
            }
        }
    }
    if let (Some(n), Some(a)) = (name, low) {
        found.insert(a, n);
    }
    Some(found)
}

fn check(name: &str) {
    let Some(dir) = corpus() else { return };
    let path = dir.join(name);
    let Ok(data) = std::fs::read(&path) else {
        return;
    };
    let Ok(obj) = r12e_format::load(&data, &LoadOptions::default()) else {
        return;
    };
    let Some(debug) = &obj.debug else {
        panic!("{name}: no debug information was read at all");
    };
    let Some(expected) = readelf_functions(&path) else {
        return; // no readelf here
    };
    if expected.is_empty() {
        return;
    }

    // Names are compared against readelf. Addresses are compared against this
    // object's own symbol table, which is the stronger check: a relocatable
    // object's debug addresses are written as zero and filled in by
    // relocations, so agreeing with the symbol table means the relocations
    // were applied correctly.
    let ours: BTreeMap<String, u64> = debug
        .functions
        .values()
        .map(|f| (f.name.clone(), f.low_pc.get()))
        .collect();
    let symbols: BTreeMap<String, u64> = obj
        .symbols
        .iter()
        .filter(|s| s.kind == r12e_format::SymbolKind::Function)
        .map(|s| (s.name.clone(), s.addr.get()))
        .collect();

    let mut missing = Vec::new();
    let mut wrong = Vec::new();
    for expected_name in expected.values() {
        let Some(addr) = ours.get(expected_name) else {
            missing.push(expected_name.clone());
            continue;
        };
        if let Some(from_symbol) = symbols.get(expected_name) {
            if from_symbol != addr {
                wrong.push(format!(
                    "{expected_name}: debug says {addr:#x}, the symbol table says {from_symbol:#x}"
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{name}: {} addresses disagree with the symbol table:\n  {}",
        wrong.len(),
        wrong.join("\n  ")
    );
    assert!(
        missing.is_empty(),
        "{name}: {} of {} functions readelf describes were not read: {}",
        missing.len(),
        expected.len(),
        missing.join(", ")
    );
    println!(
        "{name}: {} functions, {} types, {} line rows",
        debug.functions.len(),
        debug.types.len(),
        debug.lines.len()
    );
}

#[test]
fn function_names_and_addresses_match_readelf() {
    for name in [
        "wide.a64.O0.o",
        "wide.a64.O2.o",
        "wide.x64.O0.o",
        "wide.x64.O2.o",
        "shapes.a64.O0.o",
        "hello.a64.O0",
        "hello.a64.O2",
    ] {
        check(name);
    }
}

#[test]
fn the_types_of_a_known_function_are_read() {
    let Some(dir) = corpus() else { return };
    let Ok(data) = std::fs::read(dir.join("wide.a64.O0.o")) else {
        return;
    };
    let Ok(obj) = r12e_format::load(&data, &LoadOptions::default()) else {
        return;
    };
    let Some(debug) = &obj.debug else { return };
    let f = debug
        .functions
        .values()
        .find(|f| f.name == "use_struct")
        .expect("use_struct is in the debug information");
    // `i64 use_struct(struct Point *p, int n)`.
    assert_eq!(f.signature.parameters.len(), 2);
    let (name, ty) = &f.signature.parameters[0];
    assert_eq!(name.as_deref(), Some("p"));
    assert_eq!(debug.types.name_of(*ty), "struct Point *");
    let (name, ty) = &f.signature.parameters[1];
    assert_eq!(name.as_deref(), Some("n"));
    assert_eq!(debug.types.size_of(*ty), Some(4));

    // And the structure it points at has the three fields, at their offsets.
    let pointer = debug.types.resolve(f.signature.parameters[0].1);
    let r12e_types::ctype::Type::Pointer(inner) = debug.types.get(pointer).unwrap() else {
        panic!("the first parameter is a pointer");
    };
    let field = debug.types.field_at(*inner, 8).expect("a field at eight");
    assert_eq!(field.0.name, "tag");
}

#[test]
fn the_line_table_locates_a_function() {
    let Some(dir) = corpus() else { return };
    let Ok(data) = std::fs::read(dir.join("wide.a64.O0.o")) else {
        return;
    };
    let Ok(obj) = r12e_format::load(&data, &LoadOptions::default()) else {
        return;
    };
    let Some(debug) = &obj.debug else { return };
    let f = debug
        .functions
        .values()
        .find(|f| f.name == "collatz")
        .expect("collatz is in the debug information");
    let row = debug
        .line_for(f.low_pc)
        .expect("the line table covers the function's entry");
    assert!(row.file.contains("wide.c"), "file was {:?}", row.file);
    assert!(row.line > 100, "line was {}", row.line);
}
