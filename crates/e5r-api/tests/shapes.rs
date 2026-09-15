//! Structure recovery measured against the debug information.
//!
//! A function that walks an array of structures touches the same offsets the
//! declaration lists, and the machine code says so whether or not the binary
//! carries types. The oracle is DWARF: the fixture is compiled with debug
//! information, the recovery runs without looking at it, and the two are
//! compared.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_core::Addr;
use e5r_format::LoadOptions;
use e5r_types::ctype::Type;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// The shapes seen through each incoming pointer of one function.
fn shapes_of(p: &Program, name: &str) -> Option<BTreeMap<u64, e5r_ir::shape::Shape>> {
    let f = p
        .functions_by_address()
        .find(|f| f.display_name() == name)?;
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = e5r_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    e5r_ir::stack::promote(&mut ir);
    let mut ssa = e5r_ir::ssa::build(&ir);
    e5r_ir::opt::optimize(&mut ssa);
    Some(
        e5r_ir::shape::shapes(&ssa)
            .into_iter()
            .map(|(l, s)| (l.offset, s))
            .collect(),
    )
}

/// The fields the debug information declares for the first parameter.
fn declared_fields(p: &Program, name: &str) -> Option<Vec<(i64, u8)>> {
    let d = p.object.debug.as_ref()?;
    let f = d.functions.values().find(|f| f.name == name)?;
    let (_, ty) = f.signature.parameters.first()?;
    let Type::Pointer(inner) = d.types.get(d.types.resolve(*ty))? else {
        return None;
    };
    let Type::Composite(c) = d.types.get(d.types.resolve(*inner))? else {
        return None;
    };
    Some(
        c.fields
            .iter()
            .map(|field| {
                (
                    field.offset as i64,
                    d.types.size_of(field.ty).unwrap_or(0) as u8,
                )
            })
            .collect(),
    )
}

#[test]
fn the_fields_of_a_structure_come_out_of_the_code() {
    for fixture in ["wide.a64.O0.o", "wide.a64.O1.o", "wide.x64.O0.o"] {
        let Some(p) = open(fixture) else { continue };
        let Some(shapes) = shapes_of(&p, "use_struct") else {
            continue;
        };
        let Some(declared) = declared_fields(&p, "use_struct") else {
            continue;
        };
        assert!(!declared.is_empty(), "{fixture}: no declared fields");

        // The pointer is the first argument, wherever the convention puts it.
        let abi = e5r_ir::abi::of(&p.object.arch);
        let first = abi.integer_arguments[0];
        let shape = shapes
            .get(&first)
            .unwrap_or_else(|| panic!("{fixture}: nothing was seen through the first argument"));

        let recovered = shape.fields();
        assert_eq!(
            recovered, declared,
            "{fixture}: recovered {recovered:?}, the debug information says {declared:?}"
        );
        // And the stride says how big the structure is.
        assert_eq!(
            shape.size(),
            Some(16),
            "{fixture}: the element size came out as {:?}",
            shape.size()
        );
    }
}

#[test]
fn an_array_walk_reports_its_element_size() {
    for fixture in ["wide.a64.O0.o", "wide.x64.O0.o"] {
        let Some(p) = open(fixture) else { continue };
        let Some(shapes) = shapes_of(&p, "sum_array") else {
            continue;
        };
        let abi = e5r_ir::abi::of(&p.object.arch);
        let Some(shape) = shapes.get(&abi.integer_arguments[0]) else {
            continue;
        };
        // `u64 *a` read one element at a time: eight bytes at offset zero.
        assert_eq!(shape.fields(), vec![(0, 8)], "{fixture}");
    }
}

#[test]
fn nothing_is_reported_for_a_function_that_takes_no_pointers() {
    let Some(p) = open("wide.a64.O0.o") else {
        return;
    };
    let Some(shapes) = shapes_of(&p, "arith64") else {
        return;
    };
    let abi = e5r_ir::abi::of(&p.object.arch);
    assert!(
        !shapes.contains_key(&abi.integer_arguments[0]),
        "an integer argument was reported as a pointer"
    );
}
