//! The loop the tool exists for: decompile, assert what the engine could not
//! work out, decompile again and see the assertion in the output.
//!
//! An assertion that is parsed, validated, stored and then ignored by the
//! emitter is the same as no assertion at all, so every test here compares two
//! decompilations of the same function and pins what the declaration changed.
//! The last one pins what it did not change, which is the half that keeps an
//! assertion from being a licence to rewrite the body.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use e5r_analysis::{Function, Options, Program, analyze};
use e5r_core::Addr;
use e5r_decomp::expr::Role;
use e5r_format::LoadOptions;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

fn function<'a>(p: &'a Program, name: &str) -> &'a Function {
    p.functions_by_address()
        .find(|f| f.display_name() == name)
        .unwrap_or_else(|| panic!("no function called {name}"))
}

/// Decompile one function, with an asserted declaration or without.
fn decompile(p: &Program, name: &str, declaration: Option<&str>) -> e5r_api::Decompiled {
    let f = function(p, name);
    let mut declared: BTreeMap<Addr, String> = BTreeMap::new();
    if let Some(text) = declaration {
        declared.insert(f.entry, text.to_string());
    }
    e5r_api::decompile::decompile_function_with(p, f, &declared)
}

/// The whole translation unit, so the definitions a declaration needs are in
/// view as well as the body.
fn unit(p: &Program, name: &str, declaration: Option<&str>) -> String {
    let f = function(p, name);
    let mut declared: BTreeMap<Addr, String> = BTreeMap::new();
    if let Some(text) = declaration {
        declared.insert(f.entry, text.to_string());
    }
    e5r_api::decompile::decompile_program_with(p, &[f], &declared).text()
}

#[test]
fn an_assertion_names_the_parameters_and_narrows_their_types() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    // Nothing declared this binary: the recovery can say that three argument
    // registers arrive with values, and how wide each one is read.
    let before = decompile(&p, "nestedoffset", None);
    assert_eq!(
        before.signature,
        "uint64_t nestedoffset(uint64_t arg0, uint32_t arg1, uint32_t arg2)"
    );
    assert!(before.text.contains("arg0 + ("), "{}", before.text);

    let after = decompile(
        &p,
        "nestedoffset",
        Some(
            "int nestedoffset(struct outer { int first; int pad; int array[16]; } *ptr, int a, int b)",
        ),
    );
    assert_eq!(
        after.signature,
        "int32_t nestedoffset(struct outer *ptr, int32_t a, int32_t b)"
    );
    // The names reach the body, and the declared pointer is cast back to an
    // integer wherever the machine used it as an address: C would scale the
    // arithmetic and the machine has already done the scaling.
    assert!(after.text.contains("(uint64_t)ptr + ("), "{}", after.text);
    assert!(
        after.text.contains("(uint32_t)a + (uint32_t)b"),
        "{}",
        after.text
    );
    // The declared return type is the cast on the way out.
    assert!(after.text.contains("return (int32_t)("), "{}", after.text);
    assert!(!after.text.contains("arg0"), "{}", after.text);

    // A structure the declaration introduced is defined before it is used, so
    // what comes out is a translation unit and not a fragment.
    let text = unit(
        &p,
        "nestedoffset",
        Some(
            "int nestedoffset(struct outer { int first; int pad; int array[16]; } *ptr, int a, int b)",
        ),
    );
    assert!(
        text.contains("struct outer { int32_t first; int32_t pad; int32_t array[16]; };"),
        "{text}"
    );
}

#[test]
fn an_asserted_void_return_drops_the_result_the_code_left_behind() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    let before = decompile(&p, "twodim", None);
    assert!(
        before.signature.starts_with("uint64_t "),
        "{}",
        before.signature
    );
    assert!(before.text.contains("return ("), "{}", before.text);

    let after = decompile(&p, "twodim", Some("void twodim(int valin, int valout)"));
    assert_eq!(
        after.signature,
        "void twodim(int32_t valin, int32_t valout)"
    );
    // Nothing is returned and nothing pretends to be.
    assert!(after.text.contains("    return;\n"), "{}", after.text);
    assert!(!after.text.contains("return ("), "{}", after.text);
    // The code did leave something in a register, and saying so is how an
    // analyst finds out their declaration was the surprising one.
    assert!(
        after
            .conflicts
            .iter()
            .any(|c| c.contains("returns nothing and the code leaves a value")),
        "{:?}",
        after.conflicts
    );
}

#[test]
fn an_assertion_outranks_the_debug_information_and_the_conflict_is_recorded() {
    let Some(p) = open("wide.x64.O0.o") else {
        return;
    };
    // The compiler recorded this one, and the analyst still wins.
    let before = decompile(&p, "arith8", None);
    assert_eq!(before.signature, "u8 arith8(u8 a, u8 b)");
    assert!(!before.asserted);
    assert!(before.conflicts.is_empty());

    let after = decompile(
        &p,
        "arith8",
        Some("int arith8(unsigned char a, unsigned char b)"),
    );
    assert_eq!(after.signature, "int32_t arith8(uint8_t a, uint8_t b)");
    assert!(after.asserted);
    assert!(after.text.contains("return (int32_t)("), "{}", after.text);
    // The declaration names two arguments and the code reads four registers.
    // The declaration is honoured and what it overrode is reported rather than
    // discarded, which is the whole of bet four.
    assert!(
        after
            .conflicts
            .iter()
            .any(|c| c.contains("which the declaration does not name")),
        "{:?}",
        after.conflicts
    );
}

#[test]
fn a_result_too_large_for_a_register_declares_the_pointer_the_caller_passes() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    let after = decompile(
        &p,
        "heapstring",
        Some("struct big { long a; long b; long c; } heapstring(int n)"),
    );
    // Twenty-four bytes do not fit the result registers, so the caller passes
    // the address of the result in the first argument register and every
    // declared parameter sits one register further along. Getting this wrong
    // makes every name in the body wrong.
    assert_eq!(
        after.signature,
        "void heapstring(struct big *__result, int32_t n)"
    );
    assert!(after.text.contains("(uint64_t)__result"), "{}", after.text);
}

#[test]
fn a_declaration_that_does_not_parse_changes_nothing() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    let before = decompile(&p, "nestedoffset", None);
    let after = decompile(&p, "nestedoffset", Some("int nestedoffset(struct"));
    assert_eq!(before.text, after.text);
    assert!(!after.asserted);
}

#[test]
fn an_assertion_changes_the_names_and_the_types_and_nothing_else() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    let declaration =
        "int nestedoffset(struct outer { int first; int pad; int array[16]; } *ptr, int a, int b)";
    let before = decompile(&p, "nestedoffset", None);
    let after = decompile(&p, "nestedoffset", Some(declaration));

    // The structuring is untouched: a declaration says what the values are,
    // never what the control flow is.
    assert_eq!(before.gotos, after.gotos);
    assert_eq!(before.lost, after.lost);
    assert_eq!(before.locals, after.locals);
    assert_eq!(before.unmodelled, after.unmodelled);

    let (old, new): (Vec<&str>, Vec<&str>) =
        (before.text.lines().collect(), after.text.lines().collect());
    assert_eq!(
        old.len(),
        new.len(),
        "{}\n----\n{}",
        before.text,
        after.text
    );
    // Every line that changed has to be explained by something the
    // declaration said. Anything else is the assertion being used as a licence
    // to rewrite the body.
    let introduced = ["ptr", "a", "b", "int32_t", "struct outer"];
    for (old, new) in old.iter().zip(new.iter()) {
        if old == new {
            continue;
        }
        assert!(
            introduced.iter().any(|w| word(new, w)),
            "line changed for no declared reason:\n  {old}\n  {new}"
        );
    }
}

#[test]
fn the_variables_come_back_with_their_names_and_types() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    let d = decompile(&p, "dupptr", None);
    // A count of locals cannot be matched against anything. These can.
    assert_eq!(d.variables.len(), d.locals + 2, "{:?}", d.variables);
    let named = |name: &str| {
        d.variables
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("no variable {name} in {:?}", d.variables))
    };
    assert_eq!(named("arg0").role, Role::Parameter);
    assert_eq!(named("arg0").ty, "struct s_dupptr_arg0 *");
    assert_eq!(named("v2").role, Role::Local);
    assert_eq!(named("v2").ty, "uint32_t");
    assert_eq!(named("v2").size, 4);
    // Every variable the text declares is a variable the text mentions.
    for v in &d.variables {
        assert!(word(&d.text, &v.name), "{} is not in the body", v.name);
    }

    // A declaration renames them, and the report renames with it.
    let after = decompile(
        &p,
        "dupptr",
        Some("long dupptr(unsigned int *table, int index)"),
    );
    assert!(
        after
            .variables
            .iter()
            .any(|v| v.name == "table" && v.ty == "uint32_t *" && v.role == Role::Parameter)
    );
}

#[test]
fn an_access_through_a_pointer_reads_as_a_field() {
    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    // Nothing declared this pointer. The offsets the code touches through it
    // are enough to say it points at a structure, and an access at a known
    // offset then reads as the field it is rather than as arithmetic.
    let text = unit(&p, "dupptr", None);
    assert!(text.contains("struct s_dupptr_arg0 {"), "{text}");
    assert!(text.contains("arg0[v0].field_c"), "{text}");
    // The name says the offset, which is the honest thing for a field nobody
    // declared: `field_c` is this crate's name for what is at twelve, not a
    // name anyone wrote down.
    assert!(!text.contains("->sub"), "{text}");
}

#[test]
fn a_declared_field_name_beats_the_one_the_offset_implies() {
    use e5r_ir::op::Op;
    use e5r_ir::ssa::SsaKind;

    let Some(p) = open("dt-memory.x64.O2") else {
        return;
    };
    let f = function(&p, "dupptr");
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

    let abi = e5r_ir::abi::of(&p.object.arch);
    let first = abi.integer_arguments[0];
    let prototype = e5r_decomp::Prototype {
        parameters: vec![e5r_decomp::Param {
            name: "p".to_string(),
            decl: "struct thing *p".to_string(),
            floating: false,
            pointer: true,
            size: 8,
            fields: vec![(4, 4), (12, 4)],
            stride: Some(4),
            stack: None,
        }],
        returns: Some("uint64_t".to_string()),
        definitions: Vec::new(),
        locals: BTreeMap::new(),
    };
    let mut r = e5r_decomp::expr::Rebuilder::new(&ssa);
    r.declare(&prototype);

    let load = ssa
        .blocks
        .values()
        .flat_map(|b| b.ops.iter())
        .find(|op| {
            op.kind == SsaKind::Op(Op::Load) && r.field_access(op.inputs.first(), op.size).is_some()
        })
        .expect("a load through the pointer");

    // With nothing declared, the field is named after the offset it is at,
    // which says on its face that this crate made the name up.
    assert!(r.expr(load).to_string().contains("field_c"));

    // With a declaration, the name a person wrote down is the one that prints.
    r.field_names
        .insert(first, BTreeMap::from([(12i64, "count".to_string())]));
    let declared = r.expr(load).to_string();
    assert!(declared.contains("count"), "{declared}");
    assert!(!declared.contains("field_c"), "{declared}");
}

/// True when a name appears in a text as a whole word.
fn word(text: &str, name: &str) -> bool {
    e5r_decomp::expr::mentions(text, name)
}

/// Asking for one function gives the same body as asking for all of them.
///
/// The callee table used to hold only what was asked for, so a call to
/// anything else rendered as an anonymous name with no arguments. That is two
/// different answers for one function depending on how the question was
/// phrased, and the one you get alone is the wrong one: it drops the
/// arguments, which is undefined behaviour in the emitted C.
#[test]
fn a_function_decompiles_the_same_alone_as_in_a_whole_program() {
    for name in ["dt-calls.a64.O2", "driver.a64.O2", "dt-control.x64.O2"] {
        let Some(p) = open(name) else { continue };
        let every: Vec<&e5r_analysis::Function> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .collect();
        let whole = e5r_api::decompile_program(&p, &every);
        assert!(!whole.functions.is_empty(), "{name} decompiled nothing");
        for d in &whole.functions {
            let Some(f) = p.function(d.addr) else {
                continue;
            };
            let alone = e5r_api::decompile_function(&p, f);
            assert_eq!(
                alone.text, d.text,
                "{name}: {} differs alone from how it reads in the whole program",
                d.name
            );
        }
    }
}
