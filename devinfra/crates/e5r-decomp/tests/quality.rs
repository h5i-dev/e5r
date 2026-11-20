//! The decompiler measured by whether a compiler accepts what it wrote.
//!
//! Reading decompiler output cannot tell you whether it is well formed. Handing
//! it to a C compiler can, and that is the gate here: every function recovered
//! from the fixtures is decompiled, the whole lot is written as one translation
//! unit, and `clang -c` has to accept it. A structuring bug that drops a brace
//! or an expression rebuilder that emits an unbalanced cast fails loudly.
//!
//! The second measure is the goto count. Structuring that gives up produces a
//! labelled goto, which is honest but is also the thing to improve, so the
//! density is held under a ceiling that only comes down.

use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_analysis::{Options, Program, analyze};
use e5r_format::LoadOptions;

/// Ceiling on the share of functions the structuring could not express without
/// a label. Only lowered.
///
/// The share rather than the count: one function of forty nested loops can
/// need twenty labels, and averaging those over the corpus says more about
/// that one function than about the structuring.
const MAX_UNSTRUCTURED: f64 = 0.07;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// Decompile every recovered function into one translation unit, by exactly
/// the path the command line takes.
fn decompile_all(p: &Program) -> e5r_api::Unit {
    let targets: Vec<&e5r_analysis::Function> = p
        .functions_by_address()
        .filter(|f| f.is_complete() && f.cfg.blocks.len() <= 300)
        .collect();
    e5r_api::decompile_program(p, &targets)
}

fn clang() -> Option<String> {
    for name in ["clang", "cc", "gcc"] {
        if Command::new(name).arg("--version").output().is_ok() {
            return Some(name.to_string());
        }
    }
    None
}

/// Compile one translation unit and return what the compiler said.
fn compile(text: &str, tag: &str) -> Option<(bool, String)> {
    let cc = clang()?;
    let dir = std::env::temp_dir().join(format!("e5r-decomp-{tag}"));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("out.c");
    std::fs::write(&src, text).ok()?;
    let output = Command::new(cc)
        .args(["-c", "-w", "-ffreestanding", "-o"])
        .arg(dir.join("out.o"))
        .arg(&src)
        .output()
        .ok()?;
    Some((
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    ))
}

fn check(binary: &str) {
    let Some(p) = open(binary) else { return };
    let unit = decompile_all(&p);
    let count = unit.functions.len();
    if count == 0 {
        return;
    }
    let Some((ok, errors)) = compile(&unit.text(), binary) else {
        return; // no compiler here
    };
    assert!(
        ok,
        "{binary}: the decompiled output of {count} functions does not compile:\n{}",
        errors.lines().take(20).collect::<Vec<_>>().join("\n")
    );

    let gotos = unit.gotos();
    let unstructured = unit.functions.iter().filter(|f| f.gotos > 0).count();
    let share = unstructured as f64 / count as f64;
    assert!(
        share <= MAX_UNSTRUCTURED,
        "{binary}: {unstructured} of {count} functions needed a label \
         ({share:.2}), ceiling is {MAX_UNSTRUCTURED}; {gotos} gotos in total"
    );
    println!(
        "{binary}: {count} functions, {unstructured} needed a label ({share:.2}), \
         {gotos} gotos"
    );
}

#[test]
fn aarch64_output_compiles() {
    for opt in ["O0", "O1", "O2", "O3", "Os"] {
        check(&format!("driver.a64.{opt}"));
    }
}

#[test]
fn x86_output_compiles() {
    for opt in ["O0", "O1", "O2", "O3", "Os"] {
        check(&format!("driver.x64.{opt}"));
    }
}

#[test]
fn a_stripped_binary_decompiles_too() {
    check("hello.a64.O2.stripped");
}

/// The fixtures built with debug information, where the output is typed from
/// what the compiler recorded rather than from the calling convention.
#[test]
fn output_typed_from_debug_information_compiles() {
    for name in [
        "wide.a64.O0.o",
        "wide.a64.O1.o",
        "wide.a64.O2.o",
        "wide.x64.O0.o",
        "wide.x64.O2.o",
        "shapes.a64.O0.o",
        "shapes.x64.O2.o",
        "hello.a64.O0",
        "hello.a64.O2",
    ] {
        check(name);
    }
}
