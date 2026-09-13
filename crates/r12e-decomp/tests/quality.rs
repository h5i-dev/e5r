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

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_analysis::{Options, Program, analyze};
use r12e_core::Addr;
use r12e_format::LoadOptions;

/// Ceiling on gotos per function. Only lowered.
const MAX_GOTO_DENSITY: f64 = 0.26;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

struct Unit {
    text: String,
    functions: usize,
    gotos: usize,
}

/// Decompile every recovered function into one translation unit.
fn decompile_all(p: &Program) -> Unit {
    let mut declarations: Vec<String> = Vec::new();
    let mut bodies = String::new();
    let mut functions = 0;
    let mut gotos = 0;
    let mut seen: Vec<String> = Vec::new();

    for f in p.functions_by_address() {
        if !f.is_complete() || f.cfg.blocks.len() > 300 {
            continue;
        }
        let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
            .cfg
            .blocks
            .iter()
            .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
            .collect();
        let ir = r12e_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
        let mut ssa = r12e_ir::ssa::build(&ir);
        r12e_ir::opt::optimize(&mut ssa);
        // A name C will take, and only once: two symbols can share a name.
        let name = format!("f_{:x}", f.entry.get());
        if seen.contains(&name) {
            continue;
        }
        seen.push(name.clone());
        let out = r12e_decomp::decompile(&name, &ssa);
        declarations.extend(out.declarations);
        bodies.push_str(&out.text);
        bodies.push('\n');
        functions += 1;
        gotos += out.gotos;
    }

    declarations.sort();
    declarations.dedup();
    let mut text = String::from("#include <stdint.h>\n");
    for d in &declarations {
        text.push_str(d);
        text.push('\n');
    }
    text.push_str(&bodies);
    Unit {
        text,
        functions,
        gotos,
    }
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
    let dir = std::env::temp_dir().join(format!("r12e-decomp-{tag}"));
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
    if unit.functions == 0 {
        return;
    }
    let Some((ok, errors)) = compile(&unit.text, binary) else {
        return; // no compiler here
    };
    assert!(
        ok,
        "{binary}: the decompiled output of {} functions does not compile:\n{}",
        unit.functions,
        errors.lines().take(20).collect::<Vec<_>>().join("\n")
    );

    let density = unit.gotos as f64 / unit.functions as f64;
    assert!(
        density <= MAX_GOTO_DENSITY,
        "{binary}: {} gotos across {} functions ({density:.2} each), ceiling is {MAX_GOTO_DENSITY}",
        unit.gotos,
        unit.functions
    );
    println!(
        "{binary}: {} functions, {} gotos ({density:.2} each)",
        unit.functions, unit.gotos
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
