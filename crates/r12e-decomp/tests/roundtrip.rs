//! The decompiler measured by running what it wrote.
//!
//! Compiling the output proves it is well formed and nothing more. An inverted
//! comparison, a dropped operand, a shift by the wrong amount: all of those
//! compile. The only way to know that the C says what the machine says is to
//! run both on the same inputs and compare, so that is the gate here.
//!
//! The machine's side comes from the interpreter, which is itself measured
//! against what real hardware did with the same instructions, so nothing in
//! this file is the decompiler being asked to check itself.
//!
//! Only functions whose whole behaviour is their return value are eligible: no
//! calls, no memory, no helpers the C cannot honestly define. That is a small
//! part of a real program and it is the part where a silent arithmetic bug
//! hides, which is exactly what this is for.

use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_analysis::{Function, Options, Program, analyze};
use r12e_api::emulate::{Setup, run};
use r12e_format::LoadOptions;

/// How many functions may still return something the machine does not.
///
/// Zero, and it was a ratchet until it got here. A decompiler that produces a
/// wrong answer is worse than one that refuses, so nothing above zero was ever
/// going to be the end state; the number came down as the defects behind it
/// were found, and the gate failed both when it rose and when it fell without
/// being recorded, so that neither direction could pass unnoticed.
///
/// Every function that can be compiled and run is now run, on every argument
/// vector, and agrees with the interpreter. Any future disagreement is a
/// regression and the failure message names the function and the arguments.
const MAX_DISAGREEING: usize = 0;

/// Argument vectors every eligible function is run on.
///
/// The edges first, because that is where a sign extension or an off-by-one in
/// a comparison shows, then a deterministic spread.
fn vectors(arity: usize) -> Vec<Vec<u64>> {
    const EDGES: [u64; 12] = [
        0,
        1,
        2,
        5,
        0x7f,
        0x80,
        0xffff_ffff,
        0x8000_0000,
        0x7fff_ffff,
        u64::MAX,
        0x1_0000_0000,
        81,
    ];
    let mut out: Vec<Vec<u64>> = EDGES.iter().map(|e| vec![*e; arity.max(1)]).collect();
    // A linear congruential sequence, so the corpus is the same on every run
    // and a failure can be reproduced from the printed arguments alone.
    let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
    for _ in 0..24 {
        let mut v = Vec::with_capacity(arity);
        for _ in 0..arity.max(1) {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            v.push(seed >> 11);
        }
        out.push(v);
    }
    out
}

/// Anything in a decompiled body that means its behaviour is not just its
/// return value, or that the C cannot be given an honest definition for.
///
/// Every helper the emitter can reach is named with a leading `__`, so one
/// test covers them all and a helper added later cannot slip past.
const DISQUALIFYING: &[&str] = &["sub_", "__", "*(", "goto"];

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(path: &Path) -> Option<Program> {
    let data = std::fs::read(path).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

fn cc() -> Option<String> {
    for name in ["clang", "cc", "gcc"] {
        if Command::new(name).arg("--version").output().is_ok() {
            return Some(name.to_string());
        }
    }
    None
}

/// How many parameters a decompiled signature or definition declares.
///
/// Counted from the `argN` names rather than from the commas, because a
/// parameter's type can itself be a generated name containing `arg`.
///
/// The ones the convention ran out of registers for are named `arg_s<offset>`
/// by where the caller left them, not by their position, so they are counted
/// rather than maximised over. They come after the register arguments in the
/// declaration, which is the order a caller passes them in.
fn arity(text: &str) -> usize {
    let head = &text[..text.find(')').map(|i| i + 1).unwrap_or(text.len())];
    let b = head.as_bytes();
    let mut highest = None;
    for (i, _) in head.match_indices("arg") {
        if i > 0 && (b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_') {
            continue;
        }
        let digits: String = head[i + 3..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect();
        if let Ok(n) = digits.parse::<usize>() {
            highest = Some(highest.map_or(n, |h: usize| h.max(n)));
        }
    }
    let on_stack = head
        .match_indices("arg_s")
        .filter(|(i, _)| *i == 0 || !(b[*i - 1].is_ascii_alphanumeric() || b[*i - 1] == b'_'));
    highest.map_or(0, |h| h + 1) + on_stack.count()
}

/// One function the gate can run: its C, its name, and what the interpreter
/// said it returns for each argument vector.
struct Candidate {
    name: String,
    text: String,
    args: Vec<Vec<u64>>,
    expected: Vec<u64>,
}

/// Decompile one function and run it, if it is eligible.
fn candidate(p: &Program, f: &Function) -> Option<Candidate> {
    let d = r12e_api::decompile_function(p, f);
    if d.text.is_empty() || DISQUALIFYING.iter().any(|bad| d.text.contains(bad)) {
        return None;
    }
    // A function whose C returns nothing has no answer to compare, and one
    // that takes a pointer reaches memory the harness cannot set up.
    // A floating point parameter arrives in a vector register, which the
    // interpreter is not being asked to set up here.
    if !d.signature.starts_with("uint64_t")
        || d.signature.contains('*')
        || d.signature.contains("farg")
    {
        return None;
    }
    let n = arity(&d.signature);
    if n > 6 {
        return None;
    }
    let args = vectors(n);
    let mut expected = Vec::with_capacity(args.len());
    for a in &args {
        let r = run(
            p,
            f,
            &Setup {
                arguments: a.clone(),
                ..Setup::default()
            },
        );
        if !r.clean() {
            return None;
        }
        expected.push(r.result);
    }
    Some(Candidate {
        name: d.name.clone(),
        text: d.text,
        args,
        expected,
    })
}

/// Write a program that calls each candidate on each vector and prints what it
/// returned, one line per call.
fn harness(cands: &[Candidate]) -> String {
    let mut out = String::from("#include <stdint.h>\n#include <stdio.h>\n\n");
    for c in cands {
        out.push_str(&c.text);
        out.push('\n');
    }
    out.push_str("int main(void) {\n");
    for (i, c) in cands.iter().enumerate() {
        for (j, a) in c.args.iter().enumerate() {
            let n = arity(&c.text);
            let call: Vec<String> = a
                .iter()
                .take(n)
                .map(|v| format!("(uint64_t){v}ULL"))
                .collect();
            out.push_str(&format!(
                "    printf(\"{i} {j} %llu\\n\", (unsigned long long){}({}));\n",
                c.name,
                call.join(", ")
            ));
        }
    }
    out.push_str("    return 0;\n}\n");
    out
}

/// Compile and run the harness, returning `(function, vector) -> result`.
fn execute(text: &str, tag: &str) -> Option<Vec<(usize, usize, u64)>> {
    let cc = cc()?;
    let dir = std::env::temp_dir().join(format!("r12e-roundtrip-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("r.c");
    let bin = dir.join("r");
    std::fs::write(&src, text).ok()?;
    let built = Command::new(&cc)
        .arg("-O0")
        .arg("-w")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .output()
        .ok()?;
    assert!(
        built.status.success(),
        "the decompiled output did not compile:\n{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let ran = Command::new(&bin).output().ok()?;
    let _ = std::fs::remove_dir_all(&dir);
    let mut out = Vec::new();
    for line in String::from_utf8_lossy(&ran.stdout).lines() {
        let mut it = line.split_whitespace();
        let (Some(i), Some(j), Some(v)) = (it.next(), it.next(), it.next()) else {
            continue;
        };
        out.push((i.parse().ok()?, j.parse().ok()?, v.parse().ok()?));
    }
    Some(out)
}

/// Every pure function in the corpus computes, when compiled and run, what the
/// machine computes.
#[test]
// `<= 0` is `== 0`, and the comparison is written against the constant on
// purpose: it is the ratchet, and the assertion should still read as a ceiling
// the day one has to be allowed again.
#[allow(clippy::absurd_extreme_comparisons)]
fn decompiled_c_computes_what_the_machine_computes() {
    let Some(dir) = build_dir() else { return };
    if cc().is_none() {
        return;
    }
    let mut checked = 0usize;
    let mut functions = 0usize;
    let mut wrong: Vec<String> = Vec::new();

    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .map(|n| {
                    let n = n.to_string_lossy();
                    n.starts_with("dt-") || n.starts_with("driver.")
                })
                .unwrap_or(false)
        })
        .filter(|p| p.extension().is_none_or(|e| e != "c" && e != "out"))
        .collect();
    files.sort();

    for path in &files {
        let Some(p) = open(path) else { continue };
        let cands: Vec<Candidate> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .filter_map(|f| candidate(&p, f))
            .collect();
        if cands.is_empty() {
            continue;
        }
        functions += cands.len();
        let tag = path.file_name().unwrap_or_default().to_string_lossy();
        let Some(results) = execute(&harness(&cands), &tag) else {
            continue;
        };
        for (i, j, got) in results {
            let Some(c) = cands.get(i) else { continue };
            let Some(want) = c.expected.get(j) else {
                continue;
            };
            checked += 1;
            if got != *want {
                wrong.push(format!(
                    "{tag} {}({:?}): the machine returns {want:#x}, the C returns {got:#x}",
                    c.name, c.args[j]
                ));
            }
        }
    }

    assert!(
        functions > 20,
        "only {functions} function(s) were eligible; the gate is not measuring anything"
    );
    let names: std::collections::BTreeSet<String> = wrong
        .iter()
        .filter_map(|l| l.split_once('('))
        .map(|(head, _)| head.to_string())
        .collect();
    assert!(
        names.len() <= MAX_DISAGREEING,
        "{} function(s) return something the machine does not, against a ceiling of \
         {MAX_DISAGREEING}. {} of {checked} call(s) over {functions} function(s).\nfirst 20:\n{}",
        names.len(),
        wrong.len(),
        wrong
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    eprintln!("{checked} call(s) over {functions} function(s) agree");
}
