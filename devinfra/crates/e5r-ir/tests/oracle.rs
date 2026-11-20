//! The lifters measured against the machine, for real.
//!
//! One program is compiled for both architectures and executed: natively on
//! this host, and under qemu for the other one. The same calls are then lifted
//! and interpreted, and the answers have to match. Nothing here is an
//! assertion about what the lifter ought to do; every expected value came out
//! of a processor.
//!
//! The case table is shared with the driver that produced those answers, so a
//! case cannot exist on one side and not the other.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_core::{Addr, Arch};
use e5r_format::LoadOptions;
use e5r_ir::exec::run_with;
use e5r_ir::{Machine, Stop};

/// Where a fresh machine's stack lives, away from the image.
const STACK: u64 = 0x7fff_0000;
/// The return address a called function will pop, which stops the run.
const SENTINEL: u64 = 0xdead_0000;
/// How deep the interpreter follows calls, which recursion needs.
const DEPTH: u32 = 4096;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// One line of the case table.
struct Case {
    name: String,
    kind: String,
    args: Vec<Arg>,
}

enum Arg {
    Number(u64),
    /// A floating argument, as its bit pattern and its width.
    Float(u64, u8),
    Symbol(String),
}

fn cases() -> Vec<Case> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/portable/cases.txt");
    let text = std::fs::read_to_string(path).unwrap_or_default();
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        let head = parts.next().unwrap();
        let (name, kind) = head.split_once(':').unwrap_or((head, "u64"));
        let args = parts
            .map(|t| match t.strip_prefix('&') {
                Some(s) => Arg::Symbol(s.to_string()),
                None => parse_argument(t),
            })
            .collect();
        out.push(Case {
            name: name.to_string(),
            kind: kind.to_string(),
            args,
        });
    }
    out
}

/// A floating literal is one with a point or an exponent; a trailing `f` makes
/// it single precision, exactly as the C the driver was built from reads it.
fn parse_argument(t: &str) -> Arg {
    let single = t.ends_with('f') && !t.starts_with("0x");
    let body = if single { &t[..t.len() - 1] } else { t };
    let floating =
        !body.starts_with("0x") && (body.contains('.') || body.contains('e') || body.contains('E'));
    if floating {
        if let Ok(v) = body.parse::<f64>() {
            return if single {
                Arg::Float((v as f32).to_bits() as u64, 4)
            } else {
                Arg::Float(v.to_bits(), 8)
            };
        }
    }
    Arg::Number(parse_number(t))
}

fn parse_number(t: &str) -> u64 {
    if let Some(hex) = t.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).unwrap_or(0)
    } else if let Some(neg) = t.strip_prefix('-') {
        (neg.parse::<i64>().unwrap_or(0)).wrapping_neg() as u64
    } else {
        t.parse::<u64>().unwrap_or(0)
    }
}

/// The value the driver would have written, given what the return register
/// holds: the C cast to `u64` widens by the function's own return type.
fn widen(raw: u64, kind: &str) -> u64 {
    let (bits, signed) = match kind {
        // A floating result is compared as the bits the register holds, which
        // the driver recorded the same way.
        "f32" => (32, false),
        "f64" => return raw,
        "u8" => (8, false),
        "i8" => (8, true),
        "u16" => (16, false),
        "i16" => (16, true),
        "u32" => (32, false),
        "i32" => (32, true),
        "i64" => (64, true),
        _ => (64, false),
    };
    if bits == 64 {
        return raw;
    }
    let truncated = raw & ((1u64 << bits) - 1);
    if signed && truncated >> (bits - 1) == 1 {
        truncated | !((1u64 << bits) - 1)
    } else {
        truncated
    }
}

/// Set up the machine for a call and run it, returning the result register.
///
/// Integer and floating arguments have separate sequences of registers, which
/// is how both calling conventions work.
fn call(p: &Program, entry: Addr, args: &[Value], float_result: bool) -> (u64, e5r_ir::Outcome) {
    let mut m = Machine::over(&p.object.memory);
    m.budget = 1 << 24;
    // Real storage under the stack pointer, so a spill and its reload agree.
    m.write_mem(STACK - 0x8000, &[0u8; 0x10000]);
    match p.object.arch {
        Arch::AArch64 => {
            use e5r_ir::lift::aarch64::{gpr_offset, sp_offset, vec_offset};
            let (mut n, mut f) = (0u8, 0u8);
            for a in args {
                match a {
                    Value::Int(v) if n < 8 => {
                        m.set_reg(gpr_offset(n), 8, *v);
                        n += 1;
                    }
                    Value::Int(_) => {}
                    Value::Float(v, size) if f < 8 => {
                        m.set_reg(vec_offset(f), *size, *v);
                        f += 1;
                    }
                    Value::Float(..) => {}
                }
            }
            m.set_reg(sp_offset(), 8, STACK);
            // The link register holds an address that is not code, so the
            // outermost return stops rather than running on.
            m.set_reg(gpr_offset(30), 8, SENTINEL);
            let outcome = run_with(&mut m, &p.object.memory, &p.object.arch, entry, DEPTH);
            let result = if float_result {
                m.reg(vec_offset(0), 8)
            } else {
                m.reg(gpr_offset(0), 8)
            };
            (result, outcome)
        }
        _ => {
            use e5r_ir::lift::x86::{gpr_offset, sp_offset, vec_offset};
            // rdi, rsi, rdx, rcx, r8, r9 for integers, xmm0 onward for floats.
            const ORDER: [u8; 6] = [7, 6, 2, 1, 8, 9];
            let sp = STACK;
            m.set_reg(sp_offset(), 8, sp);
            m.write_mem(sp, &SENTINEL.to_le_bytes());
            let (mut n, mut f, mut stacked) = (0usize, 0u8, 0u64);
            for a in args {
                match a {
                    Value::Int(v) if n < 6 => {
                        m.set_reg(gpr_offset(ORDER[n]), 8, *v);
                        n += 1;
                    }
                    Value::Int(v) => {
                        m.write_mem(sp + 8 + stacked * 8, &v.to_le_bytes());
                        stacked += 1;
                    }
                    Value::Float(v, size) if f < 8 => {
                        m.set_reg(vec_offset(f), *size, *v);
                        f += 1;
                    }
                    Value::Float(..) => {}
                }
            }
            let outcome = run_with(&mut m, &p.object.memory, &p.object.arch, entry, DEPTH);
            let result = if float_result {
                m.reg(vec_offset(0), 8)
            } else {
                m.reg(gpr_offset(0), 8)
            };
            (result, outcome)
        }
    }
}

/// An argument as the machine takes it.
#[derive(Debug, Clone, Copy)]
enum Value {
    Int(u64),
    Float(u64, u8),
}

fn load(name: &str) -> Option<Program> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

fn symbols(p: &Program) -> BTreeMap<String, Addr> {
    p.object
        .symbols
        .iter()
        .map(|s| (s.name.clone(), s.addr))
        .collect()
}

/// Run every case against the recorded output of the real program.
fn check(binary: &str) {
    let Some(p) = load(binary) else { return };
    let Ok(recorded) = std::fs::read(build_dir().unwrap().join(format!("{binary}.out"))) else {
        return;
    };
    let cases = cases();
    assert_eq!(
        recorded.len(),
        cases.len() * 8,
        "{binary}: the recording has {} values and the table has {}",
        recorded.len() / 8,
        cases.len()
    );
    let table = symbols(&p);

    let mut wrong = Vec::new();
    let mut incomplete = Vec::new();
    for (n, case) in cases.iter().enumerate() {
        let Some(entry) = table.get(&case.name) else {
            incomplete.push(format!("{}: no symbol", case.name));
            continue;
        };
        let args: Vec<Value> = case
            .args
            .iter()
            .map(|a| match a {
                Arg::Number(v) => Value::Int(*v),
                Arg::Float(v, size) => Value::Float(*v, *size),
                Arg::Symbol(s) => Value::Int(table.get(s).map(|a| a.get()).unwrap_or(0)),
            })
            .collect();
        let expected = u64::from_le_bytes(recorded[n * 8..n * 8 + 8].try_into().unwrap());
        let floating = case.kind.starts_with('f') && case.kind != "flag";
        let (raw, outcome) = call(&p, *entry, &args, floating);
        if outcome.stop != Stop::Returned {
            incomplete.push(format!(
                "{}({:?}) stopped with {:?}, unlifted {:?}",
                case.name,
                args,
                outcome.stop,
                &outcome.unlifted[..outcome.unlifted.len().min(3)]
            ));
            continue;
        }
        let got = widen(raw, &case.kind);
        if got != expected {
            wrong.push(format!(
                "{}({args:?}) = {got:#x}, the machine says {expected:#x}",
                case.name
            ));
        }
    }

    assert!(
        wrong.is_empty(),
        "{binary}: {} of {} cases disagree with the processor:\n  {}",
        wrong.len(),
        cases.len(),
        wrong.join("\n  ")
    );
    // A case that did not finish is a gap rather than a wrong answer, but the
    // gate is the same: this corpus is the one the lifter is expected to cover.
    assert!(
        incomplete.is_empty(),
        "{binary}: {} of {} cases did not run to completion:\n  {}",
        incomplete.len(),
        cases.len(),
        incomplete.join("\n  ")
    );
}

/// Every optimization level of both architectures, because a vectorizer and a
/// scheduler reach different corners of the instruction set than a plain
/// translation does.
#[test]
fn aarch64_lifting_matches_the_processor() {
    for opt in ["O0", "O1", "O2", "O3", "Os"] {
        check(&format!("driver.a64.{opt}"));
    }
}

#[test]
fn x86_lifting_matches_the_processor() {
    for opt in ["O0", "O1", "O2", "O3", "Os"] {
        check(&format!("driver.x64.{opt}"));
    }
}
