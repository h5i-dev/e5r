//! Emulating functions out of object files, against what the processor said.
//!
//! The same case table the lifter's oracle uses, run against the relocatable
//! objects rather than the linked drivers. It exercises a different path: an
//! object's call targets are written as zero and filled in by relocations, so
//! a wrong relocation makes every call land on itself and the answers diverge.

use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_format::LoadOptions;

fn build() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// One case: what to call, with what, and what the processor answered.
struct Case {
    name: String,
    kind: String,
    args: Vec<u64>,
    expected: u64,
}

fn cases() -> Vec<Case> {
    let Some(dir) = build() else {
        return Vec::new();
    };
    let table = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/portable/cases.txt");
    let Ok(text) = std::fs::read_to_string(table) else {
        return Vec::new();
    };
    let Ok(recorded) = std::fs::read(dir.join("driver.a64.O2.out")) else {
        return Vec::new();
    };

    let mut out = Vec::new();
    for (n, line) in text
        .lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
        .enumerate()
    {
        let mut parts = line.split_whitespace();
        let head = parts.next().unwrap_or_default();
        let (name, kind) = head.split_once(':').unwrap_or((head, "u64"));
        // Only the cases whose arguments are numbers: a case that points at a
        // global belongs to the driver that defines it.
        let mut args = Vec::new();
        let mut usable = true;
        for token in parts {
            match parse(token) {
                Some(v) => args.push(v),
                None => usable = false,
            }
        }
        // Floating results and floating arguments go through other registers,
        // which this surface does not set.
        if !usable || kind.starts_with('f') || line.contains('.') {
            continue;
        }
        let Some(bytes) = recorded.get(n * 8..n * 8 + 8) else {
            continue;
        };
        out.push(Case {
            name: name.to_string(),
            kind: kind.to_string(),
            args,
            expected: u64::from_le_bytes(bytes.try_into().unwrap()),
        });
    }
    out
}

fn parse(token: &str) -> Option<u64> {
    if token.starts_with('&') {
        return None;
    }
    if let Some(hex) = token.strip_prefix("0x") {
        return u64::from_str_radix(hex, 16).ok();
    }
    if let Some(neg) = token.strip_prefix('-') {
        return Some((neg.parse::<i64>().ok()?).wrapping_neg() as u64);
    }
    token.parse::<u64>().ok()
}

/// The value the driver would have recorded, given what the register held.
fn widen(raw: u64, kind: &str) -> u64 {
    let (bits, signed) = match kind {
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

fn check(fixture: &str) {
    let Some(p) = open(fixture) else { return };
    let cases = cases();
    if cases.is_empty() {
        return;
    }

    let mut wrong = Vec::new();
    let mut ran = 0;
    for case in &cases {
        let Some(f) = p
            .functions_by_address()
            .find(|f| f.name.as_deref() == Some(case.name.as_str()))
        else {
            continue;
        };
        let setup = r12e_api::Setup {
            arguments: case.args.clone(),
            depth: 4096,
            ..Default::default()
        };
        let run = r12e_api::emulate::run(&p, f, &setup);
        if run.stop != r12e_ir::Stop::Returned {
            wrong.push(format!("{}{:?}: {:?}", case.name, case.args, run.stop));
            continue;
        }
        ran += 1;
        let got = widen(run.result, &case.kind);
        if got != case.expected {
            wrong.push(format!(
                "{}{:?} = {got:#x}, the processor said {:#x}",
                case.name, case.args, case.expected
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{fixture}: {} of {} cases disagree:\n  {}",
        wrong.len(),
        cases.len(),
        wrong.join("\n  ")
    );
    assert!(ran > 10, "{fixture}: only {ran} cases ran");
    println!("{fixture}: {ran} cases agree with the processor");
}

#[test]
fn object_files_emulate_to_the_same_answers() {
    for fixture in [
        "wide.a64.O0.o",
        "wide.a64.O1.o",
        "wide.a64.O2.o",
        "wide.x64.O0.o",
        "wide.x64.O2.o",
    ] {
        check(fixture);
    }
}
