//! How much of what the decoder decodes the lifter also models.
//!
//! The same shape as the decoder's coverage gate, and for the same reason: an
//! instruction the lifter does not model is a gap with a floor that only rises,
//! and it is reported honestly rather than approximated.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, analyze};
use r12e_core::Arch;
use r12e_format::LoadOptions;
use r12e_ir::lift;

/// Floor on the share of decoded instructions the lifter models. Only raised.
const MIN_COVERAGE: f64 = 0.996;
/// The x86-64 floor, which has only the fixtures behind it: this host runs no
/// x86 system binaries, so the corpus is smaller and the number is not
/// comparable to the AArch64 one.
const MIN_X86_COVERAGE: f64 = 0.999;

fn targets(arch: &Arch) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    let tag = if *arch == Arch::AArch64 { "a64" } else { "x64" };
    if let Ok(entries) = std::fs::read_dir(&dir) {
        for e in entries.flatten() {
            let p = e.path();
            let n = p.file_name().unwrap().to_string_lossy().into_owned();
            if n.contains(tag) && !n.contains("macho") && !n.ends_with(".out") {
                out.push(p);
            }
        }
    }
    if *arch == Arch::AArch64 {
        for p in [
            "/usr/lib/aarch64-linux-gnu/libc.so.6",
            "/bin/bash",
            "/bin/ls",
        ] {
            let p = PathBuf::from(p);
            if p.is_file() {
                out.push(p);
            }
        }
    }
    out
}

/// Count what lifts, over the instructions inside recovered functions.
///
/// Walking every executable byte instead would count section padding, which
/// decodes as `udf` and made up a seventh of the denominator. Measuring against
/// what analysis believes is code is the honest denominator.
fn measure(arch: &Arch) -> (u64, u64, BTreeMap<String, u64>) {
    let mut decoded = 0u64;
    let mut lifted = 0u64;
    let mut missing: BTreeMap<String, u64> = BTreeMap::new();

    for path in targets(arch) {
        let Ok(data) = std::fs::read(&path) else {
            continue;
        };
        let Ok(obj) = r12e_format::load(&data, &LoadOptions::default()) else {
            continue;
        };
        if obj.arch != *arch {
            continue;
        }
        let program = analyze(obj, &Options::default());
        for f in program.functions_by_address() {
            for insn in program.instructions(f) {
                decoded += 1;
                if lift::lift(arch, &insn).complete {
                    lifted += 1;
                } else {
                    *missing.entry(insn.mnemonic.to_string()).or_default() += 1;
                }
            }
        }
    }
    (decoded, lifted, missing)
}

#[test]
fn the_lifter_models_most_of_what_the_decoder_decodes() {
    check(&Arch::AArch64, MIN_COVERAGE, 10_000);
}

#[test]
fn the_x86_lifter_models_most_of_what_the_decoder_decodes() {
    check(&Arch::X86_64, MIN_X86_COVERAGE, 2_000);
}

fn check(arch: &Arch, floor: f64, minimum: u64) {
    let (decoded, lifted, missing) = measure(arch);
    if decoded < minimum {
        return; // no corpus
    }
    let coverage = lifted as f64 / decoded as f64;
    let mut worst: Vec<(&String, &u64)> = missing.iter().collect();
    worst.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    let summary: Vec<String> = worst
        .iter()
        .take(10)
        .map(|(m, n)| format!("{m} x{n}"))
        .collect();
    assert!(
        coverage >= floor,
        "{arch:?}: lifted {:.2}% of {decoded} decoded instructions, floor is {:.2}%\n\
         biggest gaps: {}",
        coverage * 100.0,
        floor * 100.0,
        summary.join(", ")
    );
    println!(
        "{arch:?} lift coverage: {lifted} of {decoded} decoded instructions, {:.2}%",
        coverage * 100.0
    );
}

/// A work list, not a gate. Ignored by default.
#[test]
#[ignore]
fn lift_coverage_report() {
    for arch in [Arch::AArch64, Arch::X86_64] {
        report(&arch);
    }
}

fn report(arch: &Arch) {
    let (decoded, lifted, missing) = measure(arch);
    println!("--- {arch:?} ---");
    println!(
        "{lifted} of {decoded} lifted ({:.2}%)",
        lifted as f64 / decoded.max(1) as f64 * 100.0
    );
    let mut v: Vec<(String, u64)> = missing.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (m, n) in v.iter().take(40) {
        println!("{n:>8}  {m}");
    }
}
