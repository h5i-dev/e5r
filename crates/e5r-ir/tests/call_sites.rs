//! Convention detection over real code, gated on what the compiler recorded.
//!
//! `DW_TAG_call_site_parameter` is the producer saying where it put each
//! argument of each call. That is ground truth for argument counts and
//! positions on any fixture built with debug information, and it is the
//! strongest gate available: a detection that misses a register the compiler
//! says it filled loses an argument at every call site.
//!
//! The DWARF register numbers are translated through `e5r_ir::dwreg`, which
//! exists because nothing else joins the two numbering schemes: DWARF says
//! "register 5" and only that table knows it means `rdi`.
//!
//! The second half is a survey rather than a gate: how many functions in the
//! corpus come out non-standard, and which. A number that moves is a thing to
//! look at, not a thing to fail on, so it is printed.
//!
//! Read the PE rows with care. `lift::x86` and `opt` both ask
//! `abi::of(&arch)` which registers a call clobbers and which are live at a
//! return, and that answers System V for every x86-64 image. On a PE, `rsi`
//! and `rdi` are callee-saved, so the epilogue restoring them is dead code by
//! the System V answer and is deleted before this ever sees it. Until those
//! two take the container's convention, a Windows function that saves `rsi`
//! looks like one that clobbers it.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_core::Addr;
use e5r_core::provenance::Strength;
use e5r_format::dwarf::Location as DwarfLocation;
use e5r_format::{Format, LoadOptions};
use e5r_ir::abi::Abi;
use e5r_ir::conv::{self, Convention, Observed};
use e5r_ir::dwreg;
use e5r_ir::ssa::SsaFunction;

/// Floor on the share of recorded call-site arguments the detection also finds.
/// Only raised.
///
/// Measured at 33 of 37 over the fixtures below. The four it misses are one
/// function, `pick` in `em-paths.{a64,x64}.{O1,O2}`, and they are one defect
/// rather than four: `pick` copies its second argument into the first argument
/// register and then tail calls, a tail call lifts to `Op::Branch` and not to
/// `Op::Return`, and `opt`'s liveness treats the convention's registers as live
/// only at a `Return`. So the copy is dead by the optimizer's rules, dead code
/// elimination deletes it, and the only read of that register is gone before
/// detection sees the function. The fix belongs in `opt`, which must treat a
/// branch leaving the function as a call and hold the argument registers live
/// across it; the floor comes back up when it lands.
const MIN_AGREEMENT: f64 = 0.89;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// The convention the container declares, not just the one the machine does.
/// The same x86-64 code passes its first argument in `rdi` under ELF and in
/// `rcx` under PE, and reading a PE image with the System V table turns every
/// prologue that saves `xmm6` into an invented argument.
fn abi_of(p: &Program) -> Abi {
    e5r_ir::abi::of_container(&p.object.arch, p.object.format == Format::Pe)
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// Every function in SSA form, optimized, the way the rest of the engine
/// builds them.
fn ssa(p: &Program) -> BTreeMap<Addr, SsaFunction> {
    let mut out = BTreeMap::new();
    for f in p.functions_by_address() {
        let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
            .cfg
            .blocks
            .iter()
            .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
            .collect();
        if blocks.is_empty() {
            continue;
        }
        let mut ir = e5r_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
        e5r_ir::stack::promote(&mut ir);
        let mut built = e5r_ir::ssa::build(&ir);
        e5r_ir::opt::optimize(&mut built);
        out.insert(f.entry, built);
    }
    out
}

/// What the callers say, both from their code and from what the compiler
/// recorded about them.
fn observed(
    p: &Program,
    built: &BTreeMap<Addr, SsaFunction>,
    abi: &Abi,
) -> BTreeMap<Addr, Observed> {
    let mut out: BTreeMap<Addr, Observed> = BTreeMap::new();
    for f in built.values() {
        for (target, seen) in conv::observe(f, abi) {
            out.entry(target).or_default().merge(&seen);
        }
    }
    for (target, recorded) in recorded(p) {
        out.entry(target).or_default().recorded.extend(recorded);
    }
    out
}

/// The compiler's own record: for each callee, the register file offsets it
/// filled at each call site it described.
///
/// A parameter with no register location is a stack slot or an expression this
/// does not model, and it is dropped rather than guessed at: the gate is that
/// what the compiler named in a register is found, not that nothing else
/// exists.
fn recorded(p: &Program) -> BTreeMap<Addr, Vec<Vec<u64>>> {
    census(p).0
}

/// The same, with a count of how much ground truth the file actually carries.
fn census(p: &Program) -> (BTreeMap<Addr, Vec<Vec<u64>>>, usize, usize, usize) {
    let mut out: BTreeMap<Addr, Vec<Vec<u64>>> = BTreeMap::new();
    let mut sites = 0usize;
    let mut with_target = 0usize;
    let mut with_registers = 0usize;
    let Some(d) = p.object.debug.as_ref() else {
        return (out, 0, 0, 0);
    };
    for f in d.functions.values() {
        for c in &f.call_sites {
            sites += 1;
            let Some(target) = c.target else { continue };
            with_target += 1;
            let mut registers = Vec::new();
            for parameter in &c.parameters {
                let Some(DwarfLocation::Register(n)) = parameter.location.as_ref() else {
                    continue;
                };
                if let Some(offset) = dwreg::offset(&p.object.arch, *n) {
                    registers.push(offset);
                }
            }
            if !registers.is_empty() {
                with_registers += 1;
                out.entry(target).or_default().push(registers);
            }
        }
    }
    (out, sites, with_target, with_registers)
}

/// Running totals, so the ratio means something.
#[derive(Default)]
struct Totals {
    described: usize,
    found: usize,
    missed: Vec<String>,
    callees: usize,
    proven: usize,
    /// How much ground truth there is at all: call sites the compiler
    /// described, how many name a callee we can join to, and how many carry a
    /// parameter in a register.
    sites: usize,
    with_target: usize,
    with_registers: usize,
}

fn check(fixture: &str, totals: &mut Totals) {
    let Some(p) = open(fixture) else { return };
    if p.object.debug.is_none() {
        return;
    }
    let abi = abi_of(&p);
    let built = ssa(&p);
    let seen = observed(&p, &built, &abi);

    let (_, sites, with_target, with_registers) = census(&p);
    totals.sites += sites;
    totals.with_target += with_target;
    totals.with_registers += with_registers;

    let mut described = 0usize;
    let mut found = 0usize;
    for (at, f) in &built {
        let Some(o) = seen.get(at) else { continue };
        if o.recorded.is_empty() {
            continue;
        }
        let d = conv::detect_with(f, &abi, o);
        totals.callees += 1;
        if d.strength == Strength::Proven {
            totals.proven += 1;
        }
        let arrives: BTreeSet<u64> = d
            .arguments
            .iter()
            .filter(|a| a.purpose.is_argument())
            .map(|a| a.location.offset)
            .collect();
        for register in o.recorded_registers() {
            described += 1;
            if arrives.contains(&register) {
                found += 1;
            } else {
                let name = p
                    .function(*at)
                    .map(|f| f.display_name())
                    .unwrap_or_else(|| format!("{at}"));
                totals.missed.push(format!(
                    "{fixture}: {name} takes an argument in {register:#x} the compiler recorded \
                     and the reads do not show"
                ));
            }
        }
    }
    if described == 0 {
        return;
    }
    totals.described += described;
    totals.found += found;
    println!("{fixture}: {found} of {described} recorded argument registers found");
}

#[test]
fn detection_agrees_with_what_the_compiler_recorded_about_its_own_calls() {
    let mut totals = Totals::default();
    // Every fixture that carries `DW_TAG_call_site_parameter` at all, which
    // is a small part of the corpus: a producer emits it at -O1 and above and
    // only for calls whose arguments it could describe. Listing the ones with
    // none would not make the gate stronger, it would only make the list
    // longer, so the list is the ones that have it.
    for fixture in [
        "em-paths.a64.O1",
        "em-paths.a64.O2",
        "em-paths.x64.O1",
        "em-paths.x64.O2",
        "wide.a64.O1.o",
        "wide.a64.O2.o",
        "wide.a64.O3.o",
        "wide.a64.Os.o",
        "wide.a64.dwarf4.o",
        "wide.x64.O1.o",
        "wide.x64.O2.o",
        "wide.x64.O3.o",
        "wide.x64.Os.o",
        "wide.x64.sse42.o",
        "shapes.a64.O1.o",
        "shapes.a64.Os.o",
        "shapes.a64.O2.cpp.o",
        "hello.a64.O2",
        "hello.a64.dwarf4",
        "panicky",
        // Carry no call-site information, and are here so a producer that
        // starts emitting it is measured rather than silently skipped.
        "wide.a64.O0.o",
        "wide.x64.O0.o",
        "shapes.a64.O0.o",
        "shapes.x64.O2.o",
        "hello.a64.O0",
        "driver.a64.O2",
        "driver.x64.O2",
    ] {
        check(fixture, &mut totals);
    }
    println!(
        "{} call sites described, {} name a callee in the image, {} carry a register \
         argument",
        totals.sites, totals.with_target, totals.with_registers
    );
    if totals.described == 0 {
        // No fixture carried call-site information, which is a gap in the
        // corpus rather than a failure here.
        return;
    }
    let share = totals.found as f64 / totals.described as f64;
    println!(
        "{} of {} recorded argument registers found ({share:.3}) over {} callees, \
         {} of them proven",
        totals.found, totals.described, totals.callees, totals.proven
    );
    assert!(
        share >= MIN_AGREEMENT,
        "only {} of {} recorded argument registers were found ({share:.3}), floor is \
         {MIN_AGREEMENT}. first 10:\n  {}",
        totals.found,
        totals.described,
        totals
            .missed
            .iter()
            .take(10)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n  ")
    );
}

/// How many functions in the corpus use a convention that is not the
/// platform's, and which.
///
/// A survey. The number is printed rather than gated because it is a property
/// of the corpus, and a corpus of compiled C where most functions departed
/// from the convention would mean the detection is measuring something else.
#[test]
fn the_corpus_survey_says_which_functions_are_not_standard() {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut examples: Vec<String> = Vec::new();
    let mut total = 0usize;
    let mut narrowed = 0usize;

    for fixture in [
        "wide.a64.O0.o",
        "wide.a64.O2.o",
        "wide.x64.O0.o",
        "wide.x64.O2.o",
        "shapes.a64.O2.o",
        "shapes.x64.O2.o",
        "shapes.a64.O2.cpp",
        "hello.a64.O0",
        "driver.a64.O2",
        "driver.x64.O2",
        "cpp-hierarchy.x64.O0.rtti",
        "cpp-hierarchy.a64.O0.rtti",
        "win.x64.O2.exe",
        "win.a64.O2.exe",
        "cpp-hierarchy.win-x64.O0.rtti.exe",
    ] {
        let Some(p) = open(fixture) else { continue };
        let abi = abi_of(&p);
        let built = ssa(&p);
        let seen = observed(&p, &built, &abi);
        for (at, f) in &built {
            let d = conv::detect_with(f, &abi, seen.get(at).unwrap_or(&Observed::default()));
            total += 1;
            *counts.entry(d.convention.as_str()).or_default() += 1;
            if d.convention == Convention::Fewer {
                narrowed += 1;
            }
            if d.convention == Convention::NonStandard && examples.len() < 40 {
                let name = p
                    .function(*at)
                    .map(|f| f.display_name())
                    .unwrap_or_else(|| format!("{at}"));
                examples.push(format!("{fixture}: {name}: {}", d.describe()));
            }
        }
    }
    if total == 0 {
        return;
    }
    println!("{total} functions: {counts:?}");
    println!("{narrowed} took fewer arguments than the fixed order would have given them");
    for e in &examples {
        println!("  {e}");
    }
    // Compiled C keeps the convention. A corpus where most functions did not
    // would mean this is measuring something other than the convention.
    let standard = counts.get("standard").copied().unwrap_or(0)
        + counts.get("standard-fewer-arguments").copied().unwrap_or(0);
    assert!(
        standard * 2 >= total,
        "only {standard} of {total} functions keep the platform convention"
    );
}
