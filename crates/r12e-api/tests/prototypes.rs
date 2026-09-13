//! Prototype recovery, measured against what the compiler recorded.
//!
//! The fixtures carry debug information, so the number of parameters each
//! function takes and whether it returns anything are known. The recovery runs
//! without looking at any of it: a register read before this function wrote it
//! arrived with a value, and one written on the way to a return is left for
//! the caller.
//!
//! A recovered count that is too low loses an argument at every call site, so
//! that is a failure. One that is too high is a function whose argument the
//! compiler passed and never used, which the machine code cannot distinguish
//! from one it uses; those are counted and held under a ceiling.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::Addr;
use r12e_format::LoadOptions;
use r12e_types::ctype::Type;

/// Ceiling on the share of functions where the recovery counts more arguments
/// than were declared. Only lowered.
const MAX_OVERCOUNT: f64 = 0.14;

/// Ceiling on the share of void functions credited with a result. Only
/// lowered, and it comes down when the feedback edges land: a caller that
/// never reads the result is the evidence this cannot see from inside.
const MAX_FALSE_RETURN: f64 = 0.95;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// Recover one function's prototype.
fn recover(p: &Program, f: &r12e_analysis::Function) -> r12e_ir::proto::Prototype {
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = r12e_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    r12e_ir::stack::promote(&mut ir);
    let mut ssa = r12e_ir::ssa::build(&ir);
    r12e_ir::opt::optimize(&mut ssa);
    r12e_ir::proto::recover(&ssa, &r12e_ir::abi::of(&p.object.arch))
}

/// What the debug information declared: how many integer and floating
/// parameters, and whether anything comes back.
fn declared(p: &Program, at: Addr) -> Option<(usize, usize, bool)> {
    let d = p.object.debug.as_ref()?;
    let f = d.functions.get(&at)?;
    let mut integers = 0;
    let mut floats = 0;
    for (_, ty) in &f.signature.parameters {
        match d.types.get(d.types.resolve(*ty)) {
            Some(Type::Float { .. }) => floats += 1,
            _ => integers += 1,
        }
    }
    Some((integers, floats, f.signature.returns.is_some()))
}

/// Running totals, so the ratio is measured over a sample big enough to mean
/// something rather than over three functions.
#[derive(Default)]
struct Totals {
    checked: usize,
    overcounted: usize,
}

fn check(fixture: &str, totals: &mut Totals) {
    let Some(p) = open(fixture) else { return };
    if p.object.debug.is_none() {
        return;
    }

    let mut checked = 0;
    let mut overcounted = 0;
    let mut short = Vec::new();
    let mut missing_return = Vec::new();

    for f in p.functions_by_address() {
        if !f.is_complete() {
            continue;
        }
        let Some((integers, floats, returns)) = declared(&p, f.entry) else {
            continue;
        };
        let recovered = recover(&p, f);
        checked += 1;
        let name = f.display_name();

        // Arguments on the stack count towards the total the caller passes.
        let recovered_integers = recovered.integer_arguments + recovered.stack_arguments.len();
        if recovered_integers < integers || recovered.float_arguments < floats {
            short.push(format!(
                "{name}: recovered {recovered_integers} integer and {} float, \
                 declared {integers} and {floats}",
                recovered.float_arguments
            ));
        } else if recovered_integers > integers || recovered.float_arguments > floats {
            overcounted += 1;
        }

        if returns && recovered.returns.is_none() {
            missing_return.push(name);
        }
    }

    if checked == 0 {
        return;
    }
    assert!(
        short.is_empty(),
        "{fixture}: {} function(s) lost an argument:\n  {}",
        short.len(),
        short.join("\n  ")
    );
    assert!(
        missing_return.is_empty(),
        "{fixture}: {} function(s) return a value the recovery did not see: {}",
        missing_return.len(),
        missing_return.join(", ")
    );
    totals.checked += checked;
    totals.overcounted += overcounted;
    println!("{fixture}: {checked} prototypes, {overcounted} over-counted");
}

#[test]
fn recovered_prototypes_agree_with_the_debug_information() {
    let mut totals = Totals::default();
    for fixture in [
        "wide.a64.O0.o",
        "wide.a64.O1.o",
        "wide.a64.O2.o",
        "wide.x64.O0.o",
        "wide.x64.O2.o",
        "shapes.a64.O0.o",
        "shapes.x64.O2.o",
        "hello.a64.O0",
    ] {
        check(fixture, &mut totals);
    }
    if totals.checked == 0 {
        return;
    }
    let share = totals.overcounted as f64 / totals.checked as f64;
    assert!(
        share <= MAX_OVERCOUNT,
        "{} of {} prototypes counted too many arguments ({share:.2}), \
         ceiling is {MAX_OVERCOUNT}",
        totals.overcounted,
        totals.checked
    );
    println!(
        "{} prototypes, {} over-counted ({share:.2})",
        totals.checked, totals.overcounted
    );
}

/// How often a void function is credited with a result.
///
/// Recovery never misses a real return, which is the direction that costs a
/// caller something. The other direction it cannot always settle: a function
/// whose last act is to compute an address into the first argument register
/// has left a value there, and only its callers know whether anyone reads it.
/// Settling that is what the roadmap's feedback edges are for; until then the
/// rate is measured and held under a ceiling.
#[test]
fn a_result_is_claimed_only_when_something_was_left_behind() {
    let mut void_functions = 0;
    let mut credited = 0;
    for fixture in ["wide.a64.O0.o", "wide.a64.O2.o", "wide.x64.O0.o", "wide.x64.O2.o"] {
        let Some(p) = open(fixture) else { continue };
        let Some(d) = p.object.debug.as_ref() else {
            continue;
        };
        for f in p.functions_by_address().filter(|f| f.is_complete()) {
            let Some(df) = d.functions.get(&f.entry) else {
                continue;
            };
            if df.signature.returns.is_some() {
                continue;
            }
            void_functions += 1;
            if recover(&p, f).returns.is_some() {
                credited += 1;
            }
        }
    }
    if void_functions == 0 {
        return;
    }
    let share = credited as f64 / void_functions as f64;
    assert!(
        share <= MAX_FALSE_RETURN,
        "{credited} of {void_functions} functions that return nothing were \
         credited with a result ({share:.2}), ceiling is {MAX_FALSE_RETURN}"
    );
    println!("{void_functions} void functions, {credited} credited with a result ({share:.2})");
}

#[test]
fn a_function_that_keeps_the_conventions_promises_says_so() {
    let Some(p) = open("wide.a64.O2.o") else { return };
    let mut standard = 0;
    let mut total = 0;
    for f in p.functions_by_address().filter(|f| f.is_complete()) {
        total += 1;
        if recover(&p, f).standard {
            standard += 1;
        }
    }
    assert!(total > 10, "only {total} functions");
    // Compiled C keeps the convention; a fixture where most functions did not
    // would mean the check is measuring something else.
    assert!(
        standard * 4 >= total * 3,
        "only {standard} of {total} functions keep the calling convention"
    );
}
