//! Range analysis, checked against what the code actually produces.
//!
//! An interval is sound when it contains every value the computation can
//! produce. That cannot be proved by reading it, but it can be falsified by
//! running the code: take the case table the lifter's oracle uses, run each
//! call in the interpreter, and require the analysis to have said the value
//! that came back was possible. A range that excludes something that happened
//! is a bug with no allowance.
//!
//! The comparison is against the bits the result register held, not against
//! the number C would have made of them: the interval describes a register.
//!
//! The test also reports how often the analysis knows anything at all, because
//! an analysis that answers "any value" to everything is sound and useless.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::Addr;
use r12e_format::LoadOptions;
use r12e_ir::range::Range;
use r12e_ir::ssa::{SsaFunction, SsaKind};

/// Floor on the share of returned values the analysis can say anything about.
/// Only raised.
const MIN_BOUNDED: f64 = 0.20;

fn build() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

struct Case {
    name: String,
    args: Vec<u64>,
}

/// The cases whose arguments are plain numbers, with the answer the processor
/// gave.
fn cases() -> Vec<Case> {
    let Some(dir) = build() else { return Vec::new() };
    let table = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/portable/cases.txt");
    let _ = dir;
    let Ok(text) = std::fs::read_to_string(table) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for line in text
        .lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
    {
        let mut parts = line.split_whitespace();
        let head = parts.next().unwrap_or_default();
        let (name, kind) = head.split_once(':').unwrap_or((head, "u64"));
        if kind.starts_with('f') || line.contains('.') {
            continue;
        }
        let mut args = Vec::new();
        let mut usable = true;
        for token in parts {
            match number(token) {
                Some(v) => args.push(v),
                None => usable = false,
            }
        }
        if usable {
            out.push(Case {
                name: name.to_string(),
                args,
            });
        }
    }
    out
}

fn number(token: &str) -> Option<u64> {
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

fn ssa_of(p: &Program, f: &r12e_analysis::Function) -> Option<SsaFunction> {
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
    Some(ssa)
}

/// What the analysis says about the value a function leaves behind.
///
/// The join over every path out: a function with a switch in it returns from
/// several places, and what it can produce is what any of them can. Taking one
/// of them would be comparing a run that went one way against a bound computed
/// for another.
fn returned(
    ssa: &SsaFunction,
    abi: &r12e_ir::abi::Abi,
    ranges: &BTreeMap<r12e_ir::ssa::Value, Range>,
) -> Option<Range> {
    let mut out: Option<Range> = None;
    for b in ssa.blocks.values() {
        if !b
            .ops
            .iter()
            .any(|op| op.kind == SsaKind::Op(r12e_ir::op::Op::Return))
        {
            continue;
        }
        // The last write to a result register in this block is what it leaves.
        let last = b
            .ops
            .iter()
            .rev()
            .filter_map(|op| op.out)
            .find(|v| {
                v.location.space == r12e_ir::op::Space::Register
                    && abi.results.contains(&v.location.offset)
            });
        let Some(range) = last.and_then(|v| ranges.get(&v)) else {
            // A path whose value is unknown makes the whole answer unknown.
            return Some(Range::ANY);
        };
        out = Some(match out {
            Some(existing) => existing.join(*range),
            None => *range,
        });
    }
    out
}

#[test]
fn every_range_contains_what_the_processor_produced() {
    let cases = cases();
    if cases.is_empty() {
        return;
    }

    let mut checked = 0;
    let mut bounded = 0;
    let mut wrong = Vec::new();

    for fixture in ["wide.a64.O0.o", "wide.a64.O2.o", "wide.x64.O0.o"] {
        let Some(p) = open(fixture) else { continue };
        let abi = r12e_ir::abi::of(&p.object.arch);
        for case in &cases {
            let Some(f) = p
                .functions_by_address()
                .find(|f| f.name.as_deref() == Some(case.name.as_str()))
            else {
                continue;
            };
            let Some(ssa) = ssa_of(&p, f) else { continue };
            let ranges = r12e_ir::range::ranges(&ssa);
            let Some(range) = returned(&ssa, &abi, &ranges) else {
                continue;
            };
            // Run it, and compare against what the register actually held.
            let setup = r12e_api::Setup {
                arguments: case.args.clone(),
                depth: 4096,
                ..Default::default()
            };
            let outcome = r12e_api::emulate::run(&p, f, &setup);
            if outcome.stop != r12e_ir::Stop::Returned {
                continue;
            }
            checked += 1;
            if !range.is_any() {
                bounded += 1;
            }
            let produced = outcome.result as i64;
            if !range.contains(produced) && !range.is_any() {
                wrong.push(format!(
                    "{fixture}: {}{:?} produced {produced}, the range said {}..={}",
                    case.name, case.args, range.low, range.high
                ));
            }
        }
    }

    assert!(
        wrong.is_empty(),
        "{} range(s) exclude a value the processor produced:\n  {}",
        wrong.len(),
        wrong.join("\n  ")
    );
    if checked == 0 {
        return;
    }
    let share = bounded as f64 / checked as f64;
    assert!(
        share >= MIN_BOUNDED,
        "only {bounded} of {checked} results were bounded at all ({share:.2}), \
         floor is {MIN_BOUNDED}"
    );
    println!("{checked} results checked, {bounded} bounded ({share:.2})");
}

#[test]
fn a_masked_value_is_bounded_by_its_mask() {
    let Some(p) = open("wide.a64.O2.o") else { return };
    // `indexed` reads `table[i & 63] + table[(i >> 6) & 63]`, so the masks
    // bound the indices whatever the argument is.
    let Some(f) = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some("indexed"))
    else {
        return;
    };
    let Some(ssa) = ssa_of(&p, f) else { return };
    let ranges = r12e_ir::range::ranges(&ssa);
    let bounded = ranges
        .values()
        .filter(|r| !r.is_any() && r.width() <= 63)
        .count();
    assert!(
        bounded > 0,
        "nothing in a function full of masks came out bounded"
    );
}
