//! The width an operation works at, kept through the optimizer.
//!
//! A machine comparison is a subtraction and a formula over the flags, and the
//! optimizer puts the comparison back. The number of bits it compares at is
//! carried by nothing but the width of its operands, so a pass that widens one
//! of them changes the answer: 0x80000000 is negative at 32 bits and positive
//! at 64. These check that the width survives.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_core::{Addr, Arch};
use e5r_format::LoadOptions;
use e5r_ir::op::{Op, Space};
use e5r_ir::opt;
use e5r_ir::ssa::{self, Location, Operand, SsaBlock, SsaFunction, SsaKind, SsaOp, Value};
use e5r_ir::{func, stack};

/// The comparisons whose operand widths are the width being compared.
const COMPARISONS: [Op; 6] = [
    Op::IntEqual,
    Op::IntNotEqual,
    Op::IntLess,
    Op::IntLessEqual,
    Op::IntSLess,
    Op::IntSLessEqual,
];

fn value(space: Space, offset: u64, size: u8, version: u32) -> Value {
    Value {
        location: Location {
            space,
            offset,
            size,
        },
        version,
    }
}

fn op(o: Op, out: Option<Value>, inputs: Vec<Operand>, size: u8) -> SsaOp {
    SsaOp {
        addr: Addr(0x1000),
        kind: SsaKind::Op(o),
        out,
        inputs,
        size,
    }
}

/// One block holding what a 32-bit `subs` and a signed branch lift to.
///
/// Each operand is read out of a 64-bit register, written back into one, and
/// read out again, which is the shape a compiler that spills produces and the
/// shape that used to lose the width.
fn thirty_two_bit_signed_compare() -> SsaFunction {
    let mut ops = Vec::new();
    let mut narrow = Vec::new();
    for (n, reg) in [0u64, 8].into_iter().enumerate() {
        let n = n as u32;
        let read = value(Space::Unique, 0x100 + reg, 4, n);
        let widened = value(Space::Register, reg, 8, n);
        let again = value(Space::Unique, 0x200 + reg, 4, n);
        ops.push(op(
            Op::SubPiece,
            Some(read),
            vec![
                Operand::Undefined(Location {
                    space: Space::Register,
                    offset: reg,
                    size: 8,
                }),
                Operand::Const(0, 1),
            ],
            4,
        ));
        ops.push(op(
            Op::IntZExt,
            Some(widened),
            vec![Operand::Value(read)],
            8,
        ));
        ops.push(op(
            Op::SubPiece,
            Some(again),
            vec![Operand::Value(widened), Operand::Const(0, 1)],
            4,
        ));
        narrow.push(Operand::Value(again));
    }
    let (x, y) = (narrow[0], narrow[1]);

    let difference = value(Space::Unique, 0x300, 4, 0);
    let sign = value(Space::Unique, 0x304, 4, 0);
    let negative = value(Space::Register, 0x400, 1, 0);
    let overflow = value(Space::Register, 0x401, 1, 0);
    let less = value(Space::Register, 0x402, 1, 0);
    ops.push(op(Op::IntSub, Some(difference), vec![x, y], 4));
    ops.push(op(
        Op::IntRight,
        Some(sign),
        vec![Operand::Value(difference), Operand::Const(31, 1)],
        4,
    ));
    ops.push(op(
        Op::IntNotEqual,
        Some(negative),
        vec![Operand::Value(sign), Operand::Const(0, 4)],
        1,
    ));
    ops.push(op(Op::IntSBorrow, Some(overflow), vec![x, y], 1));
    ops.push(op(
        Op::IntNotEqual,
        Some(less),
        vec![Operand::Value(negative), Operand::Value(overflow)],
        1,
    ));
    // A branch, so the comparison is not dead and survives to be inspected.
    ops.push(op(
        Op::CBranch,
        None,
        vec![Operand::Const(0x2000, 8), Operand::Value(less)],
        8,
    ));

    SsaFunction {
        arch: Arch::AArch64,
        entry: Addr(0x1000),
        blocks: BTreeMap::from([(
            Addr(0x1000),
            SsaBlock {
                ops,
                successors: Vec::new(),
                predecessors: Vec::new(),
            },
        )]),
    }
}

#[test]
fn a_signed_comparison_keeps_the_width_it_was_made_at() {
    let mut f = thirty_two_bit_signed_compare();
    opt::optimize(&mut f);
    let comparisons: Vec<&SsaOp> = f
        .blocks
        .values()
        .flat_map(|b| b.ops.iter())
        .filter(|o| o.kind == SsaKind::Op(Op::IntSLess))
        .collect();
    assert_eq!(
        comparisons.len(),
        1,
        "the flag algebra should fold to one signed comparison, got {}",
        f.blocks
            .values()
            .flat_map(|b| b.ops.iter())
            .map(|o| format!("{:?}", o.kind))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let sizes: Vec<u8> = comparisons[0].inputs.iter().map(|i| i.size()).collect();
    assert_eq!(
        sizes,
        vec![4, 4],
        "a 32-bit signed comparison compares 32 bits in both operands"
    );
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    if obj.arch != Arch::AArch64 {
        return None;
    }
    Some(analyze(obj, &Options::default()))
}

fn optimized(p: &Program, name: &str) -> Option<SsaFunction> {
    let f = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some(name))?;
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    stack::promote(&mut ir);
    let mut s = ssa::build(&ir);
    opt::optimize(&mut s);
    Some(s)
}

/// Both operands of a comparison, in the functions whose machine code compares
/// at 32 bits throughout.
#[test]
fn the_fixtures_compare_at_the_width_the_machine_did() {
    let Some(p) = open("driver.a64.O0") else {
        return;
    };
    for name in ["select_chain", "sarith32"] {
        let Some(f) = optimized(&p, name) else {
            continue;
        };
        let widths: BTreeSet<Vec<u8>> = f
            .blocks
            .values()
            .flat_map(|b| b.ops.iter())
            .filter(|o| matches!(&o.kind, SsaKind::Op(o) if COMPARISONS.contains(o)))
            .map(|o| o.inputs.iter().map(|i| i.size()).collect())
            .collect();
        assert!(
            widths.iter().all(|w| w == &vec![4u8, 4]),
            "{name} compares 32-bit values; the operand widths are {widths:?}"
        );
    }
}

/// Nothing in the corpus compares two operands of different widths, whatever
/// the width is: the machine had one pair of registers and one width.
#[test]
fn no_comparison_mixes_two_widths() {
    let mut bad: Vec<String> = Vec::new();
    for name in ["driver.a64.O0", "driver.a64.O1", "driver.a64.O2"] {
        let Some(p) = open(name) else { continue };
        for f in p.functions_by_address().filter(|f| f.is_complete()) {
            let Some(symbol) = f.name.clone() else {
                continue;
            };
            let Some(s) = optimized(&p, &symbol) else {
                continue;
            };
            for o in s.blocks.values().flat_map(|b| b.ops.iter()) {
                let SsaKind::Op(k) = o.kind else { continue };
                if !COMPARISONS.contains(&k) || o.inputs.len() != 2 {
                    continue;
                }
                if o.inputs[0].size() != o.inputs[1].size() {
                    bad.push(format!(
                        "{name} {symbol} {:?} at {:?}: {} vs {}",
                        k,
                        o.addr,
                        o.inputs[0].size(),
                        o.inputs[1].size()
                    ));
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "{} comparison(s) read a different number of bits from each operand:\n{}",
        bad.len(),
        bad.iter().take(20).cloned().collect::<Vec<_>>().join("\n")
    );
}
