//! Prototypes across a whole program, where the callers get a say.
//!
//! A function on its own cannot always say whether it returns anything. One
//! whose last act computes an address into the first argument register has
//! left a value there, and nothing inside it says whether that was the point.
//! The callers know: if every one of them ignores what came back, it was not a
//! result.
//!
//! This is the roadmap's feedback edge in its simplest useful form. It runs
//! once over the call graph rather than to a fixed point, because the one fact
//! it propagates cannot change what any caller does with its own result.

use std::collections::{BTreeMap, BTreeSet};

use r12e_analysis::Program;
use r12e_core::Addr;
use r12e_ir::proto::Prototype;
use r12e_ir::ssa::{SsaFunction, SsaKind};

/// A recovered prototype and how it was settled.
#[derive(Debug, Clone)]
pub struct Recovered {
    /// What the function itself says.
    pub prototype: Prototype,
    /// How many calls to it were found.
    pub callers: usize,
    /// True when at least one caller reads what it left in the result
    /// register.
    pub result_used: bool,
}

/// Recover every function's prototype, then let the callers settle the
/// returns.
pub fn prototypes(p: &Program) -> BTreeMap<Addr, Recovered> {
    let abi = r12e_ir::abi::of(&p.object.arch);
    let mut out: BTreeMap<Addr, Recovered> = BTreeMap::new();
    let mut ssa: BTreeMap<Addr, SsaFunction> = BTreeMap::new();

    for f in p.functions_by_address() {
        let Some(built) = build(p, f) else { continue };
        let prototype = r12e_ir::proto::recover(&built, &abi);
        out.insert(
            f.entry,
            Recovered {
                prototype,
                callers: 0,
                result_used: false,
            },
        );
        ssa.insert(f.entry, built);
    }

    // Who calls whom, and whether the caller reads what came back. The call
    // defines the result register, so "reads what came back" is exactly
    // "something uses the value that call defined".
    for function in ssa.values() {
        let consumed = consumed(function, &abi);
        for b in function.blocks.values() {
            for op in &b.ops {
                if op.kind != SsaKind::Op(r12e_ir::op::Op::Call) {
                    continue;
                }
                let Some(target) = op.inputs.first().and_then(|i| i.as_const()) else {
                    continue;
                };
                let Some(entry) = out.get_mut(&Addr(target)) else {
                    continue;
                };
                entry.callers += 1;
                if let Some(result) = op.out {
                    if consumed.contains(&result) {
                        entry.result_used = true;
                    }
                }
            }
        }
    }

    // A function every caller ignores did not return anything, whatever it
    // left lying in the register. One with no callers keeps its own answer:
    // absence of evidence is not evidence.
    for recovered in out.values_mut() {
        if recovered.callers > 0 && !recovered.result_used {
            recovered.prototype.returns = None;
            recovered.prototype.returns_float = false;
        }
    }
    out
}

/// Every value this function does something with.
///
/// Reading it as an operand is the obvious way, but not the only one: a value
/// left in an argument register before a call is passed to that call, and one
/// left in the result register at a return is handed back. Neither appears as
/// an operand of anything, because the registers are the convention rather
/// than the instruction.
fn consumed(f: &SsaFunction, abi: &r12e_ir::abi::Abi) -> BTreeSet<r12e_ir::ssa::Value> {
    use r12e_ir::op::{Op, Space};

    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Some(v) = i.as_value() {
                    out.insert(v);
                }
            }
        }
    }

    let argument: BTreeSet<u64> = abi
        .integer_arguments
        .iter()
        .chain(abi.float_arguments.iter())
        .copied()
        .collect();
    let result: BTreeSet<u64> = abi.results.iter().copied().collect();

    for b in f.blocks.values() {
        // What each register holds as the block is walked, so the value a call
        // or a return finds there is the one that was passed or handed back.
        let mut latest: BTreeMap<u64, r12e_ir::ssa::Value> = BTreeMap::new();
        for op in &b.ops {
            match op.kind {
                SsaKind::Op(Op::Call) | SsaKind::Op(Op::CallInd) => {
                    for offset in &argument {
                        if let Some(v) = latest.get(offset) {
                            out.insert(*v);
                        }
                    }
                }
                SsaKind::Op(Op::Return) => {
                    for offset in &result {
                        if let Some(v) = latest.get(offset) {
                            out.insert(*v);
                        }
                    }
                }
                _ => {}
            }
            if let Some(v) = op.out {
                if v.location.space == Space::Register {
                    latest.insert(v.location.offset, v);
                }
            }
        }
    }
    out
}

/// One function in SSA form, optimized.
fn build(p: &Program, f: &r12e_analysis::Function) -> Option<SsaFunction> {
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    if blocks.is_empty() {
        return None;
    }
    let mut ir = r12e_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    r12e_ir::stack::promote(&mut ir);
    let mut ssa = r12e_ir::ssa::build(&ir);
    r12e_ir::opt::optimize(&mut ssa);
    Some(ssa)
}

/// The functions that call a given one, for a caller that wants the graph
/// rather than the prototypes.
pub fn callers_of(p: &Program, target: Addr) -> BTreeSet<Addr> {
    p.xrefs
        .to(target)
        .iter()
        .filter(|x| x.kind == r12e_analysis::XrefKind::Call)
        .filter_map(|x| p.function(x.from).map(|f| f.entry))
        .collect()
}
