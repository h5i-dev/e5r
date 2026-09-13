//! Dataflow over SSA: constant folding, copy propagation, dead code removal.
//!
//! The point is not speed. Lifting one machine instruction produces several IR
//! operations and most of them are bookkeeping: a flag nothing reads, a
//! temporary that holds a constant, a merge that puts a value back where it
//! already was. Removing them is what turns IR into something a person can
//! read, and it is the difference between a disassembler and the beginning of a
//! decompiler.
//!
//! Every pass runs to a fixed point and every pass is conservative: an
//! operation whose effect is not understood is kept.

use std::collections::{BTreeMap, BTreeSet};

use crate::op::Op;
use crate::ssa::{Operand, SsaFunction, SsaKind, Value};

/// What a pass changed.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Changes {
    /// Operations whose result became a constant.
    pub folded: usize,
    /// Operands replaced with what they were copied from.
    pub propagated: usize,
    /// Operations removed because nothing read them.
    pub removed: usize,
}

impl Changes {
    /// True when nothing changed.
    pub fn is_empty(self) -> bool {
        self == Changes::default()
    }

    fn add(&mut self, other: Changes) {
        self.folded += other.folded;
        self.propagated += other.propagated;
        self.removed += other.removed;
    }
}

/// Run every pass to a fixed point.
pub fn optimize(f: &mut SsaFunction) -> Changes {
    let mut total = Changes::default();
    for _ in 0..32 {
        let mut round = Changes::default();
        round.add(propagate(f));
        round.add(fold(f));
        round.add(remove_dead(f));
        if round.is_empty() {
            break;
        }
        total.add(round);
    }
    total
}

/// Replace an operand with what it was copied from.
///
/// A copy chain is followed to its source, and a phi whose inputs all agree is
/// itself a copy, which is what removes the phis lifting introduces for values
/// that never actually differ between paths.
pub fn propagate(f: &mut SsaFunction) -> Changes {
    let mut source: BTreeMap<Value, Operand> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            let Some(out) = op.out else { continue };
            match &op.kind {
                SsaKind::Op(Op::Copy) if op.inputs.len() == 1 => {
                    // A copy that narrows or widens is not a copy.
                    if operand_size(&op.inputs[0], op.size) == op.size {
                        source.insert(out, op.inputs[0]);
                    }
                }
                // A phi whose inputs are all the same value is that value.
                SsaKind::Phi if !op.inputs.is_empty() => {
                    let first = op.inputs[0];
                    if op.inputs.iter().all(|i| *i == first) && first != Operand::Value(out) {
                        source.insert(out, first);
                    }
                }
                _ => {}
            }
        }
    }
    if source.is_empty() {
        return Changes::default();
    }

    // Follow chains, with a guard: a phi cycle would otherwise loop.
    let resolve = |mut o: Operand| {
        let mut guard = 0;
        while let Operand::Value(v) = o {
            match source.get(&v) {
                Some(next) if *next != o && guard < 64 => {
                    o = *next;
                    guard += 1;
                }
                _ => break,
            }
        }
        o
    };

    let mut changed = Changes::default();
    for b in f.blocks.values_mut() {
        for op in b.ops.iter_mut() {
            for i in op.inputs.iter_mut() {
                let to = resolve(*i);
                if to != *i {
                    *i = to;
                    changed.propagated += 1;
                }
            }
        }
    }
    changed
}

/// Evaluate operations whose inputs are all constants.
pub fn fold(f: &mut SsaFunction) -> Changes {
    let mut changed = Changes::default();
    for b in f.blocks.values_mut() {
        for op in b.ops.iter_mut() {
            let SsaKind::Op(o) = op.kind else { continue };
            if op.out.is_none() || matches!(o, Op::Copy | Op::Load | Op::Store) {
                continue;
            }
            let consts: Option<Vec<u64>> = op.inputs.iter().map(|i| i.as_const()).collect();
            let Some(consts) = consts else { continue };
            if consts.is_empty() {
                continue;
            }
            let Some(value) = evaluate(o, &consts, op.size, &op.inputs) else {
                continue;
            };
            // Rewritten as a copy of the constant rather than deleted, so a
            // later pass sees an ordinary copy and the definition survives.
            op.kind = SsaKind::Op(Op::Copy);
            op.inputs = vec![Operand::Const(value, op.size)];
            changed.folded += 1;
        }
    }
    changed
}

/// The size an operand is read at.
fn operand_size(o: &Operand, default: u8) -> u8 {
    match o {
        Operand::Const(_, s) => *s,
        Operand::Value(v) => v.location.size,
        Operand::Undefined(l) => l.size,
    }
    .max(1)
    .min(default.max(1))
}

/// Evaluate a constant operation, or `None` when the result is not defined.
fn evaluate(op: Op, a: &[u64], size: u8, inputs: &[Operand]) -> Option<u64> {
    let mask = match size {
        0 => return None,
        1..=7 => (1u64 << (size as u32 * 8)) - 1,
        _ => u64::MAX,
    };
    let in_size = |n: usize| match inputs.get(n) {
        Some(Operand::Const(_, s)) => (*s).max(1),
        _ => size.max(1),
    };
    let sext = |v: u64, s: u8| -> i64 {
        if s >= 8 {
            v as i64
        } else {
            let shift = 64 - s as u32 * 8;
            ((v << shift) as i64) >> shift
        }
    };
    let x = *a.first()?;
    let xs = sext(x, in_size(0));
    let y = a.get(1).copied().unwrap_or(0);
    let ys = sext(y, in_size(1));
    let bits = in_size(0) as u64 * 8;

    let out = match op {
        Op::IntAdd => x.wrapping_add(y),
        Op::IntSub => x.wrapping_sub(y),
        Op::IntMul => x.wrapping_mul(y),
        Op::IntDiv | Op::IntRem | Op::IntSDiv | Op::IntSRem if y == 0 => return None,
        Op::IntDiv => x / y,
        Op::IntRem => x % y,
        Op::IntSDiv => xs.wrapping_div(ys) as u64,
        Op::IntSRem => xs.wrapping_rem(ys) as u64,
        Op::IntAnd => x & y,
        Op::IntOr => x | y,
        Op::IntXor => x ^ y,
        Op::IntNot => !x,
        Op::IntNegate => x.wrapping_neg(),
        Op::IntLeft => {
            if y >= bits {
                0
            } else {
                x << y
            }
        }
        Op::IntRight => {
            if y >= bits {
                0
            } else {
                x >> y
            }
        }
        Op::IntSRight => {
            if y >= bits {
                if xs < 0 { u64::MAX } else { 0 }
            } else {
                (xs >> y) as u64
            }
        }
        Op::IntEqual => (x == y) as u64,
        Op::IntNotEqual => (x != y) as u64,
        Op::IntLess => (x < y) as u64,
        Op::IntSLess => (xs < ys) as u64,
        Op::IntLessEqual => (x <= y) as u64,
        Op::IntSLessEqual => (xs <= ys) as u64,
        Op::IntZExt => x,
        Op::IntSExt => xs as u64,
        Op::PopCount => x.count_ones() as u64,
        Op::BoolAnd => ((x != 0) && (y != 0)) as u64,
        Op::BoolOr => ((x != 0) || (y != 0)) as u64,
        Op::BoolXor => ((x != 0) ^ (y != 0)) as u64,
        Op::BoolNot => (x == 0) as u64,
        Op::SubPiece => x >> (y * 8),
        // The carry and overflow operations depend on the operand width in a
        // way the constant folder would have to duplicate; left alone.
        _ => return None,
    };
    Some(out & mask)
}

/// Remove operations nothing reads.
///
/// A store, a branch, a call and anything unmodelled are kept whatever their
/// output: their effect is not the value they produce.
pub fn remove_dead(f: &mut SsaFunction) -> Changes {
    let mut live: BTreeSet<Value> = BTreeSet::new();
    // Seed from the operations that must stay, then close over their inputs.
    let mut work: Vec<Value> = Vec::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if !has_effect(op) {
                continue;
            }
            for i in &op.inputs {
                if let Operand::Value(v) = i {
                    if live.insert(*v) {
                        work.push(*v);
                    }
                }
            }
        }
    }
    let defs: BTreeMap<Value, (r12e_core::Addr, usize)> = f.definitions();
    while let Some(v) = work.pop() {
        let Some((block, index)) = defs.get(&v) else {
            continue;
        };
        let Some(op) = f.blocks.get(block).and_then(|b| b.ops.get(*index)) else {
            continue;
        };
        for i in &op.inputs {
            if let Operand::Value(u) = i {
                if live.insert(*u) {
                    work.push(*u);
                }
            }
        }
    }

    let mut changed = Changes::default();
    for b in f.blocks.values_mut() {
        let before = b.ops.len();
        b.ops.retain(|op| match op.out {
            Some(v) => has_effect(op) || live.contains(&v),
            None => true,
        });
        changed.removed += before - b.ops.len();
    }
    changed
}

/// True when an operation matters for reasons other than its result.
fn has_effect(op: &crate::ssa::SsaOp) -> bool {
    match &op.kind {
        SsaKind::Phi => false,
        SsaKind::Op(o) => matches!(
            o,
            Op::Store
                | Op::Branch
                | Op::CBranch
                | Op::BranchInd
                | Op::Call
                | Op::CallInd
                | Op::Return
                | Op::Unimplemented
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_arithmetic_folds() {
        assert_eq!(evaluate(Op::IntAdd, &[2, 3], 8, &[]), Some(5));
        assert_eq!(evaluate(Op::IntMul, &[6, 7], 8, &[]), Some(42));
    }

    #[test]
    fn folding_respects_the_output_width() {
        // Four bytes, so the carry is dropped rather than kept.
        assert_eq!(evaluate(Op::IntAdd, &[0xffff_ffff, 1], 4, &[]), Some(0));
    }

    #[test]
    fn division_by_zero_does_not_fold() {
        assert_eq!(evaluate(Op::IntDiv, &[1, 0], 8, &[]), None);
        assert_eq!(evaluate(Op::IntSRem, &[1, 0], 8, &[]), None);
    }

    #[test]
    fn signed_operations_use_the_input_width() {
        // A one-byte 0xff is -1, and the shift has to know that.
        let inputs = [Operand::Const(0xff, 1), Operand::Const(1, 1)];
        assert_eq!(evaluate(Op::IntSRight, &[0xff, 1], 1, &inputs), Some(0xff));
    }

    #[test]
    fn the_flag_operations_are_left_alone() {
        // They depend on the operand width in a way the folder would have to
        // duplicate, so it does not guess.
        assert_eq!(evaluate(Op::IntCarry, &[1, 2], 8, &[]), None);
        assert_eq!(evaluate(Op::IntSCarry, &[1, 2], 8, &[]), None);
    }
}
