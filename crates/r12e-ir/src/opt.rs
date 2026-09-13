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

use crate::op::{Op, Space};
use crate::ssa::{Location, Operand, SsaFunction, SsaKind, Value};

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
        round.add(simplify(f));
        round.add(cse(f));
        round.add(patterns(f));
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
/// The value a location holds at the end of a block, whether it was written
/// there or arrived from a predecessor.
fn last_definition(
    f: &SsaFunction,
    b: &crate::ssa::SsaBlock,
    location: Location,
    before: usize,
) -> Option<Value> {
    if let Some(v) = b.ops[..before.min(b.ops.len())]
        .iter()
        .rev()
        .filter_map(|op| op.out)
        .find(|v| v.location == location)
    {
        return Some(v);
    }
    // Nothing in this block wrote it, so whatever the rest of the function
    // last put there is what the caller sees.
    f.blocks
        .values()
        .flat_map(|other| other.ops.iter())
        .filter_map(|op| op.out)
        .filter(|v| v.location == location)
        .max_by_key(|v| v.version)
}

/// Remove operations nothing reads and nothing observes.
pub fn remove_dead(f: &mut SsaFunction) -> Changes {
    let mut live: BTreeSet<Value> = BTreeSet::new();
    // Seed from the operations that must stay, then close over their inputs.
    let mut work: Vec<Value> = Vec::new();

    // The caller reads the result and expects the saved registers back, so the
    // last value in each of those at a return is live even though nothing in
    // this function reads it. Without this the result is dead by construction
    // and every function optimizes down to its side effects.
    let abi = crate::abi::of(&f.arch);
    let live_out = abi.live_at_return();
    for b in f.blocks.values() {
        let returns = b
            .ops
            .iter()
            .any(|op| op.kind == SsaKind::Op(crate::op::Op::Return));
        if !returns {
            continue;
        }
        for location in &live_out {
            if let Some(v) = last_definition(f, b, *location, b.ops.len()) {
                if live.insert(v) {
                    work.push(v);
                }
            }
        }
    }

    // A call reads its arguments out of registers the IR does not name as its
    // inputs, so without this every instruction that sets one up looks dead.
    // Deleting them does not just lose readability: it loses the argument.
    let argument_locations: Vec<Location> = abi
        .integer_arguments
        .iter()
        .chain(abi.float_arguments.iter())
        .map(|offset| Location {
            space: Space::Register,
            offset: *offset,
            size: 8,
        })
        .collect();
    for b in f.blocks.values() {
        for (n, op) in b.ops.iter().enumerate() {
            if !matches!(
                op.kind,
                SsaKind::Op(crate::op::Op::Call) | SsaKind::Op(crate::op::Op::CallInd)
            ) {
                continue;
            }
            for location in &argument_locations {
                if let Some(v) = last_definition(f, b, *location, n) {
                    if live.insert(v) {
                        work.push(v);
                    }
                }
            }
        }
    }

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

/// Bits a value can have set, as a mask.
///
/// Cheap and surprisingly load-bearing: a 32-bit write to a 64-bit register is
/// a merge of two halves, and knowing that one half is provably zero is what
/// collapses the merge back into the value that was written. Without it every
/// sub-register operation carries its own bookkeeping into the output.
#[derive(Debug, Default)]
pub struct KnownBits {
    masks: BTreeMap<Value, u64>,
}

impl KnownBits {
    /// Compute for every value in a function.
    pub fn of(f: &SsaFunction) -> KnownBits {
        let defs = f.definitions();
        let mut masks: BTreeMap<Value, u64> = BTreeMap::new();
        // Iterate: a phi's mask depends on its inputs, which may be defined
        // later. The masks only ever grow, so this settles.
        for _ in 0..8 {
            let mut changed = false;
            for b in f.blocks.values() {
                for op in &b.ops {
                    let Some(out) = op.out else { continue };
                    let m = mask_of_op(f, &defs, &masks, op);
                    let width = width_mask(out.location.size);
                    let m = m & width;
                    if masks.get(&out).copied() != Some(m) {
                        masks.insert(out, m);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        KnownBits { masks }
    }

    /// The mask of one operand.
    pub fn operand(&self, o: &Operand) -> u64 {
        match o {
            Operand::Const(v, size) => *v & width_mask(*size),
            Operand::Value(v) => self
                .masks
                .get(v)
                .copied()
                .unwrap_or_else(|| width_mask(v.location.size)),
            Operand::Undefined(l) => width_mask(l.size),
        }
    }
}

fn width_mask(size: u8) -> u64 {
    if size >= 8 || size == 0 {
        u64::MAX
    } else {
        (1u64 << (size as u64 * 8)) - 1
    }
}

fn mask_of_op(
    f: &SsaFunction,
    defs: &BTreeMap<Value, (r12e_core::Addr, usize)>,
    masks: &BTreeMap<Value, u64>,
    op: &crate::ssa::SsaOp,
) -> u64 {
    let get = |o: &Operand| -> u64 {
        match o {
            Operand::Const(v, size) => *v & width_mask(*size),
            Operand::Value(v) => masks
                .get(v)
                .copied()
                .unwrap_or_else(|| width_mask(v.location.size)),
            Operand::Undefined(l) => width_mask(l.size),
        }
    };
    let _ = (f, defs);
    let a = op.inputs.first().map(&get).unwrap_or(u64::MAX);
    let b = op.inputs.get(1).map(&get).unwrap_or(u64::MAX);
    match op.kind {
        SsaKind::Phi => op.inputs.iter().map(&get).fold(0, |acc, m| acc | m),
        SsaKind::Op(o) => match o {
            Op::Copy => a,
            Op::IntAnd => a & b,
            Op::IntOr | Op::IntXor => a | b,
            Op::IntZExt => a,
            Op::SubPiece => width_mask(op.size),
            Op::Load => width_mask(op.size),
            Op::IntLeft => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(n) if n < 64 => a << n,
                _ => u64::MAX,
            },
            Op::IntRight => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(n) if n < 64 => a >> n,
                _ => u64::MAX,
            },
            // A comparison or a flag is one bit.
            Op::IntEqual
            | Op::IntNotEqual
            | Op::IntLess
            | Op::IntLessEqual
            | Op::IntSLess
            | Op::IntSLessEqual
            | Op::IntCarry
            | Op::IntSCarry
            | Op::IntSBorrow
            | Op::BoolAnd
            | Op::BoolOr
            | Op::BoolXor
            | Op::BoolNot
            | Op::FloatEqual
            | Op::FloatNotEqual
            | Op::FloatLess
            | Op::FloatLessEqual
            | Op::FloatNan => 1,
            Op::PopCount | Op::LzCount => 0x7f,
            _ => u64::MAX,
        },
    }
}

/// Rewrite operations whose result is already available in one of their inputs.
///
/// The rules are the identities that machine code produces by construction:
/// masking bits that are already zero, merging a half that is provably empty,
/// exclusive-oring a value with itself.
pub fn simplify(f: &mut SsaFunction) -> Changes {
    let known = KnownBits::of(f);
    // A snapshot of what each value is computed by, so a rule can look one
    // step back without borrowing the function while it is being rewritten.
    let mut source: BTreeMap<Value, (Op, Vec<Operand>)> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let (Some(out), SsaKind::Op(o)) = (op.out, op.kind.clone()) {
                source.insert(out, (o, op.inputs.clone()));
            }
        }
    }
    let mut changes = Changes::default();
    for b in f.blocks.values_mut() {
        for op in &mut b.ops {
            let SsaKind::Op(o) = op.kind else { continue };
            let (a, c) = (op.inputs.first().cloned(), op.inputs.get(1).cloned());
            let (Some(a), Some(c)) = (a, c) else { continue };
            let (ma, mc) = (known.operand(&a), known.operand(&c));
            let same = match (&a, &c) {
                (Operand::Value(x), Operand::Value(y)) => x == y,
                (Operand::Undefined(x), Operand::Undefined(y)) => x == y,
                _ => false,
            };
            let width = width_mask(op.size);

            let replacement: Option<Operand> = match o {
                // Masking off bits that were never set.
                Op::IntAnd => {
                    if let Some(k) = c.as_const() {
                        if ma & width & !k == 0 {
                            Some(a)
                        } else if ma & k == 0 {
                            Some(Operand::Const(0, op.size))
                        } else {
                            None
                        }
                    } else if same {
                        Some(a)
                    } else {
                        None
                    }
                }
                // Merging with a half that is empty.
                Op::IntOr => {
                    if mc == 0 {
                        Some(a)
                    } else if ma == 0 {
                        Some(c)
                    } else if same {
                        Some(a)
                    } else {
                        None
                    }
                }
                Op::IntXor => {
                    if same {
                        Some(Operand::Const(0, op.size))
                    } else if mc == 0 {
                        Some(a)
                    } else if ma == 0 {
                        Some(c)
                    } else {
                        None
                    }
                }
                Op::IntAdd | Op::IntSub if c.as_const() == Some(0) => Some(a),
                Op::IntSub if same => Some(Operand::Const(0, op.size)),
                Op::IntMul if c.as_const() == Some(1) => Some(a),
                Op::IntMul if c.as_const() == Some(0) => Some(Operand::Const(0, op.size)),
                Op::IntLeft | Op::IntRight | Op::IntSRight if c.as_const() == Some(0) => Some(a),
                // Widening something already that wide.
                Op::IntZExt if ma & width == ma && a.size() == op.size => Some(a),
                // Taking the low bytes of a value that has no others.
                Op::SubPiece if c.as_const() == Some(0) && ma & !width_mask(op.size) == 0 => {
                    Some(a)
                }
                _ => None,
            };

            if let Some(r) = replacement {
                op.kind = SsaKind::Op(Op::Copy);
                op.inputs = vec![r];
                changes.folded += 1;
                continue;
            }

            // Masking one half of a merge away, which is what reading a
            // sub-register through a whole-register merge amounts to. Handled
            // separately because it rewrites the operands rather than
            // replacing the operation.
            if o == Op::IntAnd {
                if let (Some(k), Operand::Value(v)) = (c.as_const(), &a) {
                    if let Some((Op::IntOr, parts)) = source.get(v) {
                        let (p, q) = (parts.first().cloned(), parts.get(1).cloned());
                        if let (Some(p), Some(q)) = (p, q) {
                            let keep = if known.operand(&p) & k == 0 {
                                Some(q)
                            } else if known.operand(&q) & k == 0 {
                                Some(p)
                            } else {
                                None
                            };
                            if let Some(keep) = keep {
                                op.inputs = vec![keep, c];
                                changes.folded += 1;
                                continue;
                            }
                        }
                    }
                }
            }
        }
    }
    changes
}

/// Rewrite flag algebra back into the comparison it stands for.
///
/// A machine has no `<`; it has a subtraction and four flags, and a condition
/// is a formula over them. Left alone that formula is what the decompiler
/// prints, and `(a - b) >> 63 != 0 == borrow(a, b)` is not what anyone wrote.
/// These rules recognize the formulas the architectures actually emit and put
/// the comparison back.
pub fn patterns(f: &mut SsaFunction) -> Changes {
    let mut source: BTreeMap<Value, (Op, Vec<Operand>)> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let (Some(out), SsaKind::Op(o)) = (op.out, op.kind.clone()) {
                source.insert(out, (o, op.inputs.clone()));
            }
        }
    }

    let mut changes = Changes::default();
    for b in f.blocks.values_mut() {
        for op in &mut b.ops {
            let SsaKind::Op(o) = op.kind else { continue };
            let (Some(a), Some(c)) = (op.inputs.first().cloned(), op.inputs.get(1).cloned()) else {
                continue;
            };

            // A comparison against a subtraction is a comparison of its
            // operands, which is what the subtraction was for.
            if matches!(o, Op::IntEqual | Op::IntNotEqual) && c.as_const() == Some(0) {
                if let Some((x, y)) = as_subtraction(&source, &a) {
                    op.inputs = vec![x, y];
                    changes.folded += 1;
                    continue;
                }
            }

            // The signed comparisons: the sign of the difference against the
            // overflow flag.
            if matches!(o, Op::IntEqual | Op::IntNotEqual) {
                if let (Some((x, y)), Some((px, py))) =
                    (sign_of_difference(&source, &a), as_borrow(&source, &c))
                {
                    if x == px && y == py {
                        op.kind = SsaKind::Op(if o == Op::IntEqual {
                            // Sign agrees with overflow: not less than.
                            Op::IntSLessEqual
                        } else {
                            Op::IntSLess
                        });
                        op.inputs = if o == Op::IntEqual {
                            vec![y, x]
                        } else {
                            vec![x, y]
                        };
                        changes.folded += 1;
                        continue;
                    }
                }
            }

            // Not equal and not less is greater.
            if o == Op::BoolAnd {
                if let (Some((x, y)), Some((px, py))) =
                    (as_inequality(&source, &a), as_signed_le(&source, &c))
                {
                    if x == py && y == px {
                        op.kind = SsaKind::Op(Op::IntSLess);
                        op.inputs = vec![py, px];
                        changes.folded += 1;
                        continue;
                    }
                }
            }
        }
    }
    changes
}

/// The operands of a subtraction, if that is what an operand is.
fn as_subtraction(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntSub, inputs) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

/// `(x - y) >> (bits - 1) != 0`, which is the negative flag.
fn sign_of_difference(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntNotEqual, inputs) = source.get(v)? else {
        return None;
    };
    if inputs.get(1)?.as_const() != Some(0) {
        return None;
    }
    let Operand::Value(shifted) = inputs.first()? else {
        return None;
    };
    let (Op::IntRight, shift_inputs) = source.get(shifted)? else {
        return None;
    };
    let bits = shift_inputs.first()?.size() as u64 * 8;
    if shift_inputs.get(1)?.as_const() != Some(bits - 1) {
        return None;
    }
    as_subtraction(source, shift_inputs.first()?)
}

/// The operands of a signed borrow, if that is what an operand is.
fn as_borrow(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntSBorrow, inputs) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

fn as_inequality(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (op, inputs) = source.get(v)?;
    match op {
        Op::IntNotEqual => Some((inputs.first().cloned()?, inputs.get(1).cloned()?)),
        // The same thing said the other way round, which is how a machine that
        // inverts its condition codes writes it.
        Op::BoolNot => as_equality(source, inputs.first()?),
        _ => None,
    }
}

fn as_equality(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntEqual, inputs) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

fn as_signed_le(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntSLessEqual, inputs) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

/// Replace a repeated computation with the value it already produced.
///
/// Within a block only, and only for operations with no effect, so the
/// question of whether the earlier one is reachable from the later never
/// arises. Lifting produces these constantly: a compare and the branch that
/// reads it both recompute the same subtraction, and until they are the same
/// value no rule can see that they are the same condition.
pub fn cse(f: &mut SsaFunction) -> Changes {
    let mut changes = Changes::default();
    for b in f.blocks.values_mut() {
        let mut seen: BTreeMap<(Op, Vec<Operand>, u8), Value> = BTreeMap::new();
        for op in &mut b.ops {
            let SsaKind::Op(o) = op.kind else { continue };
            if !pure(o) {
                continue;
            }
            let Some(out) = op.out else { continue };
            let key = (o, op.inputs.clone(), op.size);
            match seen.get(&key) {
                Some(earlier) => {
                    op.kind = SsaKind::Op(Op::Copy);
                    op.inputs = vec![Operand::Value(*earlier)];
                    changes.folded += 1;
                }
                None => {
                    seen.insert(key, out);
                }
            }
        }
    }
    changes
}

/// True when an operation depends on nothing but its inputs.
fn pure(o: Op) -> bool {
    !matches!(
        o,
        Op::Load
            | Op::Store
            | Op::Call
            | Op::CallInd
            | Op::Branch
            | Op::CBranch
            | Op::BranchInd
            | Op::Return
            | Op::Unimplemented
            | Op::Copy
    )
}
