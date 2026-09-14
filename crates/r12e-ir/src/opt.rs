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

use std::cell::RefCell;
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
        round.add(divisions(f));
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
                    if operand_size(&op.inputs[0]) == op.size {
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
///
/// The size the operand itself carries, with no clamping to the operation's
/// width. Clamping used to happen here, and it made a narrowing copy compare
/// equal to the operation's size, so only a widening copy was ever refused and
/// an eight-byte value under a four-byte copy propagated into four-byte
/// contexts. That is the shape that once turned every signed `<` in the corpus
/// into its complement, so what the caller wants is the honest size.
///
/// Removing the clamp costs nothing measured: over 5,120 functions of the
/// fixture corpus there are 285,718 copies before optimization and 105,801
/// after, and not one of them has an operand of a different size from the copy
/// in either direction. The whole fixture corpus decompiles to the same text
/// either way and the roundtrip gate does not move. It is dropped because the
/// guard should mean what it says when a lifter does emit such a copy, not
/// because anything here emits one today.
fn operand_size(o: &Operand) -> u8 {
    match o {
        Operand::Const(_, s) => *s,
        Operand::Value(v) => v.location.size,
        Operand::Undefined(l) => l.size,
    }
    .max(1)
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
                // Taking the low bytes of a value that has no others. The
                // replacement has to be the same width: a narrow read is the
                // only record of how many bits an operation works at, and a
                // signed comparison rebuilt from operands that grew reads the
                // sign bit in the wrong place.
                Op::SubPiece if c.as_const() == Some(0) && ma & !width_mask(op.size) == 0 => {
                    narrowed_to(&source, &a, op.size)
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

/// An operand of exactly `size` bytes holding what the low `size` bytes of `o`
/// hold, when a widening put them there.
///
/// Zero-extending a value and then reading its low bytes back is what lifting a
/// narrow register write followed by a narrow read produces, and the value
/// before the extension is already the right width. Without this the only way
/// to keep the width is to keep the extract.
fn narrowed_to(
    source: &BTreeMap<Value, (Op, Vec<Operand>)>,
    o: &Operand,
    size: u8,
) -> Option<Operand> {
    let mut current = *o;
    // A bound rather than a visited set: the chains are a handful of links and
    // a cycle would otherwise spin here.
    for _ in 0..16 {
        if current.size() == size {
            return Some(current);
        }
        let Operand::Value(v) = current else {
            return None;
        };
        let (Op::IntZExt, inputs) = source.get(&v)? else {
            return None;
        };
        let next = *inputs.first()?;
        // Extending something narrower than the read puts zeroes in the bytes
        // being read, so the value before it is not what is wanted.
        if next.size() < size {
            return None;
        }
        current = next;
    }
    None
}

/// Rewrite flag algebra back into the comparison it stands for.
///
/// A machine has no `<`; it has a subtraction and four flags, and a condition
/// is a formula over them. Left alone that formula is what the decompiler
/// prints, and `(a - b) >> 63 != 0 == borrow(a, b)` is not what anyone wrote.
/// These rules recognize the formulas the architectures actually emit and put
/// the comparison back.
pub fn patterns(f: &mut SsaFunction) -> Changes {
    // The width each operation works at travels with it: a comparison rebuilt
    // from a subtraction has to compare the bits the subtraction subtracted.
    let mut source: BTreeMap<Value, (Op, Vec<Operand>, u8)> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let (Some(out), SsaKind::Op(o)) = (op.out, op.kind.clone()) {
                source.insert(out, (o, op.inputs.clone(), op.size));
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
                if let Some((x, y, width)) = as_subtraction(&source, &a) {
                    if let (Some(x), Some(y)) = (at_width(x, width), at_width(y, width)) {
                        op.inputs = vec![x, y];
                        changes.folded += 1;
                        continue;
                    }
                }
            }

            // The signed comparisons: the sign of the difference against the
            // overflow flag.
            if matches!(o, Op::IntEqual | Op::IntNotEqual) {
                if let (Some((x, y, width)), Some((px, py))) =
                    (sign_of_difference(&source, &a), as_borrow(&source, &c))
                {
                    // Both operands have to be the width the machine compared
                    // at, or the sign bit the comparison reads is not the one
                    // the flags were computed from.
                    let narrowed = match (x == px && y == py, at_width(x, width)) {
                        (true, Some(x)) => at_width(y, width).map(|y| (x, y)),
                        _ => None,
                    };
                    if let Some((x, y)) = narrowed {
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

            // Not equal and not less is greater. The inequality is on the
            // subtraction's operands and the `<=` is on them reversed, so
            // `x != y && y <= x` is `y < x`, which is the `<=`'s own order.
            if o == Op::BoolAnd {
                if let (Some((x, y)), Some((px, py))) =
                    (as_inequality(&source, &a), as_signed_le(&source, &c))
                {
                    if x == py && y == px {
                        op.kind = SsaKind::Op(Op::IntSLess);
                        op.inputs = vec![px, py];
                        changes.folded += 1;
                        continue;
                    }
                }
            }
        }
    }
    changes
}

/// The operands of a subtraction and the width it works at, if that is what an
/// operand is.
fn as_subtraction(
    source: &BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    o: &Operand,
) -> Option<(Operand, Operand, u8)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntSub, inputs, size) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?, *size))
}

/// An operand read at `width` bytes, or `None` when it cannot be.
///
/// A constant is whatever width it is needed at, since its value says
/// everything about it. Anything else already carries a width, and a
/// comparison rebuilt at a width the operand does not have would read a
/// different sign bit than the machine did.
fn at_width(o: Operand, width: u8) -> Option<Operand> {
    match o {
        _ if o.size() == width => Some(o),
        Operand::Const(v, _) => Some(Operand::Const(v & width_mask(width), width)),
        _ => None,
    }
}

/// `(x - y) >> (bits - 1) != 0`, which is the negative flag.
fn sign_of_difference(
    source: &BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    o: &Operand,
) -> Option<(Operand, Operand, u8)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntNotEqual, inputs, _) = source.get(v)? else {
        return None;
    };
    if inputs.get(1)?.as_const() != Some(0) {
        return None;
    }
    let Operand::Value(shifted) = inputs.first()? else {
        return None;
    };
    let (Op::IntRight, shift_inputs, _) = source.get(shifted)? else {
        return None;
    };
    let shifted_value = *shift_inputs.first()?;
    let bits = shifted_value.size() as u64 * 8;
    if shift_inputs.get(1)?.as_const() != Some(bits - 1) {
        return None;
    }
    // A comparison against zero leaves no subtraction behind: `x - 0` is `x`
    // and an earlier rule already said so, so the sign of the difference is
    // the sign of the value. Without this the whole flag formula survives into
    // the output as a borrow against zero.
    as_subtraction(source, &shifted_value).or_else(|| {
        let width = shifted_value.size();
        Some((shifted_value, Operand::Const(0, width), width))
    })
}

/// The operands of a signed borrow, if that is what an operand is.
fn as_borrow(
    source: &BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntSBorrow, inputs, _) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

fn as_inequality(
    source: &BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (op, inputs, _) = source.get(v)?;
    match op {
        Op::IntNotEqual => Some((inputs.first().cloned()?, inputs.get(1).cloned()?)),
        // The same thing said the other way round, which is how a machine that
        // inverts its condition codes writes it.
        Op::BoolNot => as_equality(source, inputs.first()?),
        _ => None,
    }
}

fn as_equality(
    source: &BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntEqual, inputs, _) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

fn as_signed_le(
    source: &BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    o: &Operand,
) -> Option<(Operand, Operand)> {
    let Operand::Value(v) = o else { return None };
    let (Op::IntSLessEqual, inputs, _) = source.get(v)? else {
        return None;
    };
    Some((inputs.first().cloned()?, inputs.get(1).cloned()?))
}

/// The divisor an unsigned reciprocal multiply and shift stand for, verified.
///
/// A compiler replaces `x / d` by `(x * magic) >> shift`, and `magic` is all
/// that survives into the machine code. The divisor is recoverable from it:
/// the transformation is correct only when `d` lies in `[2^shift / magic,
/// 2^shift / magic + 1)`, and that interval holds exactly one integer. What is
/// returned is that integer, but only after it has been checked against the
/// true quotient at every dividend in `0..=max`. Nothing here trusts the
/// derivation: a divisor that is wrong by one is a silently wrong program, and
/// the check is what a formula cannot be.
pub fn unsigned_divisor(magic: u64, shift: u32, max: u64) -> Option<u64> {
    let m = magic as i128;
    let d = candidate_divisor(m, shift)?;
    quotient_agrees(m, shift, d, 0, 0, max as i128).then_some(d as u64)
}

/// The divisor a signed reciprocal multiply and shift stand for, verified.
///
/// The signed sequence is `(magic * x >> shift) + (x < 0)`, where the shift is
/// arithmetic and the added bit is what turns a floor into a truncation. The
/// two halves of the range are different statements and both are checked: on
/// the negative side the correction is one short of a floor, which is what the
/// `-1` in the second check records.
pub fn signed_divisor(magic: u64, shift: u32, bits: u32) -> Option<u64> {
    if !(2..=64).contains(&bits) {
        return None;
    }
    let m = magic as i128;
    let d = candidate_divisor(m, shift)?;
    let top = 1i128 << (bits - 1);
    let ok =
        quotient_agrees(m, shift, d, 0, 0, top - 1) && quotient_agrees(m, shift, d, -1, 1, top);
    ok.then_some(d as u64)
}

/// The only divisor a magic number and a shift can stand for.
///
/// Agreement at the top of a quotient step forces `magic * d >= 2^shift` and
/// agreement just below the next one forces `magic * d < 2^shift + magic`, so
/// `d` is pinned to one integer before anything is checked. A multiplier of one
/// is refused, which is what keeps an ordinary shift an ordinary shift: a
/// compiler needs no reciprocal to divide by a power of two, so a shift with no
/// multiply in front of it is bit manipulation and printing it as a division
/// would bury what the code is doing.
fn candidate_divisor(m: i128, shift: u32) -> Option<i128> {
    if m <= 1 || shift >= 126 {
        return None;
    }
    let total = 1i128 << shift;
    let d = (total + m - 1) / m;
    (d >= 3 && d <= u64::MAX as i128).then_some(d)
}

/// True when `floor((m * x + bias) / 2^shift)` is `x / d` at every integer `x`
/// in `lo..=hi`.
///
/// Closed form rather than sampled. Writing `x` as `k * d + r` turns the left
/// side into `k` exactly when `0 <= k*e + r*m + bias < 2^shift`, where
/// `e = m*d - 2^shift` is what the reciprocal drifts by per step of the
/// quotient. That expression rises with `r` inside each run of `d` dividends
/// and drops at every run boundary, so its extremes over any interval are at
/// the ends of the interval and at the first and last whole run, which is a
/// handful of points to evaluate. Anything that overflows is refused rather
/// than wrapped.
fn quotient_agrees(m: i128, shift: u32, d: i128, bias: i128, lo: i128, hi: i128) -> bool {
    if m <= 0 || d <= 0 || lo < 0 || hi < lo || shift >= 126 {
        return false;
    }
    let span = 1i128 << shift;
    let Some(e) = m.checked_mul(d).and_then(|p| p.checked_sub(span)) else {
        return false;
    };
    let value = |x: i128| -> Option<i128> {
        (x / d)
            .checked_mul(e)?
            .checked_add((x % d).checked_mul(m)?)?
            .checked_add(bias)
    };
    let mut points = vec![lo, hi];
    for p in [
        // The end of the run `lo` falls in, and the start of the run `hi` does.
        (lo / d) * d + d - 1,
        (hi / d) * d,
        // The last whole run inside the interval, and the first.
        ((hi + 1) / d) * d - 1,
        ((lo + d - 1) / d) * d,
    ] {
        if p >= lo && p <= hi {
            points.push(p);
        }
    }
    points
        .into_iter()
        .all(|x| matches!(value(x), Some(v) if v >= 0 && v < span))
}

/// How far a recognizer follows a chain of definitions.
const REACH: u32 = 24;

/// A value the code computes as `floor(m * x / 2^shift)` for one dividend `x`.
///
/// Every rule that builds one of these is exact: the value it describes is the
/// value the machine computes, not an approximation of it. That is what makes
/// the divisor check meaningful.
#[derive(Debug, Clone, Copy)]
struct Scaled {
    /// The dividend as the code names it, before the widening.
    base: Operand,
    /// The dividend after the widening the multiply reads it through.
    wide: Operand,
    /// True when that widening was a sign extension.
    signed: bool,
    /// The exact multiplier, never a rounded one.
    m: i128,
    /// How far the exact product has been floor-divided, as a power of two.
    shift: u32,
}

/// What a function's values are computed by, for the reciprocal rules.
struct Reciprocal<'a> {
    source: &'a BTreeMap<Value, (Op, Vec<Operand>, u8)>,
    known: &'a KnownBits,
    /// What [`Reciprocal::scaled`] answered for an operand at a depth.
    ///
    /// It is a pure function of the two, and it branches: the `SubPiece` rule
    /// falls through to a second reading when the first does not fit, `IntAdd`
    /// tries two rules, and `combined` tries both operand orders. With
    /// [`REACH`] at 24 that is a search of up to 2^24 states over a graph with
    /// far fewer, and on one `IntRight` in a zlib function built at `-O0` it
    /// took 28 seconds. Remembering the answers makes it linear in the states
    /// that exist.
    memo: RefCell<BTreeMap<(Operand, u32), Option<Scaled>>>,
}

impl Reciprocal<'_> {
    /// What computed an operand, if anything in this function did.
    fn def(&self, o: &Operand) -> Option<(Op, &Vec<Operand>, u8)> {
        let Operand::Value(v) = o else { return None };
        let (op, inputs, size) = self.source.get(v)?;
        Some((*op, inputs, *size))
    }

    /// The interval the dividend lies in.
    ///
    /// A signed dividend spans its width; an unsigned one is bounded by the
    /// bits it can have set, which is tighter and is what makes a division of
    /// an already shifted value verifiable at all.
    fn base_range(&self, s: &Scaled) -> (i128, i128) {
        let bits = s.base.size().clamp(1, 8) as u32 * 8;
        if s.signed {
            (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
        } else {
            (0, self.known.operand(&s.base) as i128)
        }
    }

    /// The interval the scaled value itself lies in.
    fn range(&self, s: &Scaled) -> Option<(i128, i128)> {
        let (lo, hi) = self.base_range(s);
        let a = s.m.checked_mul(lo)? >> s.shift;
        let b = s.m.checked_mul(hi)? >> s.shift;
        Some((a.min(b), a.max(b)))
    }

    /// True when every value it can take survives being held in `size` bytes.
    ///
    /// The rules read the machine's registers as the mathematical values they
    /// stand for, and that reading is only honest while nothing has wrapped.
    fn fits(&self, s: &Scaled, size: u8) -> bool {
        let Some((lo, hi)) = self.range(s) else {
            return false;
        };
        let bits = size.clamp(1, 8) as u32 * 8;
        if s.signed {
            lo >= -(1i128 << (bits - 1)) && hi < (1i128 << (bits - 1))
        } else {
            lo >= 0 && (bits >= 127 || hi < (1i128 << bits))
        }
    }

    /// True when an operand is the dividend itself, however it is spelled.
    fn is_base(&self, o: &Operand, s: &Scaled) -> bool {
        *o == s.base || *o == s.wide || self.same(o, &s.base)
    }

    /// The value an operand carries, with the copies and the width changes
    /// that do not change it stripped off.
    fn core(&self, o: &Operand, depth: u32) -> Operand {
        if depth == 0 {
            return *o;
        }
        let Some((op, inputs, _)) = self.def(o) else {
            return *o;
        };
        let through = match op {
            Op::Copy | Op::IntZExt | Op::IntSExt => true,
            Op::SubPiece => inputs.get(1).and_then(|i| i.as_const()) == Some(0),
            _ => false,
        };
        match (through, inputs.first()) {
            (true, Some(i)) => self.core(i, depth - 1),
            _ => *o,
        }
    }

    /// True when two operands carry the same value.
    fn same(&self, a: &Operand, b: &Operand) -> bool {
        a == b || self.core(a, REACH) == self.core(b, REACH)
    }

    /// The exact value an operand computes, in reciprocal form.
    fn scaled(&self, o: &Operand, depth: u32) -> Option<Scaled> {
        if let Some(hit) = self.memo.borrow().get(&(*o, depth)) {
            return *hit;
        }
        let out = self.scaled_uncached(o, depth);
        self.memo.borrow_mut().insert((*o, depth), out);
        out
    }

    fn scaled_uncached(&self, o: &Operand, depth: u32) -> Option<Scaled> {
        if depth == 0 {
            return None;
        }
        let (op, inputs, size) = self.def(o)?;
        let first = *inputs.first()?;
        match op {
            Op::Copy => self.scaled(&first, depth - 1),
            // The widening is where the dividend enters, and whether it was
            // signed or zero filled is what says how to read every bit above.
            Op::IntZExt | Op::IntSExt => {
                if first.size() >= size {
                    return None;
                }
                let s = Scaled {
                    base: first,
                    wide: *o,
                    signed: op == Op::IntSExt,
                    m: 1,
                    shift: 0,
                };
                self.fits(&s, size).then_some(s)
            }
            // Multiplying a value that has already been floor-divided loses
            // the remainder, so only an exact product composes.
            Op::IntMul => {
                let (c, other) = multiplier(inputs, size)?;
                let a = self.scaled(&other, depth - 1)?;
                if a.shift != 0 {
                    return None;
                }
                let s = Scaled {
                    m: a.m.checked_mul(c)?,
                    ..a
                };
                // The multiplier may be negative here: a reciprocal that needs
                // more bits than the multiply holds is stored as its low half,
                // and the missing one comes back as the dividend added later.
                self.fits(&s, size).then_some(s)
            }
            Op::IntSRight => {
                let n = inputs.get(1)?.as_const()? as u32;
                let a = self.scaled(&first, depth - 1)?;
                if !a.signed || n >= 126 || !self.fits(&a, size) {
                    return None;
                }
                Some(Scaled {
                    shift: a.shift + n,
                    ..a
                })
            }
            Op::IntRight => {
                let n = inputs.get(1)?.as_const()? as u32;
                let a = self.scaled(&first, depth - 1)?;
                if a.signed || n >= 126 || !self.fits(&a, size) {
                    return None;
                }
                Some(Scaled {
                    shift: a.shift + n,
                    ..a
                })
            }
            Op::SubPiece if inputs.get(1)?.as_const() == Some(0) => {
                // A logical shift whose zero fill lands above the bytes kept
                // is, at this width, the arithmetic shift a signed value
                // needs, and it is how a compiler reads the high half of a
                // product back.
                if let Some((Op::IntRight, hi, inner)) = self.def(&first) {
                    let n = hi.get(1)?.as_const()? as u32;
                    if n + size as u32 * 8 >= inner as u32 * 8 && n < 126 {
                        if let Some(a) = self.scaled(hi.first()?, depth - 1) {
                            if self.fits(&a, inner) {
                                let s = Scaled {
                                    shift: a.shift + n,
                                    ..a
                                };
                                return self.fits(&s, size).then_some(s);
                            }
                        }
                    }
                }
                let a = self.scaled(&first, depth - 1)?;
                self.fits(&a, size).then_some(a)
            }
            Op::IntAdd => self
                .halved_sum(inputs, size, depth)
                .or_else(|| self.combined(inputs, size, 1, depth)),
            Op::IntSub => self.combined(inputs, size, -1, depth),
            _ => None,
        }
    }

    /// A term of a sum, where the dividend spelled plainly counts as one.
    fn term(&self, o: &Operand, of: &Scaled, depth: u32) -> Option<Scaled> {
        if self.is_base(o, of) {
            return Some(Scaled {
                m: 1,
                shift: 0,
                ..*of
            });
        }
        let s = self.scaled(o, depth)?;
        (self.same(&s.base, &of.base) && s.signed == of.signed).then_some(s)
    }

    /// `a + b` or `a - b`, which is exact only while one side is unshifted:
    /// two floors added are not the floor of the sum.
    fn combined(&self, inputs: &[Operand], size: u8, sign: i128, depth: u32) -> Option<Scaled> {
        let (l, r) = (*inputs.first()?, *inputs.get(1)?);
        let orders: &[(Operand, Operand)] = if sign < 0 {
            &[(l, r)]
        } else {
            &[(l, r), (r, l)]
        };
        for (l, r) in orders {
            let Some(a) = self.scaled(l, depth - 1) else {
                continue;
            };
            let Some(b) = self.term(r, &a, depth - 1) else {
                continue;
            };
            if b.shift != 0 {
                continue;
            }
            let Some(scale) = 1i128.checked_shl(a.shift) else {
                continue;
            };
            let Some(m) =
                b.m.checked_mul(scale)
                    .and_then(|t| a.m.checked_add(sign * t))
            else {
                continue;
            };
            let s = Scaled { m, ..a };
            if self.fits(&s, size) {
                return Some(s);
            }
        }
        None
    }

    /// `t + ((x - t) >> 1)`, which is `floor((x + t) / 2)`.
    ///
    /// A compiler emits this when the reciprocal needs one bit more than the
    /// multiply can hold: the bit it cannot store is the `x` this adds back,
    /// and the halving is what puts the result back in range.
    fn halved_sum(&self, inputs: &[Operand], size: u8, depth: u32) -> Option<Scaled> {
        let (l, r) = (*inputs.first()?, *inputs.get(1)?);
        for (t, half) in [(l, r), (r, l)] {
            let Some(a) = self.scaled(&t, depth - 1) else {
                continue;
            };
            // The subtraction only borrows nothing, and the shift only floors,
            // while `t` cannot exceed `x`.
            let Some(scale) = 1i128.checked_shl(a.shift) else {
                continue;
            };
            if a.signed || a.m < 0 || a.m > scale {
                continue;
            }
            let Some((Op::IntRight, hi, _)) = self.def(&half) else {
                continue;
            };
            if hi.get(1)?.as_const() != Some(1) {
                continue;
            }
            let Some((Op::IntSub, sub, _)) = self.def(hi.first()?) else {
                continue;
            };
            if !self.same(sub.get(1)?, &t) || !self.is_base(sub.first()?, &a) {
                continue;
            }
            let Some(m) = a.m.checked_add(scale) else {
                continue;
            };
            let s = Scaled {
                m,
                shift: a.shift + 1,
                ..a
            };
            if self.fits(&s, size) {
                return Some(s);
            }
        }
        None
    }

    /// The dividend at the width the division has to be written at.
    fn dividend(&self, s: &Scaled, size: u8) -> Option<Operand> {
        [s.wide, s.base].into_iter().find(|o| o.size() == size)
    }

    /// `v >> n` where the shift reads the sign, through the truncation the
    /// machine may have done afterwards.
    fn arithmetic_shift(&self, o: &Operand) -> Option<(Operand, u32)> {
        let (op, inputs, size) = self.def(o)?;
        match op {
            Op::Copy => self.arithmetic_shift(inputs.first()?),
            Op::IntSRight => Some((*inputs.first()?, inputs.get(1)?.as_const()? as u32)),
            Op::SubPiece if inputs.get(1)?.as_const() == Some(0) => {
                let (inner, within, wide) = self.def(inputs.first()?)?;
                let n = within.get(1)?.as_const()? as u32;
                match inner {
                    Op::IntSRight => Some((*within.first()?, n)),
                    // The zero fill lands above the bytes kept, so at this
                    // width the logical shift is the arithmetic one.
                    Op::IntRight if n + size as u32 * 8 >= wide as u32 * 8 => {
                        Some((*within.first()?, n))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The value whose sign bit an operand holds.
    fn sign_bit(&self, o: &Operand) -> Option<Operand> {
        let (op, inputs, size) = self.def(o)?;
        match op {
            Op::Copy => self.sign_bit(inputs.first()?),
            Op::SubPiece if inputs.get(1)?.as_const() == Some(0) => self.sign_bit(inputs.first()?),
            Op::IntRight if inputs.get(1)?.as_const() == Some(size as u64 * 8 - 1) => {
                Some(*inputs.first()?)
            }
            _ => None,
        }
    }

    /// An unsigned reciprocal: the final shift of a magic product.
    fn unsigned_quotient(&self, o: Op, inputs: &[Operand], size: u8) -> Option<(Op, Vec<Operand>)> {
        if o != Op::IntRight {
            return None;
        }
        let n = inputs.get(1)?.as_const()? as u32;
        let s = self.scaled(inputs.first()?, REACH)?;
        if s.signed || s.m < 2 || s.m > u64::MAX as i128 {
            return None;
        }
        let (_, hi) = self.base_range(&s);
        let d = unsigned_divisor(s.m as u64, s.shift.checked_add(n)?, hi as u64)?;
        let x = self.dividend(&s, size)?;
        Some((Op::IntDiv, vec![x, Operand::Const(d, size)]))
    }

    /// A signed reciprocal: an arithmetic shift of a magic product plus the
    /// sign bit of that same product, which is what rounds toward zero.
    fn signed_quotient(&self, o: Op, inputs: &[Operand], size: u8) -> Option<(Op, Vec<Operand>)> {
        if o != Op::IntAdd {
            return None;
        }
        let (l, r) = (*inputs.first()?, *inputs.get(1)?);
        for (high, sign) in [(l, r), (r, l)] {
            let Some((value, n)) = self.arithmetic_shift(&high) else {
                continue;
            };
            if self.sign_bit(&sign) != Some(value) {
                continue;
            }
            let Some(s) = self.scaled(&value, REACH) else {
                continue;
            };
            if !s.signed || s.m < 2 || s.m > u64::MAX as i128 {
                continue;
            }
            let bits = s.base.size().clamp(1, 8) as u32 * 8;
            let Some(total) = s.shift.checked_add(n) else {
                continue;
            };
            let Some(d) = signed_divisor(s.m as u64, total, bits) else {
                continue;
            };
            let Some(x) = self.dividend(&s, size) else {
                continue;
            };
            return Some((Op::IntSDiv, vec![x, Operand::Const(d, size)]));
        }
        None
    }

    /// `c ? a : b`, written the way a conditional move lifts: a mask that is
    /// all ones or all zeroes, and its complement.
    fn select(&self, o: &Operand) -> Option<(Operand, Operand, Operand)> {
        let (Op::IntOr, parts, _) = self.def(o)? else {
            return None;
        };
        self.select_parts(parts)
    }

    /// The same, read from the two halves of the `or` rather than from the
    /// value they were combined into, for a rule whose whole subject is the
    /// select and not something built on it.
    fn select_parts(&self, parts: &[Operand]) -> Option<(Operand, Operand, Operand)> {
        let (Op::IntAnd, left, _) = self.def(parts.first()?)? else {
            return None;
        };
        let (Op::IntAnd, right, _) = self.def(parts.get(1)?)? else {
            return None;
        };
        let (l0, l1) = (*left.first()?, *left.get(1)?);
        let (r0, r1) = (*right.first()?, *right.get(1)?);
        for (taken, mask) in [(l0, l1), (l1, l0)] {
            let Some(condition) = self.condition_mask(&mask) else {
                continue;
            };
            for (other, complement) in [(r0, r1), (r1, r0)] {
                if let Some((Op::IntNot, of, _)) = self.def(&complement) {
                    if of.first() == Some(&mask) {
                        return Some((condition, taken, other));
                    }
                }
            }
        }
        None
    }

    /// The condition a `0 - c` mask stands for.
    fn condition_mask(&self, o: &Operand) -> Option<Operand> {
        let (op, inputs, _) = self.def(o)?;
        let widened = match op {
            Op::IntNegate => *inputs.first()?,
            Op::IntSub if inputs.first()?.as_const() == Some(0) => *inputs.get(1)?,
            _ => return None,
        };
        let (Op::IntZExt, of, _) = self.def(&widened)? else {
            return None;
        };
        Some(*of.first()?)
    }

    /// Whether a condition says `x` is negative, or says it is not.
    fn negative_test(&self, c: &Operand, x: &Operand, depth: u32) -> Option<bool> {
        if depth == 0 {
            return None;
        }
        let (op, inputs, _) = self.def(c)?;
        let first = *inputs.first()?;
        let second = inputs.get(1).copied();
        let zero = |o: Option<Operand>| o.and_then(|o| o.as_const()) == Some(0);
        match op {
            Op::Copy => self.negative_test(&first, x, depth - 1),
            Op::BoolNot => Some(!self.negative_test(&first, x, depth - 1)?),
            Op::IntSLess if zero(second) && self.same(&first, x) => Some(true),
            // `0 <= x` is how the flag rewrite spells the complement.
            Op::IntSLessEqual if first.as_const() == Some(0) && self.same(&second?, x) => {
                Some(false)
            }
            Op::IntNotEqual if zero(second) => self.is_sign_test(&first, x).then_some(true),
            Op::IntEqual if zero(second) => match self.is_sign_test(&first, x) {
                true => Some(false),
                false => Some(!self.negative_test(&first, x, depth - 1)?),
            },
            _ => None,
        }
    }

    /// True when an operand is `x`'s sign bit, by shift or by mask.
    fn is_sign_test(&self, o: &Operand, x: &Operand) -> bool {
        let Some((op, inputs, size)) = self.def(o) else {
            return false;
        };
        let Some(first) = inputs.first() else {
            return false;
        };
        if !self.same(first, x) {
            return false;
        }
        let top = size.clamp(1, 8) as u64 * 8 - 1;
        match (op, inputs.get(1).and_then(|i| i.as_const())) {
            (Op::IntRight, Some(n)) => n == top,
            (Op::IntAnd, Some(k)) => k == 1u64 << top,
            _ => false,
        }
    }

    /// A signed division by a power of two: the dividend biased when it is
    /// negative, then shifted. The bias is what makes the shift round toward
    /// zero the way the language says a division does.
    fn power_of_two_quotient(
        &self,
        o: Op,
        inputs: &[Operand],
        size: u8,
    ) -> Option<(Op, Vec<Operand>)> {
        if o != Op::IntSRight {
            return None;
        }
        let k = inputs.get(1)?.as_const()?;
        let bits = size.clamp(1, 8) as u64 * 8;
        if k == 0 || k >= bits {
            return None;
        }
        let x = self.biased(inputs.first()?, k, size)?;
        Some((Op::IntSDiv, vec![x, Operand::Const(1u64 << k, size)]))
    }

    /// The dividend `x` of a value that is `x` biased by `2^k - 1` when `x` is
    /// negative, however the bias was arrived at.
    fn biased(&self, o: &Operand, k: u64, size: u8) -> Option<Operand> {
        self.branch_biased(o, k, size)
            .or_else(|| self.shift_biased(o, k, size))
    }

    /// `x < 0 ? x + 2^k - 1 : x`, which is what a conditional move spells.
    fn branch_biased(&self, o: &Operand, k: u64, size: u8) -> Option<Operand> {
        let (condition, taken, other) = self.select(o)?;
        for (biased, plain, negative) in [(taken, other, true), (other, taken, false)] {
            let Some((Op::IntAdd, sum, _)) = self.def(&biased) else {
                continue;
            };
            if !self.same(sum.first()?, &plain) {
                continue;
            }
            if sum.get(1)?.as_const() != Some((1u64 << k) - 1) {
                continue;
            }
            if self.negative_test(&condition, &plain, REACH) != Some(negative) {
                continue;
            }
            if plain.size() != size {
                continue;
            }
            return Some(plain);
        }
        None
    }

    /// `x + (2^k - 1 when x is negative)`, where the bias was computed with
    /// shifts rather than with a branch.
    ///
    /// The sign bit of `x` is `2^1 - 1` or zero, so for a divisor of two one
    /// logical shift is the whole bias. For anything wider the value has to be
    /// smeared first: an arithmetic shift by `bits - 1` makes the sign a mask
    /// of all ones or all zeroes, and a logical shift back by `bits - k` keeps
    /// `k` of them. Reading the second shift alone would be wrong, because the
    /// top `k` bits of a negative number are not all ones.
    fn shift_biased(&self, o: &Operand, k: u64, size: u8) -> Option<Operand> {
        let (Op::IntAdd, sum, _) = self.def(o)? else {
            return None;
        };
        let bits = size.clamp(1, 8) as u64 * 8;
        let (l, r) = (*sum.first()?, *sum.get(1)?);
        for (x, bias) in [(l, r), (r, l)] {
            if x.size() != size || bias.size() != size {
                continue;
            }
            let Some((Op::IntRight, shift, width)) = self.def(&bias) else {
                continue;
            };
            let Some(n) = shift.get(1).and_then(|i| i.as_const()) else {
                continue;
            };
            let Some(inner) = shift.first() else { continue };
            if width != size {
                continue;
            }
            if k == 1 && n == bits - 1 && self.same(inner, &x) {
                return Some(x);
            }
            if n != bits - k {
                continue;
            }
            let Some((Op::IntSRight, sign, smeared)) = self.def(inner) else {
                continue;
            };
            let whole = sign.get(1).and_then(|i| i.as_const()) == Some(bits - 1);
            if smeared == size && whole && sign.first().is_some_and(|v| self.same(v, &x)) {
                return Some(x);
            }
        }
        None
    }

    /// `x - ((x + bias) & -2^k)`, which is `x % 2^k` on a signed value.
    ///
    /// The masked value is the quotient times `2^k`, so what the subtraction
    /// leaves is the remainder. A compiler reaches for this rather than a
    /// shift and a multiply back because the mask costs one instruction.
    fn masked_remainder(&self, o: Op, inputs: &[Operand], size: u8) -> Option<(Op, Vec<Operand>)> {
        if o != Op::IntSub {
            return None;
        }
        let x = *inputs.first()?;
        if x.size() != size {
            return None;
        }
        let (Op::IntAnd, masked, width) = self.def(inputs.get(1)?)? else {
            return None;
        };
        let bits = size.clamp(1, 8) as u32 * 8;
        let whole = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let mask = masked.get(1)?.as_const()? & whole;
        let k = mask.trailing_zeros() as u64;
        if width != size || k == 0 || k >= bits as u64 || mask != (u64::MAX << k) & whole {
            return None;
        }
        let y = self.biased(masked.first()?, k, size)?;
        self.same(&y, &x)
            .then(|| (Op::IntSRem, vec![x, Operand::Const(1u64 << k, size)]))
    }

    /// `x < 0 ? -(x & 1) : (x & 1)`, which is `x % 2` on a signed value.
    ///
    /// The remainder of a signed division by two is the low bit wearing the
    /// dividend's sign, and a compiler emits that rather than anything that
    /// looks like a division. Two only: for a wider power the low bits of a
    /// negative dividend are not its remainder, and a compiler biases the
    /// value first instead, which is the rule above.
    fn low_bit_remainder(&self, o: Op, inputs: &[Operand], size: u8) -> Option<(Op, Vec<Operand>)> {
        if o != Op::IntOr {
            return None;
        }
        let (condition, taken, other) = self.select_parts(inputs)?;
        for (negated, plain, negative) in [(taken, other, true), (other, taken, false)] {
            if !self.is_negation(&negated, &plain) {
                continue;
            }
            let Some((Op::IntAnd, masked, width)) = self.def(&plain) else {
                continue;
            };
            if width != size || masked.get(1)?.as_const() != Some(1) {
                continue;
            }
            let x = *masked.first()?;
            if x.size() != size {
                continue;
            }
            if self.negative_test(&condition, &x, REACH) != Some(negative) {
                continue;
            }
            return Some((Op::IntSRem, vec![x, Operand::Const(2, size)]));
        }
        None
    }

    /// True when one operand is what another one negated.
    fn is_negation(&self, o: &Operand, of: &Operand) -> bool {
        let Some((op, inputs, _)) = self.def(o) else {
            return false;
        };
        let value = match op {
            Op::IntNegate => inputs.first(),
            Op::IntSub if inputs.first().and_then(|i| i.as_const()) == Some(0) => inputs.get(1),
            _ => return false,
        };
        value.is_some_and(|v| self.same(v, of))
    }

    /// How many times a quotient an operand is, if it is a multiple of one.
    fn multiple_of_quotient(&self, o: &Operand, depth: u32) -> Option<(i128, Operand)> {
        if depth == 0 {
            return None;
        }
        let (op, inputs, size) = self.def(o)?;
        let first = *inputs.first()?;
        match op {
            Op::IntDiv | Op::IntSDiv => Some((1, *o)),
            Op::Copy | Op::IntZExt | Op::IntSExt => self.multiple_of_quotient(&first, depth - 1),
            Op::SubPiece if inputs.get(1)?.as_const() == Some(0) => {
                self.multiple_of_quotient(&first, depth - 1)
            }
            Op::IntNegate => {
                let (k, q) = self.multiple_of_quotient(&first, depth - 1)?;
                Some((-k, q))
            }
            Op::IntMul => {
                let (c, other) = multiplier(inputs, size)?;
                let (k, q) = self.multiple_of_quotient(&other, depth - 1)?;
                Some((k.checked_mul(c)?, q))
            }
            Op::IntLeft => {
                let n = inputs.get(1)?.as_const()? as u32;
                let (k, q) = self.multiple_of_quotient(&first, depth - 1)?;
                Some((k.checked_mul(1i128.checked_shl(n)?)?, q))
            }
            Op::IntAdd | Op::IntSub => {
                let (k, q) = self.multiple_of_quotient(&first, depth - 1)?;
                let (j, p) = self.multiple_of_quotient(inputs.get(1)?, depth - 1)?;
                if q != p {
                    return None;
                }
                let k = if op == Op::IntAdd {
                    k.checked_add(j)?
                } else {
                    k.checked_sub(j)?
                };
                Some((k, q))
            }
            _ => None,
        }
    }

    /// `x - d * (x / d)`, which is the remainder the compiler did not have an
    /// instruction for.
    fn remainder(&self, o: Op, inputs: &[Operand], size: u8) -> Option<(Op, Vec<Operand>)> {
        let wanted: i128 = match o {
            Op::IntSub => 1,
            Op::IntAdd => -1,
            _ => return None,
        };
        let (l, r) = (*inputs.first()?, *inputs.get(1)?);
        let orders: &[(Operand, Operand)] = if o == Op::IntSub {
            &[(l, r)]
        } else {
            &[(l, r), (r, l)]
        };
        for (x, multiple) in orders {
            if x.size() != size {
                continue;
            }
            let Some((k, q)) = self.multiple_of_quotient(multiple, REACH) else {
                continue;
            };
            let Some((division, operands, _)) = self.def(&q) else {
                continue;
            };
            let Some(d) = operands.get(1).and_then(|i| i.as_const()) else {
                continue;
            };
            if k != wanted * d as i128 || !self.same(operands.first()?, x) {
                continue;
            }
            let rem = if division == Op::IntSDiv {
                Op::IntSRem
            } else {
                Op::IntRem
            };
            return Some((rem, vec![*x, Operand::Const(d, size)]));
        }
        None
    }

    /// The division or remainder an operation is, if it is one.
    fn recognize(&self, o: Op, inputs: &[Operand], size: u8) -> Option<(Op, Vec<Operand>)> {
        self.unsigned_quotient(o, inputs, size)
            .or_else(|| self.signed_quotient(o, inputs, size))
            .or_else(|| self.power_of_two_quotient(o, inputs, size))
            .or_else(|| self.remainder(o, inputs, size))
            .or_else(|| self.masked_remainder(o, inputs, size))
            .or_else(|| self.low_bit_remainder(o, inputs, size))
    }
}

/// A multiply's constant factor and whatever it multiplies, either way round.
///
/// Multiplication commutes and the two lifters do not put the reciprocal on
/// the same side: x86-64 loads the magic number into a register and multiplies
/// the argument into it, so the constant arrives first. Reading only the second
/// operand left `x / 81` unfolded on one architecture and folded on the other.
fn multiplier(inputs: &[Operand], size: u8) -> Option<(i128, Operand)> {
    let (l, r) = (*inputs.first()?, *inputs.get(1)?);
    match (l.as_const(), r.as_const()) {
        (_, Some(c)) => Some((sign_extended(c, size), l)),
        (Some(c), None) => Some((sign_extended(c, size), r)),
        _ => None,
    }
}

/// A constant read as the signed number a `size`-byte operand holds.
fn sign_extended(v: u64, size: u8) -> i128 {
    match size.clamp(1, 8) as u32 * 8 {
        64 => v as i64 as i128,
        bits => {
            let shift = 128 - bits;
            ((v as i128) << shift) >> shift
        }
    }
}

/// Rewrite the reciprocal multiplies a compiler emits back into divisions.
///
/// No compiler emits a divide instruction for a constant divisor: it
/// multiplies by a fixed point reciprocal and shifts, and three or four
/// instructions stand where one operator did. Undoing that is the difference
/// between `x / 81` and `x * 0xca4587e7 >> 38`.
///
/// The recovery is arithmetic, not a table of known constants: the divisor
/// follows from the magic number, the shift and the range the dividend lives
/// in. Every candidate is then checked against the true quotient over that
/// whole range in closed form, and one that does not agree everywhere is not
/// emitted. A division nothing verified would be a silently wrong program,
/// which is worse than the multiply it replaced.
pub fn divisions(f: &mut SsaFunction) -> Changes {
    let mut source: BTreeMap<Value, (Op, Vec<Operand>, u8)> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let (Some(out), SsaKind::Op(o)) = (op.out, op.kind.clone()) {
                source.insert(out, (o, op.inputs.clone(), op.size));
            }
        }
    }
    let known = KnownBits::of(f);
    let rules = Reciprocal {
        source: &source,
        known: &known,
        memo: RefCell::new(BTreeMap::new()),
    };

    let mut changes = Changes::default();
    for b in f.blocks.values_mut() {
        for op in b.ops.iter_mut() {
            let SsaKind::Op(o) = op.kind else { continue };
            let Some((kind, inputs)) = rules.recognize(o, &op.inputs, op.size) else {
                continue;
            };
            op.kind = SsaKind::Op(kind);
            op.inputs = inputs;
            changes.folded += 1;
        }
    }
    changes
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
