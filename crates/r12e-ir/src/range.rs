//! What values a computation can produce.
//!
//! An interval per value, worked out from the operations that make it. It is
//! what bounds a jump table's index, what proves a comparison is always true,
//! and what says a loop counter never leaves the array it walks.
//!
//! Every answer is sound in one direction: the interval always contains every
//! value the computation can produce. It is allowed to be wider than the truth
//! and is often very much wider, but it never excludes something that can
//! happen, because a bound that is sometimes wrong is worse than no bound.

use std::collections::BTreeMap;

use crate::op::{Op, Space};
use crate::ssa::{Operand, SsaFunction, SsaKind, Value};

/// The values a computation can produce, as a signed interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    /// The smallest, read as signed.
    pub low: i64,
    /// The largest.
    pub high: i64,
}

impl Range {
    /// Everything.
    pub const ANY: Range = Range {
        low: i64::MIN,
        high: i64::MAX,
    };

    /// Exactly one value.
    pub fn exact(v: i64) -> Range {
        Range { low: v, high: v }
    }

    /// From a bound pair, in either order.
    pub fn new(a: i64, b: i64) -> Range {
        Range {
            low: a.min(b),
            high: a.max(b),
        }
    }

    /// Everything a value of this many bytes can hold, unsigned.
    pub fn unsigned(size: u8) -> Range {
        match size {
            1 => Range::new(0, 0xff),
            2 => Range::new(0, 0xffff),
            4 => Range::new(0, 0xffff_ffff),
            _ => Range::ANY,
        }
    }

    /// True when nothing outside this interval can happen.
    pub fn contains(&self, v: i64) -> bool {
        self.low <= v && v <= self.high
    }

    /// True when the interval is everything, which is the same as knowing
    /// nothing.
    pub fn is_any(&self) -> bool {
        self.low == i64::MIN && self.high == i64::MAX
    }

    /// How many values it admits, saturating.
    pub fn width(&self) -> u64 {
        (self.high as i128 - self.low as i128).unsigned_abs() as u64
    }

    /// The smallest interval containing both.
    pub fn join(self, other: Range) -> Range {
        Range {
            low: self.low.min(other.low),
            high: self.high.max(other.high),
        }
    }

    fn add(self, other: Range) -> Range {
        match (
            self.low.checked_add(other.low),
            self.high.checked_add(other.high),
        ) {
            (Some(low), Some(high)) => Range { low, high },
            _ => Range::ANY,
        }
    }

    fn sub(self, other: Range) -> Range {
        match (
            self.low.checked_sub(other.high),
            self.high.checked_sub(other.low),
        ) {
            (Some(low), Some(high)) => Range { low, high },
            _ => Range::ANY,
        }
    }

    fn mul(self, other: Range) -> Range {
        // Every corner, because the signs decide which is the extreme.
        let corners = [
            self.low.checked_mul(other.low),
            self.low.checked_mul(other.high),
            self.high.checked_mul(other.low),
            self.high.checked_mul(other.high),
        ];
        if corners.iter().any(|c| c.is_none()) {
            return Range::ANY;
        }
        let values: Vec<i64> = corners.into_iter().flatten().collect();
        Range {
            low: *values.iter().min().unwrap_or(&i64::MIN),
            high: *values.iter().max().unwrap_or(&i64::MAX),
        }
    }
}

/// How many rounds before an interval that keeps growing is given up on.
const ROUNDS: u32 = 8;

/// The interval of every value in a function.
pub fn ranges(f: &SsaFunction) -> BTreeMap<Value, Range> {
    let mut out: BTreeMap<Value, Range> = BTreeMap::new();
    // Iterate: a phi depends on values defined later, and the intervals only
    // widen, so this settles. A value still growing when the rounds run out is
    // widened to everything rather than left half-computed.
    for round in 0..ROUNDS {
        let mut changed = false;
        for b in f.blocks.values() {
            for op in &b.ops {
                let Some(out_value) = op.out else { continue };
                let mut computed = evaluate(op, &out);
                // The last round widens anything that is still moving, which
                // is what makes a loop counter terminate at something honest.
                if round + 1 == ROUNDS {
                    if let Some(previous) = out.get(&out_value) {
                        if *previous != computed {
                            computed = Range::ANY;
                        }
                    }
                }
                let joined = match out.get(&out_value) {
                    Some(previous) => previous.join(computed),
                    None => computed,
                };
                if out.get(&out_value) != Some(&joined) {
                    out.insert(out_value, joined);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    out
}

/// The interval one operand can take.
pub fn of(operand: &Operand, known: &BTreeMap<Value, Range>) -> Range {
    match operand {
        Operand::Const(v, size) => {
            // A constant is exact, read at its own width the way the
            // operation that made it will read it.
            let bits = (*size as u32 * 8).min(64);
            let signed = if bits == 64 {
                *v as i64
            } else {
                ((*v << (64 - bits)) as i64) >> (64 - bits)
            };
            Range::exact(signed)
        }
        Operand::Value(v) => known.get(v).copied().unwrap_or(Range::ANY),
        Operand::Undefined(l) if l.space == Space::Register => Range::ANY,
        Operand::Undefined(_) => Range::ANY,
    }
}

fn evaluate(op: &crate::ssa::SsaOp, known: &BTreeMap<Value, Range>) -> Range {
    let a = || {
        op.inputs
            .first()
            .map(|i| of(i, known))
            .unwrap_or(Range::ANY)
    };
    let b = || op.inputs.get(1).map(|i| of(i, known)).unwrap_or(Range::ANY);

    match op.kind {
        // A merge can be anything either path produced.
        SsaKind::Phi => op
            .inputs
            .iter()
            .map(|i| of(i, known))
            .reduce(Range::join)
            .unwrap_or(Range::ANY),
        SsaKind::Op(kind) => match kind {
            Op::Copy => a(),
            Op::IntAdd => a().add(b()),
            Op::IntSub => a().sub(b()),
            Op::IntMul => a().mul(b()),
            // A mask cannot produce a bit the mask does not have.
            Op::IntAnd => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(mask) if mask <= i64::MAX as u64 => {
                    let bounded = Range::new(0, mask as i64);
                    // Masking a value already known non-negative cannot raise
                    // it either.
                    let source = a();
                    if source.low >= 0 {
                        Range::new(0, source.high.min(mask as i64))
                    } else {
                        bounded
                    }
                }
                _ => Range::ANY,
            },
            Op::IntOr | Op::IntXor => Range::ANY,
            // A shift by a constant is a multiply or a divide.
            Op::IntLeft => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(n) if n < 62 => a().mul(Range::exact(1i64 << n)),
                _ => Range::ANY,
            },
            Op::IntRight => {
                let source = a();
                match (op.inputs.get(1).and_then(|i| i.as_const()), source.low >= 0) {
                    (Some(n), true) if n < 64 => Range::new(source.low >> n, source.high >> n),
                    _ => Range::unsigned(op.size),
                }
            }
            Op::IntSRight => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(n) if n < 64 => {
                    let source = a();
                    Range::new(source.low >> n, source.high >> n)
                }
                _ => Range::ANY,
            },
            // Widening says exactly how wide the result is.
            Op::IntZExt => {
                let source = a();
                let from = op.inputs.first().map(|i| i.size()).unwrap_or(op.size);
                if source.low >= 0 {
                    Range::new(0, source.high.max(0))
                } else {
                    Range::unsigned(from)
                }
            }
            Op::IntSExt => a(),
            Op::SubPiece => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(0) => {
                    let source = a();
                    let width = Range::unsigned(op.size);
                    if source.low >= 0 && width.contains(source.high) {
                        Range::new(0, source.high)
                    } else {
                        width
                    }
                }
                _ => Range::unsigned(op.size),
            },
            Op::Load => Range::unsigned(op.size),
            // A truth is a truth.
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
            | Op::FloatNan => Range::new(0, 1),
            Op::PopCount => Range::new(0, 64),
            Op::LzCount => Range::new(0, 64),
            // Division cannot make a number bigger than what it divides, once
            // the sign is accounted for.
            Op::IntDiv | Op::IntRem => {
                let source = a();
                if source.low >= 0 {
                    Range::new(0, source.high)
                } else {
                    Range::ANY
                }
            }
            _ => Range::ANY,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_mask_bounds_what_it_masks() {
        assert_eq!(Range::new(0, 0xff).high, 255);
        assert!(Range::new(0, 0xff).contains(0));
        assert!(Range::new(0, 0xff).contains(255));
        assert!(!Range::new(0, 0xff).contains(256));
    }

    #[test]
    fn arithmetic_that_would_overflow_gives_up_rather_than_wrapping() {
        let huge = Range::new(i64::MAX - 1, i64::MAX);
        assert!(huge.add(Range::exact(2)).is_any());
        assert!(huge.mul(Range::exact(2)).is_any());
    }

    #[test]
    fn joining_keeps_both() {
        let a = Range::new(0, 10);
        let b = Range::new(-5, 3);
        let joined = a.join(b);
        assert_eq!(joined, Range::new(-5, 10));
        assert!(joined.contains(-5) && joined.contains(10));
    }

    #[test]
    fn a_constant_is_read_at_its_own_width() {
        let known: BTreeMap<Value, Range> = BTreeMap::new();
        // 0xff as one byte is minus one, not two hundred and fifty five.
        assert_eq!(of(&Operand::Const(0xff, 1), &known), Range::exact(-1));
        assert_eq!(of(&Operand::Const(0xff, 8), &known), Range::exact(255));
    }
}
