//! What a pointer points at, inferred from how it is used.
//!
//! A function that takes a pointer and reads four bytes at offset zero, four
//! at offset four and eight at offset eight is being handed a structure with
//! three fields, and the code says so whether or not the binary carries debug
//! information. This pass collects those accesses and reports them; naming the
//! fields is a person's job, and inventing names for them would be a claim.
//!
//! It reports what it saw, not what it concluded. An access through a pointer
//! that was itself loaded from memory is not attributed to the original, and a
//! stride that two accesses disagree about is recorded as two strides rather
//! than averaged into one.

use std::collections::{BTreeMap, BTreeSet};

use crate::op::{Op, Space};
use crate::ssa::{Location, Operand, SsaFunction, SsaKind, Value};

/// One access through a pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Access {
    /// Byte offset from the pointer.
    pub offset: i64,
    /// How many bytes were touched.
    pub size: u8,
    /// True when the access wrote.
    pub write: bool,
}

/// What was seen through one pointer.
#[derive(Debug, Clone, Default)]
pub struct Shape {
    /// The accesses, deduplicated and in offset order.
    pub accesses: BTreeSet<Access>,
    /// Strides an index was scaled by, which is the size of the element when
    /// the pointer walks an array.
    pub strides: BTreeSet<u64>,
}

impl Shape {
    /// The fields this implies: one per distinct offset, at the widest access
    /// seen there.
    pub fn fields(&self) -> Vec<(i64, u8)> {
        let mut widest: BTreeMap<i64, u8> = BTreeMap::new();
        for a in &self.accesses {
            let entry = widest.entry(a.offset).or_insert(a.size);
            *entry = (*entry).max(a.size);
        }
        widest.into_iter().collect()
    }

    /// The size the accesses imply, which is the stride when there is one and
    /// otherwise the end of the last field.
    pub fn size(&self) -> Option<u64> {
        if let Some(stride) = self.strides.iter().next_back() {
            return Some(*stride);
        }
        let (offset, size) = self.fields().into_iter().next_back()?;
        (offset >= 0).then_some(offset as u64 + size as u64)
    }
}

/// Everything seen through each pointer that arrived from outside.
pub fn shapes(f: &SsaFunction) -> BTreeMap<Location, Shape> {
    let mut out: BTreeMap<Location, Shape> = BTreeMap::new();
    let defs = f.definitions();

    for b in f.blocks.values() {
        for op in &b.ops {
            let SsaKind::Op(o) = op.kind else { continue };
            let (address, size, write) = match o {
                Op::Load => (op.inputs.first(), op.size, false),
                Op::Store => (
                    op.inputs.first(),
                    op.inputs.get(1).map(|i| i.size()).unwrap_or(0),
                    true,
                ),
                _ => continue,
            };
            let Some(address) = address else { continue };
            let Some(walk) = base_of(f, &defs, address, 0) else {
                continue;
            };
            // Only pointers that arrived from outside: anything computed here
            // is already described by whatever produced it.
            let Some(location) = walk.base else { continue };
            let shape = out.entry(location).or_default();
            shape.accesses.insert(Access {
                offset: walk.offset,
                size,
                write,
            });
            shape.strides.extend(walk.strides);
        }
    }
    out
}

/// What an address expression resolves to.
struct Walk {
    /// The incoming value it is measured from, when there is one.
    base: Option<Location>,
    /// The constant part.
    offset: i64,
    /// Scales an index was multiplied by on the way.
    strides: Vec<u64>,
}

/// Unwind an address into a base, a constant offset and any strides.
fn base_of(
    f: &SsaFunction,
    defs: &BTreeMap<Value, (r12e_core::Addr, usize)>,
    operand: &Operand,
    depth: u32,
) -> Option<Walk> {
    if depth > 16 {
        return None;
    }
    match operand {
        Operand::Undefined(l) if l.space == Space::Register => Some(Walk {
            base: Some(*l),
            offset: 0,
            strides: Vec::new(),
        }),
        Operand::Undefined(_) | Operand::Const(..) => None,
        Operand::Value(v) => {
            let (block, index) = defs.get(v)?;
            let op = f.blocks.get(block)?.ops.get(*index)?;
            // A pointer the loop advances arrives as a phi: one input is where
            // it started and the other is itself plus a step. The base is the
            // start, and the step is the size of what it walks.
            if op.kind == SsaKind::Phi {
                let mut base: Option<Walk> = None;
                let mut strides: Vec<u64> = Vec::new();
                for input in &op.inputs {
                    if let Some(step) = step_around(f, defs, input, *v) {
                        strides.push(step);
                        continue;
                    }
                    let w = base_of(f, defs, input, depth + 1)?;
                    match &base {
                        // Two different starting points is two pointers, and
                        // saying which was accessed would be a guess.
                        Some(existing) if existing.base != w.base => return None,
                        Some(_) => {}
                        None => base = Some(w),
                    }
                }
                let mut walk = base?;
                walk.strides.extend(strides);
                return Some(walk);
            }
            let SsaKind::Op(o) = op.kind else { return None };
            match o {
                Op::Copy | Op::IntZExt | Op::IntSExt => {
                    base_of(f, defs, op.inputs.first()?, depth + 1)
                }
                Op::IntAdd | Op::IntSub => {
                    let (a, b) = (op.inputs.first()?, op.inputs.get(1)?);
                    let sign = if o == Op::IntSub { -1 } else { 1 };
                    // One side is the pointer, the other the displacement.
                    if let Some(k) = b.as_const() {
                        let mut walk = base_of(f, defs, a, depth + 1)?;
                        walk.offset += sign * k as i64;
                        return Some(walk);
                    }
                    if let Some(k) = a.as_const() {
                        let mut walk = base_of(f, defs, b, depth + 1)?;
                        walk.offset += k as i64;
                        return Some(walk);
                    }
                    // Neither is constant: one side is the base and the other
                    // a scaled index, whose stride says how big an element is.
                    let left = base_of(f, defs, a, depth + 1);
                    let right = base_of(f, defs, b, depth + 1);
                    let strides = stride_of(f, defs, a, 0)
                        .into_iter()
                        .chain(stride_of(f, defs, b, 0))
                        .collect::<Vec<_>>();
                    match (left, right) {
                        (Some(mut w), None) | (None, Some(mut w)) => {
                            w.strides.extend(strides);
                            Some(w)
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
    }
}

/// The constant a value adds to `phi` on its way back round, when it is the
/// phi's own increment rather than a separate pointer.
fn step_around(
    f: &SsaFunction,
    defs: &BTreeMap<Value, (r12e_core::Addr, usize)>,
    operand: &Operand,
    phi: Value,
) -> Option<u64> {
    let Operand::Value(v) = operand else {
        return None;
    };
    if *v == phi {
        return Some(0);
    }
    let (block, index) = defs.get(v)?;
    let op = f.blocks.get(block)?.ops.get(*index)?;
    let SsaKind::Op(Op::IntAdd) = op.kind else {
        return None;
    };
    let (a, b) = (op.inputs.first()?, op.inputs.get(1)?);
    let step = b.as_const().or_else(|| a.as_const())?;
    let other = if b.as_const().is_some() { a } else { b };
    (other.as_value() == Some(phi)).then_some(step)
}

/// The scale an index was multiplied by, when it was.
fn stride_of(
    f: &SsaFunction,
    defs: &BTreeMap<Value, (r12e_core::Addr, usize)>,
    operand: &Operand,
    depth: u32,
) -> Option<u64> {
    if depth > 8 {
        return None;
    }
    let Operand::Value(v) = operand else {
        return None;
    };
    let (block, index) = defs.get(v)?;
    let op = f.blocks.get(block)?.ops.get(*index)?;
    let SsaKind::Op(o) = op.kind else { return None };
    match o {
        Op::IntLeft => op.inputs.get(1)?.as_const().map(|n| 1u64 << n.min(31)),
        Op::IntMul => op.inputs.get(1)?.as_const(),
        Op::Copy | Op::IntZExt | Op::IntSExt => stride_of(f, defs, op.inputs.first()?, depth + 1),
        _ => None,
    }
}
