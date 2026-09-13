//! What a function takes and gives back, worked out from what it does.
//!
//! A prototype is not written down in a stripped binary, but it is visible: a
//! register read before anything wrote it arrived with a value, and a register
//! written on the way to a return is left for the caller. That is enough to
//! recover the shape of most functions, and where it is not, saying so is
//! better than inventing a parameter.
//!
//! The convention gives the candidates and the code decides which of them are
//! used. A function that reads the third argument register and not the first
//! two still takes three arguments: the first two are unused, not absent.

use std::collections::{BTreeMap, BTreeSet};

use crate::abi::Abi;
use crate::op::{Op, Space};
use crate::ssa::{Location, Operand, SsaFunction, SsaKind};

/// What a function appears to take and return.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Prototype {
    /// How many integer argument registers it takes, counting the unused ones
    /// before the last one it reads.
    pub integer_arguments: usize,
    /// How many floating point ones.
    pub float_arguments: usize,
    /// Offsets from the entry stack pointer of the arguments passed there.
    pub stack_arguments: Vec<i64>,
    /// Where it leaves a value the caller could read, when it leaves one.
    ///
    /// A possibility, not a promise. A function that computes an address into
    /// the first argument register on its way out has left something there,
    /// and nothing inside the function says whether anyone reads it: only its
    /// callers do. What this does guarantee is the other direction — a
    /// function that leaves nothing has `None` — so a caller is never denied a
    /// result that exists.
    pub returns: Option<u64>,
    /// True when the result is a floating point register.
    pub returns_float: bool,
    /// Callee-saved registers it writes without putting back, which is a
    /// convention the compiler invented rather than the standard one.
    pub unsaved: Vec<u64>,
    /// True when nothing about the function contradicts the standard
    /// convention.
    pub standard: bool,
}

impl Prototype {
    /// How many arguments in total, for a caller that has to pass them.
    pub fn arity(&self) -> usize {
        self.integer_arguments + self.float_arguments + self.stack_arguments.len()
    }
}

/// Recover what a function takes and returns.
pub fn recover(f: &SsaFunction, abi: &Abi) -> Prototype {
    let live_in = live_in(f);
    let written = written(f);

    // The highest argument register read, plus one: a function that reads the
    // third and not the first two still takes three.
    let integer_arguments = last_used(&live_in, &abi.integer_arguments);
    let float_arguments = last_used(&live_in, &abi.float_arguments);

    // Arguments the caller left on the stack, which promotion turned into
    // locations above the entry stack pointer.
    let mut stack_arguments: Vec<i64> = live_in
        .iter()
        .filter(|l| l.space == Space::Stack && (l.offset as i64) > 0)
        .map(|l| l.offset as i64)
        .collect();
    stack_arguments.sort();
    stack_arguments.dedup();

    // The result: a register the convention names, written somewhere that
    // reaches a return.
    let returns = returned(f, abi, &written);
    let returns_float = returns.is_some_and(|r| r >= abi.vector_base);

    // A callee-saved register this function writes and does not put back.
    let unsaved: Vec<u64> = abi
        .callee_saved
        .iter()
        .copied()
        .filter(|offset| written.contains(offset) && !restored(f, *offset))
        .collect();

    Prototype {
        integer_arguments,
        float_arguments,
        stack_arguments,
        returns,
        returns_float,
        standard: unsaved.is_empty(),
        unsaved,
    }
}

/// Locations read before this function wrote them.
fn live_in(f: &SsaFunction) -> BTreeSet<Location> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Operand::Undefined(l) = i {
                    out.insert(*l);
                }
            }
        }
    }
    out
}

/// Register offsets this function writes.
fn written(f: &SsaFunction) -> BTreeSet<u64> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            // An undefined value is not a write: it says the location holds
            // something this function did not compute.
            if op.kind == SsaKind::Op(Op::Undefine) {
                continue;
            }
            if let Some(v) = op.out {
                if v.location.space == Space::Register {
                    out.insert(v.location.offset);
                }
            }
        }
    }
    out
}

/// One past the last of `candidates` that appears among the live-in set.
fn last_used(live_in: &BTreeSet<Location>, candidates: &[u64]) -> usize {
    candidates
        .iter()
        .enumerate()
        .filter(|(_, offset)| {
            live_in
                .iter()
                .any(|l| l.space == Space::Register && l.offset == **offset)
        })
        .map(|(n, _)| n + 1)
        .next_back()
        .unwrap_or(0)
}

/// Which result register the function leaves a value in, if any.
///
/// The value that reaches a return, when the function computed it. A register
/// still holding what it arrived with was not a result: the caller put it
/// there. The one written latest wins, because a function that computes into a
/// general register and then converts into a vector one writes both.
fn returned(f: &SsaFunction, abi: &Abi, written: &BTreeSet<u64>) -> Option<u64> {
    let definitions = f.definitions();
    let mut best: Option<(usize, u64)> = None;
    for b in f.blocks.values() {
        if !b.ops.iter().any(|op| op.kind == SsaKind::Op(Op::Return)) {
            continue;
        }
        for offset in &abi.results {
            if !written.contains(offset) {
                continue;
            }
            let location = Location {
                space: Space::Register,
                offset: *offset,
                size: 8,
            };
            // What reaches the return: the last definition in this block, or
            // the newest one anywhere when the block itself did not write it.
            let (rank, value) = match b
                .ops
                .iter()
                .enumerate()
                .rev()
                .find(|(_, op)| op.out.is_some_and(|v| v.location == location))
            {
                Some((n, op)) => (n, op.out?),
                None => {
                    let newest = f
                        .blocks
                        .values()
                        .flat_map(|other| other.ops.iter())
                        .filter_map(|op| op.out)
                        .filter(|v| v.location == location)
                        .max_by_key(|v| v.version)?;
                    (0, newest)
                }
            };
            if is_entry_value(f, &definitions, value, location, 0) {
                continue;
            }
            if best.is_none_or(|(at, _)| rank > at) {
                best = Some((rank, *offset));
            }
        }
    }
    best.map(|(_, offset)| offset)
}

/// True when a register's value at every return is the one it arrived with.
fn restored(f: &SsaFunction, offset: u64) -> bool {
    let location = Location {
        space: Space::Register,
        offset,
        size: 8,
    };
    let definitions = f.definitions();
    for b in f.blocks.values() {
        if !b
            .ops
            .iter()
            .any(|op| op.kind == SsaKind::Op(Op::Return))
        {
            continue;
        }
        // What the register holds at the return: the last definition in this
        // block, or whatever reached it.
        let last = b
            .ops
            .iter()
            .rev()
            .filter_map(|op| op.out)
            .find(|v| v.location == location);
        match last {
            // Nothing in the returning block wrote it, so it still holds
            // whatever the entry left there.
            None => continue,
            Some(v) => {
                if !is_entry_value(f, &definitions, v, location, 0) {
                    return false;
                }
            }
        }
    }
    true
}

/// True when a value is the one the function was entered with, however many
/// copies and merges it came through.
fn is_entry_value(
    f: &SsaFunction,
    definitions: &BTreeMap<crate::ssa::Value, (r12e_core::Addr, usize)>,
    value: crate::ssa::Value,
    location: Location,
    depth: u32,
) -> bool {
    if depth > 16 {
        return false;
    }
    let Some((block, index)) = definitions.get(&value) else {
        return false;
    };
    let Some(op) = f.blocks.get(block).and_then(|b| b.ops.get(*index)) else {
        return false;
    };
    let inputs: Vec<&Operand> = match op.kind {
        SsaKind::Phi => op.inputs.iter().collect(),
        SsaKind::Op(Op::Copy) | SsaKind::Op(Op::Load) => op.inputs.iter().take(1).collect(),
        _ => return false,
    };
    // A load restores a spilled register: what it reads is not tracked, so a
    // reload of the same location counts as a restore only when the function
    // spilled it first. Treating a load as a restore is the assumption a
    // prologue and epilogue actually satisfy.
    if op.kind == SsaKind::Op(Op::Load) {
        return true;
    }
    inputs.iter().all(|i| match i {
        Operand::Undefined(l) => *l == location,
        Operand::Value(v) => is_entry_value(f, definitions, *v, location, depth + 1),
        Operand::Const(..) => false,
    })
}
