//! Turning stack slots into variables.
//!
//! A compiler spills a local to the stack and reloads it; lifting that
//! faithfully gives a store and a load through an address that is the stack
//! pointer plus a constant. Left alone, every local in the output reads as
//! `*(uint64_t *)(sp - 16 + 12)`, which is what the machine does and not what
//! anyone wrote.
//!
//! This pass finds the accesses whose address is a known offset from the stack
//! pointer on entry and rewrites them into reads and writes of a slot, which
//! SSA construction then treats like any other location. The result is a
//! variable.
//!
//! It refuses whenever it cannot prove the rewrite is safe. If any stack
//! address is used as a value — passed to a call, stored somewhere, computed
//! into — then something may read the slot through a pointer and promoting it
//! would lose that write. If two slots overlap without being identical, the
//! same. A refusal costs readability; a wrong promotion costs correctness.

use std::collections::{BTreeMap, BTreeSet};

use r12e_core::Addr;

use crate::abi;
use crate::func::Function;
use crate::op::{IrOp, Op, Space, Varnode};

/// What a pass changed.
#[derive(Debug, Clone, Copy, Default)]
pub struct Promoted {
    /// Accesses rewritten into slot reads and writes.
    pub accesses: usize,
    /// Distinct slots created.
    pub slots: usize,
}

/// A value's offset from the stack pointer on entry, when it has one.
type Offsets = BTreeMap<Varnode, i64>;

/// Promote the stack slots this function only ever reads and writes directly.
pub fn promote(f: &mut Function) -> Promoted {
    let sp = Varnode::register(abi::of(&f.arch).stack_pointer, 8);
    let order = f.reverse_postorder();

    // The stack offset each block starts with, which a function that pushes in
    // one block and pops in another needs.
    let mut entry_state: BTreeMap<Addr, Offsets> = BTreeMap::new();
    let mut initial = Offsets::new();
    initial.insert(sp, 0);
    entry_state.insert(f.entry, initial);

    let mut slots: BTreeMap<(i64, u8), usize> = BTreeMap::new();
    let mut escaped = false;

    // Two sweeps: the first settles the offsets at each block's entry, the
    // second records what is accessible and whether anything escapes.
    for _ in 0..4 {
        for at in &order {
            let Some(block) = f.blocks.get(at) else {
                continue;
            };
            let mut state = entry_state.get(at).cloned().unwrap_or_default();
            for op in &block.ops {
                step(op, sp, &mut state, &mut slots, &mut escaped);
            }
            for s in &block.successors {
                match entry_state.get(s) {
                    None => {
                        entry_state.insert(*s, state.clone());
                    }
                    Some(existing) => {
                        // Only what both paths agree on survives the merge.
                        let merged: Offsets = existing
                            .iter()
                            .filter(|(k, v)| state.get(*k) == Some(*v))
                            .map(|(k, v)| (*k, *v))
                            .collect();
                        if merged.len() != existing.len() {
                            entry_state.insert(*s, merged);
                        }
                    }
                }
            }
        }
    }

    if escaped || slots.is_empty() {
        return Promoted::default();
    }
    // Overlapping slots of different widths alias, and this pass has no way to
    // say that, so none of them are promoted.
    let keys: Vec<(i64, u8)> = slots.keys().copied().collect();
    let overlapping: BTreeSet<(i64, u8)> = keys
        .iter()
        .filter(|a| {
            keys.iter().any(|b| {
                *b != **a && a.0 < b.0 + b.1 as i64 && b.0 < a.0 + a.1 as i64
            })
        })
        .copied()
        .collect();

    // Rewrite.
    let mut changed = Promoted::default();
    let mut used: BTreeSet<(i64, u8)> = BTreeSet::new();
    for at in &order {
        let mut state = entry_state.get(at).cloned().unwrap_or_default();
        let Some(block) = f.blocks.get_mut(at) else {
            continue;
        };
        for op in &mut block.ops {
            let mut ignore = false;
            let before = state.clone();
            step(op, sp, &mut state, &mut BTreeMap::new(), &mut ignore);

            match op.op {
                Op::Load => {
                    let (Some(addr), Some(out)) = (op.input(0), op.out) else {
                        continue;
                    };
                    let Some(offset) = before.get(&addr).copied() else {
                        continue;
                    };
                    let key = (offset, out.size);
                    if overlapping.contains(&key) {
                        continue;
                    }
                    *op = IrOp::new(op.addr, Op::Copy, Some(out)).with(slot(key));
                    used.insert(key);
                    changed.accesses += 1;
                }
                Op::Store => {
                    let (Some(addr), Some(value)) = (op.input(0), op.input(1)) else {
                        continue;
                    };
                    let Some(offset) = before.get(&addr).copied() else {
                        continue;
                    };
                    let key = (offset, value.size);
                    if overlapping.contains(&key) {
                        continue;
                    }
                    *op = IrOp::new(op.addr, Op::Copy, Some(slot(key))).with(value);
                    used.insert(key);
                    changed.accesses += 1;
                }
                _ => {}
            }
        }
    }
    changed.slots = used.len();
    changed
}

/// The varnode a slot lives in. Negative offsets are the usual case, so the
/// offset is stored as its two's complement pattern.
fn slot((offset, size): (i64, u8)) -> Varnode {
    Varnode {
        space: Space::Stack,
        offset: offset as u64,
        size,
    }
}

/// Follow one operation's effect on what is known about the stack pointer.
fn step(
    op: &IrOp,
    sp: Varnode,
    state: &mut Offsets,
    slots: &mut BTreeMap<(i64, u8), usize>,
    escaped: &mut bool,
) {
    // An address used as anything but an address means the slot could be read
    // through a pointer, and nothing can be promoted.
    let tracked = |v: Varnode, state: &Offsets| state.contains_key(&v);
    match op.op {
        Op::Load => {
            if let (Some(addr), Some(out)) = (op.input(0), op.out) {
                if let Some(offset) = state.get(&addr).copied() {
                    *slots.entry((offset, out.size)).or_default() += 1;
                }
                // A loaded value is not a stack address any more.
                state.remove(&out);
            }
        }
        Op::Store => {
            if let (Some(addr), Some(value)) = (op.input(0), op.input(1)) {
                if let Some(offset) = state.get(&addr).copied() {
                    *slots.entry((offset, value.size)).or_default() += 1;
                }
                // Storing an address puts it somewhere this pass cannot see.
                if tracked(value, state) {
                    *escaped = true;
                }
            }
        }
        Op::Copy => {
            if let (Some(src), Some(out)) = (op.input(0), op.out) {
                match state.get(&src).copied() {
                    Some(offset) if out.size == 8 => {
                        state.insert(out, offset);
                    }
                    _ => {
                        state.remove(&out);
                    }
                }
            }
        }
        Op::IntAdd | Op::IntSub => {
            let (Some(a), Some(b), Some(out)) = (op.input(0), op.input(1), op.out) else {
                return;
            };
            let base = state.get(&a).copied();
            match (base, b.value()) {
                (Some(offset), Some(k)) if out.size == 8 => {
                    let delta = k as i64;
                    let next = if op.op == Op::IntAdd {
                        offset.wrapping_add(delta)
                    } else {
                        offset.wrapping_sub(delta)
                    };
                    state.insert(out, next);
                }
                _ => {
                    // A stack address combined with something unknown is an
                    // address this pass cannot follow.
                    if base.is_some() || tracked(b, state) {
                        *escaped = true;
                    }
                    state.remove(&out);
                }
            }
        }
        _ => {
            for i in op.inputs() {
                if tracked(*i, state) && *i != sp {
                    *escaped = true;
                }
            }
            if let Some(out) = op.out {
                state.remove(&out);
            }
        }
    }
}
