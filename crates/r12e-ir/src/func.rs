//! A whole function's IR, as blocks in a graph.
//!
//! Built from the machine control flow graph by lifting each block's
//! instructions in order. The IR keeps the machine's block structure rather
//! than inventing its own, so every operation can still be traced to the
//! instruction it came from.

use std::collections::{BTreeMap, BTreeSet};

use r12e_arch::Insn;
use r12e_core::{Addr, Arch, MemoryMap};

use crate::lift;
use crate::op::{IrOp, Op};

/// One block of IR.
#[derive(Debug, Clone)]
pub struct Block {
    /// Where the block starts.
    pub addr: Addr,
    /// The operations, in order.
    pub ops: Vec<IrOp>,
    /// Blocks control can reach from here.
    pub successors: Vec<Addr>,
    /// Blocks that can reach here.
    pub predecessors: Vec<Addr>,
}

/// A function's IR.
#[derive(Debug, Clone)]
pub struct Function {
    /// Where the function starts.
    pub entry: Addr,
    /// Blocks by start address.
    pub blocks: BTreeMap<Addr, Block>,
    /// Instructions the lifter did not model.
    pub unlifted: Vec<Addr>,
}

impl Function {
    /// Blocks in reverse post-order from the entry, which is the order every
    /// forward dataflow pass wants.
    pub fn reverse_postorder(&self) -> Vec<Addr> {
        let mut seen = BTreeSet::new();
        let mut post = Vec::new();
        // An explicit stack rather than recursion: a function with ten
        // thousand blocks would overflow one.
        let mut stack = vec![(self.entry, 0usize)];
        seen.insert(self.entry);
        while let Some((at, i)) = stack.pop() {
            let Some(b) = self.blocks.get(&at) else {
                continue;
            };
            if i < b.successors.len() {
                stack.push((at, i + 1));
                let next = b.successors[i];
                if self.blocks.contains_key(&next) && seen.insert(next) {
                    stack.push((next, 0));
                }
            } else {
                post.push(at);
            }
        }
        post.reverse();
        post
    }

    /// How many operations the function holds.
    pub fn op_count(&self) -> usize {
        self.blocks.values().map(|b| b.ops.len()).sum()
    }

    /// True when every instruction was modelled.
    pub fn is_complete(&self) -> bool {
        self.unlifted.is_empty()
    }
}

/// Lift a function, given its machine blocks.
///
/// `blocks` maps each block's start to its address range and its successors,
/// which is what the analysis crate's control flow graph already holds.
pub fn build(
    mem: &MemoryMap,
    arch: &Arch,
    entry: Addr,
    blocks: &BTreeMap<Addr, (Addr, Vec<Addr>)>,
) -> Function {
    let mut out: BTreeMap<Addr, Block> = BTreeMap::new();
    let mut unlifted = Vec::new();

    for (start, (end, succs)) in blocks {
        let mut ops = Vec::new();
        let mut at = *start;
        while at < *end {
            let Some(window) = mem.decode_window(at, arch.max_insn_len()) else {
                break;
            };
            let Some(insn) = r12e_arch::decode(arch, window, at) else {
                break;
            };
            let lifted = lift::lift(arch, &insn);
            if !lifted.complete {
                unlifted.push(at);
            }
            // Temporaries are numbered per instruction, so they are renamed to
            // be unique within the block before being appended.
            let base = ops.len() as u64 * crate::lift::MAX_TEMPS;
            ops.extend(lifted.ops.iter().map(|o| rebase_temps(*o, base)));
            at = insn.next();
        }
        out.insert(
            *start,
            Block {
                addr: *start,
                ops,
                successors: succs.clone(),
                predecessors: Vec::new(),
            },
        );
    }

    // Predecessors, derived rather than stored twice.
    let edges: Vec<(Addr, Addr)> = out
        .iter()
        .flat_map(|(a, b)| b.successors.iter().map(move |s| (*a, *s)))
        .collect();
    for (from, to) in edges {
        if let Some(b) = out.get_mut(&to) {
            if !b.predecessors.contains(&from) {
                b.predecessors.push(from);
            }
        }
    }

    Function {
        entry,
        blocks: out,
        unlifted,
    }
}

/// Shift an operation's temporaries so they do not collide with another
/// instruction's.
fn rebase_temps(mut op: IrOp, base: u64) -> IrOp {
    if let Some(o) = op.out.as_mut() {
        if o.space == crate::op::Space::Unique {
            o.offset += base;
        }
    }
    op.map_inputs(|v| {
        if v.space == crate::op::Space::Unique {
            crate::op::Varnode {
                offset: v.offset + base,
                ..v
            }
        } else {
            v
        }
    });
    op
}

/// Decode one instruction, for a caller that wants the machine view too.
pub fn decode_at(mem: &MemoryMap, arch: &Arch, at: Addr) -> Option<Insn> {
    let window = mem.decode_window(at, arch.max_insn_len())?;
    r12e_arch::decode(arch, window, at)
}

/// True when the operation ends a block.
pub fn terminates(op: &IrOp) -> bool {
    op.op.is_branch() || op.op == Op::Unimplemented
}
