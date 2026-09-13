//! Basic blocks and the control flow graph of one function.
//!
//! Built by recursive descent from the entry: decode, follow every direct
//! successor, stop at a return, a trap, or an unresolved indirect branch.
//! Blocks split when a later branch lands inside one already walked, which is
//! why the walk records instruction starts rather than assuming them.

use std::collections::{BTreeMap, BTreeSet};

use r12e_arch::{Flow, Insn};
use r12e_core::{Addr, AddrRange, Arch, Caps, MemoryMap};

/// One straight-line run of instructions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    /// Addresses the block covers.
    pub range: AddrRange,
    /// Where control can go next, sorted and deduplicated.
    pub successors: Vec<Addr>,
    /// How many instructions it holds.
    pub insns: u32,
    /// True when the block ends somewhere analysis could not follow.
    pub unresolved: bool,
}

/// Why a walk stopped before it ran out of work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Halt {
    /// Everything reachable was walked.
    Complete,
    /// An instruction cap was reached.
    InstructionCap,
    /// A block cap was reached.
    BlockCap,
    /// Bytes ran out, or an encoding was not decodable.
    Undecodable,
}

/// The control flow graph of one function.
#[derive(Debug, Clone)]
pub struct Cfg {
    /// Where the function starts.
    pub entry: Addr,
    /// Blocks by start address.
    pub blocks: BTreeMap<Addr, Block>,
    /// Direct call targets found inside, sorted and deduplicated.
    pub calls: Vec<Addr>,
    /// Addresses reached by an indirect branch we could not resolve.
    pub has_indirect: bool,
    /// Why the walk ended.
    pub halt: Halt,
}

impl Cfg {
    /// The span from the lowest to the highest byte the function covers.
    ///
    /// A hull, not a claim of contiguity: a compiler can put a cold path far
    /// from the hot one, and the hull says so rather than hiding it.
    pub fn hull(&self) -> AddrRange {
        let lo = self.blocks.keys().next().copied().unwrap_or(self.entry);
        let hi = self
            .blocks
            .values()
            .map(|b| b.range.end())
            .max()
            .unwrap_or(lo);
        AddrRange::new(lo, hi).unwrap_or(AddrRange::empty_at(lo))
    }

    /// Total bytes actually covered by blocks, which is under the hull when the
    /// function is split.
    pub fn covered_bytes(&self) -> u64 {
        self.blocks.values().map(|b| b.range.len()).sum()
    }

    /// Instructions in the whole function.
    pub fn insns(&self) -> u32 {
        self.blocks.values().map(|b| b.insns).sum()
    }

    /// True when the function was walked to the end with nothing unresolved.
    pub fn is_complete(&self) -> bool {
        self.halt == Halt::Complete && !self.has_indirect
    }
}

/// Walk one function from `entry`.
///
/// `stop_at` holds the entries of other known functions: reaching one means a
/// tail call, not a continuation, which is the single most common way a
/// disassembler runs two functions together.
pub fn build(
    mem: &MemoryMap,
    arch: &Arch,
    entry: Addr,
    stop_at: &BTreeSet<Addr>,
    caps: &Caps,
) -> Cfg {
    let mut starts: BTreeSet<Addr> = BTreeSet::new();
    let mut work: Vec<Addr> = vec![entry];
    let mut seen: BTreeSet<Addr> = BTreeSet::new();
    let mut calls: BTreeSet<Addr> = BTreeSet::new();
    let mut ends: BTreeMap<Addr, (Addr, Vec<Addr>, u32, bool)> = BTreeMap::new();
    let mut has_indirect = false;
    let mut insn_budget = caps.function_insns;
    let mut halt = Halt::Complete;

    while let Some(start) = work.pop() {
        if !seen.insert(start) {
            continue;
        }
        if ends.len() as u64 >= caps.function_blocks {
            halt = Halt::BlockCap;
            break;
        }
        starts.insert(start);

        let mut at = start;
        let mut count = 0u32;
        // One past the last instruction decoded, which is where the block ends.
        let mut end = start;
        let (succs, unresolved) = loop {
            if insn_budget == 0 {
                halt = Halt::InstructionCap;
                break (Vec::new(), true);
            }
            // A branch into the middle of this run means the run ends here and
            // a new block starts, so stop as soon as we reach a known start.
            if at != start && starts.contains(&at) {
                break (vec![at], false);
            }
            let Some(window) = mem.decode_window(at, arch.max_insn_len()) else {
                halt = Halt::Undecodable;
                break (Vec::new(), true);
            };
            let Some(insn) = r12e_arch::decode(arch, window, at) else {
                halt = Halt::Undecodable;
                break (Vec::new(), true);
            };
            insn_budget -= 1;
            count += 1;
            let next = insn.next();
            end = next;

            match insn.flow {
                Flow::Next => {
                    at = next;
                    continue;
                }
                Flow::Call(t) => {
                    calls.insert(t);
                    at = next;
                    continue;
                }
                Flow::IndirectCall | Flow::Syscall => {
                    at = next;
                    continue;
                }
                Flow::Return | Flow::Trap => break (Vec::new(), false),
                Flow::IndirectBranch => {
                    has_indirect = true;
                    break (Vec::new(), true);
                }
                Flow::Branch(t) => {
                    // A branch to another function's entry is a tail call.
                    if stop_at.contains(&t) && t != entry {
                        calls.insert(t);
                        break (Vec::new(), false);
                    }
                    break (vec![t], false);
                }
                Flow::CondBranch(t) => {
                    if stop_at.contains(&t) && t != entry {
                        calls.insert(t);
                        break (vec![next], false);
                    }
                    break (vec![t, next], false);
                }
            }
        };

        let mut s = succs.clone();
        s.sort_unstable();
        s.dedup();
        ends.insert(start, (end, s.clone(), count, unresolved));

        for t in s {
            if !seen.contains(&t) && mem.is_executable(t) {
                work.push(t);
            }
        }
    }

    // Split blocks whose range covers another block's start. A conditional
    // branch backwards into a run already walked is the usual cause.
    let mut blocks: BTreeMap<Addr, Block> = BTreeMap::new();
    for (start, (end, succs, insns, unresolved)) in &ends {
        // An empty block has nothing to cut, and an excluded range whose
        // bounds are equal is a panic rather than an empty iterator.
        let cut = if *end > *start {
            starts
                .range((
                    std::ops::Bound::Excluded(*start),
                    std::ops::Bound::Excluded(*end),
                ))
                .next()
                .copied()
        } else {
            None
        };
        let (real_end, real_succs, real_unresolved) = match cut {
            Some(c) => (c, vec![c], false),
            None => (*end, succs.clone(), *unresolved),
        };
        let Some(range) = AddrRange::new(*start, real_end) else {
            continue;
        };
        if range.is_empty() {
            continue;
        }
        blocks.insert(
            *start,
            Block {
                range,
                successors: real_succs,
                insns: if cut.is_some() { 0 } else { *insns },
                unresolved: real_unresolved,
            },
        );
    }
    // Recount instructions in any block that was cut.
    for (start, b) in blocks.iter_mut() {
        if b.insns == 0 {
            b.insns = count_insns(mem, arch, *start, b.range.end());
        }
    }

    Cfg {
        entry,
        blocks,
        calls: calls.into_iter().collect(),
        has_indirect,
        halt,
    }
}

fn count_insns(mem: &MemoryMap, arch: &Arch, start: Addr, end: Addr) -> u32 {
    let mut at = start;
    let mut n = 0;
    while at < end {
        let Some(w) = mem.decode_window(at, arch.max_insn_len()) else {
            break;
        };
        let Some(i) = r12e_arch::decode(arch, w, at) else {
            break;
        };
        at = i.next();
        n += 1;
    }
    n
}

/// Decode every instruction of a function in address order.
///
/// Walks the blocks rather than the whole hull, so bytes between a function's
/// split parts are not mistaken for its code.
pub fn instructions(mem: &MemoryMap, arch: &Arch, cfg: &Cfg) -> Vec<Insn> {
    let mut out = Vec::with_capacity(cfg.insns() as usize);
    for b in cfg.blocks.values() {
        let mut at = b.range.start();
        while at < b.range.end() {
            let Some(w) = mem.decode_window(at, arch.max_insn_len()) else {
                break;
            };
            let Some(i) = r12e_arch::decode(arch, w, at) else {
                break;
            };
            at = i.next();
            out.push(i);
        }
    }
    out.sort_by_key(|i| i.addr);
    out
}
