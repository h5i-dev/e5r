//! Basic blocks and the control flow graph of one function.
//!
//! Built by recursive descent from the entry: decode, follow every direct
//! successor, stop at a return, a trap, or an unresolved indirect branch.
//! Blocks split when a later branch lands inside one already walked, which is
//! why the walk records instruction starts rather than assuming them.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use r12e_arch::{Flow, Insn};
use r12e_core::{Addr, AddrRange, Arch, Caps, MemoryMap};

use crate::data::DataMap;
use crate::jumptable::{self, JumpTable};

/// Why a block ended, which is what tells a returning function from one that
/// never comes back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Terminator {
    /// A branch, conditional or not, or a fall-through into another block.
    Flow,
    /// A return to the caller.
    Return,
    /// A tail call: the callee returns on this function's behalf.
    TailCall,
    /// A call to a function that never returns.
    NoReturnCall,
    /// A breakpoint or an undefined instruction.
    Trap,
    /// An indirect branch nothing resolved, or bytes that did not decode.
    Unresolved,
}

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
    /// Why it ended.
    pub terminator: Terminator,
}

/// Where one block sits in the program-wide table.
pub type BlockId = u32;

/// A block and the address it starts at, which is the key every consumer knows
/// it by. Kept beside the block because a consumer iterating a function wants
/// `(&Addr, &Block)` and an `AddrRange` cannot lend out its start.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Entry {
    at: Addr,
    block: Block,
}

/// Every distinct basic block of one program, held once.
///
/// A C++ binary's shared landing pads and cold paths are branch targets that
/// no symbol names, so every function that can reach one absorbs it
/// independently: on libLLVM, 8.47M blocks stored per function are 2.69M
/// distinct ones, and a block map held per function was 82% of the live bytes.
/// Functions name a block by id instead, which is 4 bytes against 84, and it
/// makes a C and a C++ binary cost the same per byte of code.
///
/// Chunked because the table grows while functions already built hold a
/// reference to it: a chunk is sealed once and never moves, and a snapshot is
/// the list of chunks that existed when it was taken. An id means the same
/// entry in every snapshot that is long enough to hold it.
#[derive(Debug, Default)]
pub struct BlockTable {
    chunks: Vec<Arc<Vec<Entry>>>,
    /// The first id in each chunk, so an id finds its chunk by binary search.
    starts: Vec<BlockId>,
}

impl BlockTable {
    fn entry(&self, id: BlockId) -> Option<&Entry> {
        let c = self.starts.partition_point(|s| *s <= id).checked_sub(1)?;
        self.chunks[c].get((id - self.starts[c]) as usize)
    }

    /// How many distinct blocks it holds.
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|c| c.len()).sum()
    }

    /// True when it holds none.
    pub fn is_empty(&self) -> bool {
        self.chunks.iter().all(|c| c.is_empty())
    }

    /// Every distinct block, once each, in the order they were first seen.
    pub fn blocks(&self) -> impl Iterator<Item = &Block> + '_ {
        self.chunks.iter().flat_map(|c| c.iter().map(|e| &e.block))
    }
}

/// The blocks of one function: ids into a table shared with every other
/// function, in address order.
///
/// Reads like the `BTreeMap<Addr, Block>` it replaces, which is what every
/// consumer in the workspace already asks for.
#[derive(Clone, Default)]
pub struct Blocks {
    table: Arc<BlockTable>,
    ids: Vec<BlockId>,
}

impl Blocks {
    /// How many blocks the function has.
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    /// True when the walk produced none.
    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    /// The block starting exactly at `at`.
    pub fn get(&self, at: &Addr) -> Option<&Block> {
        let pos = self
            .ids
            .partition_point(|id| self.table.entry(*id).is_some_and(|e| e.at < *at));
        let e = self.table.entry(*self.ids.get(pos)?)?;
        (e.at == *at).then_some(&e.block)
    }

    /// True when a block starts exactly at `at`.
    pub fn contains_key(&self, at: &Addr) -> bool {
        self.get(at).is_some()
    }

    /// Blocks with their start addresses, in address order.
    pub fn iter(&self) -> BlocksIter<'_> {
        BlocksIter {
            table: &self.table,
            ids: self.ids.iter(),
        }
    }

    /// The blocks, in address order.
    pub fn values(&self) -> impl Iterator<Item = &Block> + '_ {
        self.iter().map(|(_, b)| b)
    }

    /// The start addresses, in order.
    pub fn keys(&self) -> impl Iterator<Item = &Addr> + '_ {
        self.iter().map(|(a, _)| a)
    }

    /// The table these blocks are held in, which is shared with every other
    /// function of the same program.
    pub fn table(&self) -> &BlockTable {
        &self.table
    }
}

impl std::fmt::Debug for Blocks {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a> IntoIterator for &'a Blocks {
    type Item = (&'a Addr, &'a Block);
    type IntoIter = BlocksIter<'a>;

    fn into_iter(self) -> BlocksIter<'a> {
        self.iter()
    }
}

/// One function's blocks, in address order.
pub struct BlocksIter<'a> {
    table: &'a BlockTable,
    ids: std::slice::Iter<'a, BlockId>,
}

impl<'a> Iterator for BlocksIter<'a> {
    type Item = (&'a Addr, &'a Block);

    fn next(&mut self) -> Option<(&'a Addr, &'a Block)> {
        loop {
            let id = *self.ids.next()?;
            // An id with no entry cannot happen: a function only ever holds
            // ids from a snapshot that already contains them. Skipped rather
            // than unwrapped so a future caller cannot turn it into a panic.
            if let Some(e) = self.table.entry(id) {
                return Some((&e.at, &e.block));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.ids.len()))
    }
}

/// Empty slot in the interner's index.
const NO_ID: BlockId = BlockId::MAX;

/// Builds a [`BlockTable`], collapsing blocks that are identical.
///
/// Interning happens as each batch of walked functions is merged rather than
/// afterwards, because a pass over finished functions would have to hold the
/// duplicated form and the interned one at once, which is the peak the whole
/// exercise is trying to avoid.
///
/// The index is open addressing over ids rather than a `HashMap` keyed by the
/// block: a map would store every distinct block a second time as its own key,
/// which costs more than it saves.
pub(crate) struct BlockInterner {
    chunks: Vec<Arc<Vec<Entry>>>,
    starts: Vec<BlockId>,
    /// Entries interned since the last seal.
    open: Vec<Entry>,
    /// The first id in `open`.
    sealed: BlockId,
    slots: Vec<BlockId>,
    filled: usize,
    /// Handed to a function whose table is not published yet, so installing
    /// one costs no allocation.
    empty: Arc<BlockTable>,
}

impl Default for BlockInterner {
    fn default() -> BlockInterner {
        BlockInterner {
            chunks: Vec::new(),
            starts: Vec::new(),
            open: Vec::new(),
            sealed: 0,
            slots: vec![NO_ID; 1024],
            filled: 0,
            empty: Arc::new(BlockTable::default()),
        }
    }
}

impl BlockInterner {
    fn entry(&self, id: BlockId) -> Option<&Entry> {
        if id >= self.sealed {
            return self.open.get((id - self.sealed) as usize);
        }
        let c = self.starts.partition_point(|s| *s <= id).checked_sub(1)?;
        self.chunks[c].get((id - self.starts[c]) as usize)
    }

    fn intern(&mut self, at: Addr, block: Block) -> BlockId {
        if (self.filled + 1) * 4 >= self.slots.len() * 3 {
            self.grow();
        }
        let mask = self.slots.len() - 1;
        let mut i = hash_block(at, &block) as usize & mask;
        while self.slots[i] != NO_ID {
            let id = self.slots[i];
            if self
                .entry(id)
                .is_some_and(|e| e.at == at && e.block == block)
            {
                return id;
            }
            i = (i + 1) & mask;
        }
        let id = self.sealed + self.open.len() as BlockId;
        self.open.push(Entry { at, block });
        self.slots[i] = id;
        self.filled += 1;
        id
    }

    fn grow(&mut self) {
        let mut slots = vec![NO_ID; self.slots.len() * 2];
        let mask = slots.len() - 1;
        for old in std::mem::take(&mut self.slots) {
            if old == NO_ID {
                continue;
            }
            let Some(e) = self.entry(old) else { continue };
            let mut i = hash_block(e.at, &e.block) as usize & mask;
            while slots[i] != NO_ID {
                i = (i + 1) & mask;
            }
            slots[i] = old;
        }
        self.slots = slots;
    }

    /// Intern one walked function's blocks. The table it names is not
    /// published yet; [`BlockInterner::publish`] does that for a whole batch.
    pub(crate) fn install(&mut self, raw: RawCfg) -> Cfg {
        let ids = raw
            .blocks
            .into_iter()
            .map(|(at, b)| self.intern(at, b))
            .collect();
        Cfg {
            entry: raw.entry,
            blocks: Blocks {
                table: self.empty.clone(),
                ids,
            },
            calls: raw.calls,
            has_indirect: raw.has_indirect,
            tables: raw.tables,
            halt: raw.halt,
        }
    }

    /// Seal what has been interned and give it to these functions.
    ///
    /// Every function installed since the last call must be published before
    /// anything reads its blocks.
    pub(crate) fn publish<'a>(&mut self, cfgs: impl Iterator<Item = &'a mut Cfg>) {
        let table = self.seal();
        for c in cfgs {
            c.blocks.table = table.clone();
        }
    }

    fn seal(&mut self) -> Arc<BlockTable> {
        if !self.open.is_empty() {
            let mut chunk = std::mem::take(&mut self.open);
            // Sealed chunks are kept for the life of the program, so the
            // capacity a doubling push left over is worth one copy to return.
            chunk.shrink_to_fit();
            self.starts.push(self.sealed);
            self.sealed += chunk.len() as BlockId;
            self.chunks.push(Arc::new(chunk));
        }
        Arc::new(BlockTable {
            chunks: self.chunks.clone(),
            starts: self.starts.clone(),
        })
    }
}

/// A block's identity, for the interner's index.
///
/// FNV rather than the default hasher: this runs once per stored block, eight
/// million times on a large C++ binary, and SipHash over a block costs more
/// than the lookup it keys.
fn hash_block(at: Addr, b: &Block) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut mix = |v: u64| {
        h ^= v;
        h = h.wrapping_mul(0x100_0000_01b3);
    };
    mix(at.get());
    mix(b.range.end().get());
    mix(b.insns as u64);
    mix(b.unresolved as u64 | ((b.terminator as u64) << 1));
    for s in &b.successors {
        mix(s.get());
    }
    h
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

impl Halt {
    /// What to call it in a report.
    pub fn as_str(self) -> &'static str {
        match self {
            Halt::Complete => "complete",
            Halt::InstructionCap => "instruction cap",
            Halt::BlockCap => "block cap",
            Halt::Undecodable => "undecodable",
        }
    }
}

/// The control flow graph of one function.
#[derive(Debug, Clone)]
pub struct Cfg {
    /// Where the function starts.
    pub entry: Addr,
    /// Blocks by start address.
    pub blocks: Blocks,
    /// Direct call targets found inside, sorted and deduplicated.
    pub calls: Vec<Addr>,
    /// Addresses reached by an indirect branch we could not resolve.
    pub has_indirect: bool,
    /// Jump tables resolved inside this function.
    pub tables: Vec<JumpTable>,
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

/// A walked function before its blocks are interned.
///
/// The walk runs on every thread at once and interning is one shared table, so
/// the two are separate steps: a thread produces this, and the merge that
/// follows turns it into a [`Cfg`].
pub(crate) struct RawCfg {
    pub(crate) entry: Addr,
    /// Blocks with their start addresses, in address order.
    pub(crate) blocks: Vec<(Addr, Block)>,
    pub(crate) calls: Vec<Addr>,
    pub(crate) has_indirect: bool,
    pub(crate) tables: Vec<JumpTable>,
    pub(crate) halt: Halt,
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
    build_with(mem, arch, entry, stop_at, &BTreeSet::new(), caps)
}

/// As [`build`], told which functions never return.
///
/// A call to one of those ends the block: continuing past it walks into
/// whatever the compiler put next, which is usually a literal pool.
///
/// One function on its own gets a block table of its own. Discovery does not
/// go through here: it shares one table across the whole program, which is
/// where the interning pays.
pub fn build_with(
    mem: &MemoryMap,
    arch: &Arch,
    entry: Addr,
    stop_at: &BTreeSet<Addr>,
    noreturn: &BTreeSet<Addr>,
    caps: &Caps,
) -> Cfg {
    let raw = build_raw(
        mem,
        arch,
        entry,
        stop_at,
        noreturn,
        caps,
        &DataMap::default(),
    );
    let mut interner = BlockInterner::default();
    let mut cfg = interner.install(raw);
    interner.publish(std::iter::once(&mut cfg));
    cfg
}

/// The walk itself, leaving the blocks for a caller to intern.
pub(crate) fn build_raw(
    mem: &MemoryMap,
    arch: &Arch,
    entry: Addr,
    stop_at: &BTreeSet<Addr>,
    noreturn: &BTreeSet<Addr>,
    caps: &Caps,
    data: &DataMap,
) -> RawCfg {
    // The executable range the entry sits in bounds every jump table target:
    // a switch does not branch into another section.
    let section = mem
        .segment_at(entry)
        .map(|s| s.range)
        .unwrap_or(AddrRange::empty_at(entry));
    let mut starts: BTreeSet<Addr> = BTreeSet::new();
    let mut work: Vec<Addr> = vec![entry];
    let mut seen: BTreeSet<Addr> = BTreeSet::new();
    let mut calls: BTreeSet<Addr> = BTreeSet::new();
    let mut ends: BTreeMap<Addr, (Addr, Vec<Addr>, u32, bool, Terminator)> = BTreeMap::new();
    let mut has_indirect = false;
    let mut insn_budget = caps.function_insns;
    let mut halt = Halt::Complete;
    let mut tables: Vec<JumpTable> = Vec::new();
    // Kept per block so an indirect branch can be resolved against the blocks
    // that lead to it: the compare that bounds a switch is almost always in a
    // predecessor, not in the block that ends with the branch.
    let mut bodies: BTreeMap<Addr, Vec<Insn>> = BTreeMap::new();

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
        // Kept so an indirect branch can be resolved against what led to it.
        let mut body: Vec<Insn> = Vec::new();
        let mut term = Terminator::Flow;
        // Thumb's IT block makes the next few instructions conditional with
        // nothing in their own halfwords saying so, so the state has to be
        // carried from one decode to the next. It starts empty at every block:
        // an IT block is a straight run of at most four instructions, and
        // branching into the middle of one is unpredictable, so no block ever
        // begins inside another's.
        let mut it = r12e_arch::arm::ItState::default();
        let (succs, unresolved) = loop {
            if insn_budget == 0 {
                halt = Halt::InstructionCap;
                term = Terminator::Unresolved;
                break (Vec::new(), true);
            }
            // A branch into the middle of this run means the run ends here and
            // a new block starts, so stop as soon as we reach a known start.
            if at != start && starts.contains(&at) {
                break (vec![at], false);
            }
            // Bytes something proved are data. Decoding them produces
            // instructions that were never executed and a block that runs on
            // into whatever follows, so the walk stops here and says it did
            // not finish. Empty for the evidence-led rounds, which run before
            // anything has been proved.
            if !data.is_empty() && data.contains(at) {
                halt = Halt::Undecodable;
                term = Terminator::Unresolved;
                break (Vec::new(), true);
            }
            let Some(window) = mem.decode_window(at, arch.max_insn_len()) else {
                halt = Halt::Undecodable;
                term = Terminator::Unresolved;
                break (Vec::new(), true);
            };
            let Some(insn) = decode_stateful(arch, window, at, &mut it) else {
                halt = Halt::Undecodable;
                term = Terminator::Unresolved;
                break (Vec::new(), true);
            };
            insn_budget -= 1;
            count += 1;
            body.push(insn);
            let next = insn.next();
            end = next;

            match insn.flow {
                Flow::Next => {
                    at = next;
                    continue;
                }
                Flow::Call(t) => {
                    calls.insert(t);
                    if noreturn.contains(&t) {
                        term = Terminator::NoReturnCall;
                        break (Vec::new(), false);
                    }
                    at = next;
                    continue;
                }
                Flow::IndirectCall | Flow::Syscall => {
                    at = next;
                    continue;
                }
                Flow::Return => {
                    term = Terminator::Return;
                    break (Vec::new(), false);
                }
                Flow::Trap => {
                    term = Terminator::Trap;
                    break (Vec::new(), false);
                }
                Flow::IndirectBranch => {
                    // A switch: read the table rather than giving up.
                    let context = with_predecessors(&bodies, &ends, start, &body);
                    match jumptable::recover(&context, mem, section, caps, arch.insn_alignment()) {
                        Some(t) => {
                            let targets = t.targets.clone();
                            tables.push(t);
                            break (targets, false);
                        }
                        None => {
                            has_indirect = true;
                            term = Terminator::Unresolved;
                            break (Vec::new(), true);
                        }
                    }
                }
                Flow::Branch(t) => {
                    // A branch to another function's entry is a tail call.
                    if stop_at.contains(&t) && t != entry {
                        calls.insert(t);
                        term = if noreturn.contains(&t) {
                            Terminator::NoReturnCall
                        } else {
                            Terminator::TailCall
                        };
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
        ends.insert(start, (end, s.clone(), count, unresolved, term));
        bodies.insert(start, body);

        for t in s {
            if !seen.contains(&t) && mem.is_executable(t) {
                work.push(t);
            }
        }
    }

    // Split blocks whose range covers another block's start. A conditional
    // branch backwards into a run already walked is the usual cause.
    // A vector rather than a map: `ends` is a `BTreeMap`, so this fills in
    // address order already, and the blocks are about to be interned anyway.
    let mut blocks: Vec<(Addr, Block)> = Vec::with_capacity(ends.len());
    for (start, (end, succs, insns, unresolved, term)) in &ends {
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
        let (real_end, real_succs, real_unresolved, real_term) = match cut {
            Some(c) => (c, vec![c], false, Terminator::Flow),
            None => (*end, succs.clone(), *unresolved, *term),
        };
        let Some(range) = AddrRange::new(*start, real_end) else {
            continue;
        };
        if range.is_empty() {
            continue;
        }
        blocks.push((
            *start,
            Block {
                range,
                successors: real_succs,
                insns: if cut.is_some() { 0 } else { *insns },
                unresolved: real_unresolved,
                terminator: real_term,
            },
        ));
    }
    // Recount instructions in any block that was cut.
    for (start, b) in blocks.iter_mut() {
        if b.insns == 0 {
            b.insns = count_insns(mem, arch, *start, b.range.end());
        }
    }

    tables.sort_by_key(|t| t.at);
    RawCfg {
        entry,
        blocks,
        calls: calls.into_iter().collect(),
        has_indirect,
        tables,
        halt,
    }
}

/// The instructions of `block` preceded by those of the blocks that reach it.
///
/// Three levels is enough in practice: a compiler puts the bound check
/// immediately before the table setup, and going deeper mostly adds unrelated
/// comparisons that could size a table wrongly.
fn with_predecessors(
    bodies: &BTreeMap<Addr, Vec<Insn>>,
    ends: &BTreeMap<Addr, (Addr, Vec<Addr>, u32, bool, Terminator)>,
    block: Addr,
    body: &[Insn],
) -> Vec<Insn> {
    let mut chain: Vec<Addr> = Vec::new();
    let mut frontier = vec![block];
    for _ in 0..3 {
        let mut next = Vec::new();
        for target in &frontier {
            for (start, (_, succs, _, _, _)) in ends {
                if succs.contains(target) && !chain.contains(start) && *start != block {
                    chain.push(*start);
                    next.push(*start);
                }
            }
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
    }

    let mut out: Vec<Insn> = chain
        .iter()
        .filter_map(|a| bodies.get(a))
        .flatten()
        .copied()
        .collect();
    out.sort_by_key(|i| i.addr);
    out.extend_from_slice(body);
    out
}

/// How many instructions fit between two addresses.
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

/// Decode every instruction of a function and hand each one straight to `f`,
/// without building a list of them.
///
/// Returns false when an instruction arrived at a lower address than the one
/// before it, which can only happen if two blocks of the function overlap. A
/// caller that needs address order then has to fall back to [`instructions`],
/// which sorts. No binary in the corpus does this, and the check is one
/// comparison per instruction against a whole function's worth of decoded
/// instructions held in memory: 224 bytes each, and the largest function in
/// `libcrypto.so.3` has 4,510 of them, on every thread at once.
pub fn for_each_instruction(
    mem: &MemoryMap,
    arch: &Arch,
    cfg: &Cfg,
    mut f: impl FnMut(Insn),
) -> bool {
    let mut ordered = true;
    let mut last: Option<Addr> = None;
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
            ordered &= last.is_none_or(|p| p <= i.addr);
            last = Some(i.addr);
            f(i);
        }
    }
    ordered
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

/// Decode one instruction, carrying the state a run of them needs.
///
/// Only Thumb has any: every other instruction set this decodes is a function
/// of its own bytes and its address.
fn decode_stateful(
    arch: &Arch,
    window: &[u8],
    at: Addr,
    it: &mut r12e_arch::arm::ItState,
) -> Option<Insn> {
    if *arch == Arch::Thumb {
        let (insn, next) = r12e_arch::arm::decode_thumb(window, at, *it)?;
        *it = next;
        return Some(insn);
    }
    r12e_arch::decode(arch, window, at)
}
