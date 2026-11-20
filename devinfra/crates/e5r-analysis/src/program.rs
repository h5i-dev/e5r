//! The analyzed program: functions, their graphs, references and strings.
//!
//! Discovery runs in rounds. Each round walks every pending entry in parallel,
//! then merges the results in sorted order and queues what they found. Sorting
//! before the merge is what makes the answer independent of which thread
//! finished first, which is gate G5.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use e5r_arch::Insn;
use e5r_core::{Addr, AddrRange, Arch, Caps, Evidence, Provenance, Strength};
use e5r_format::Object;
use rayon::prelude::*;

use crate::cfg::{self, BlockInterner, Cfg, Halt, RawCfg};
use crate::data::{self, DataMap};
use crate::noreturn;
use crate::progress::{Sink, Stage};
use crate::strings::{self, Found};
use crate::xref::{self, Xref, XrefIndex};

/// One recovered function.
#[derive(Debug, Clone)]
pub struct Function {
    /// Entry address.
    pub entry: Addr,
    /// Name, when something named it.
    pub name: Option<String>,
    /// Lowest to highest byte the blocks cover.
    pub range: AddrRange,
    /// Its control flow graph.
    pub cfg: Cfg,
    /// What said this was a function.
    pub provenance: Provenance,
}

impl Function {
    /// The name to show, falling back to the conventional address form.
    ///
    /// Demangled where possible: `std::vector<int>::push_back(int&&)` is what
    /// an analyst needs to see, and the mangled form is one command away.
    pub fn display_name(&self) -> String {
        match &self.name {
            Some(n) => e5r_types::pretty(n),
            None => format!("sub_{:x}", self.entry.get()),
        }
    }

    /// The name exactly as the file spells it, still mangled.
    pub fn raw_name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// True when the walk finished with nothing unresolved.
    pub fn is_complete(&self) -> bool {
        self.cfg.is_complete()
    }
}

/// What analysis to do.
#[derive(Debug, Clone)]
pub struct Options {
    /// Resource caps.
    pub caps: Caps,
    /// Follow direct calls to find functions nothing named.
    pub follow_calls: bool,
    /// Scan gaps between known functions for prologues. Heuristic, so it is
    /// tagged as such and can be turned off.
    pub scan_gaps: bool,
    /// Extract strings.
    pub strings: bool,
    /// String scanning options.
    pub string_opts: strings::Options,
    /// Build the cross reference index.
    pub xrefs: bool,
    /// Work out which functions never return and re-walk the callers that
    /// assumed they did.
    pub noreturn: bool,
    /// Prove which regions hold data, and stop the code partition at them.
    ///
    /// Off leaves [`Program::data`](crate::Program::data) empty and lets the
    /// gap scan read a literal pool as candidate code again. It exists so the
    /// difference can be measured, not so it can be switched off.
    pub data: bool,
    /// Threads to use. `None` means rayon's default.
    pub threads: Option<usize>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            caps: Caps::default(),
            follow_calls: true,
            scan_gaps: true,
            strings: true,
            string_opts: strings::Options::default(),
            xrefs: true,
            noreturn: true,
            data: true,
            threads: None,
        }
    }
}

impl Options {
    /// The option bytes one cache part depends on.
    ///
    /// Exactly the inputs that determine that part's value, and nothing else.
    /// Thread count is deliberately absent: the answer may not depend on it
    /// (gate G5), so keying on it would be admitting that it does. Including
    /// too much would only cost hit rate; including too little would return a
    /// wrong answer, so anything doubtful goes in.
    pub fn cache_bytes(&self, part: crate::cache::Part) -> Vec<u8> {
        let mut v = Vec::with_capacity(64);
        let c = &self.caps;
        for n in [
            c.sections,
            c.symbols,
            c.relocations,
            c.string_len,
            c.function_insns,
            c.function_blocks,
            c.jump_table_entries,
        ] {
            v.extend_from_slice(&n.to_le_bytes());
        }
        match part {
            // Cross references are read off the functions, so what changes the
            // functions changes them too.
            crate::cache::Part::Functions | crate::cache::Part::Xrefs => {
                v.push(self.follow_calls as u8);
                v.push(self.scan_gaps as u8);
                v.push(self.noreturn as u8);
                // The data map decides where the gap scan stops looking, so
                // it changes which functions exist.
                v.push(self.data as u8);
            }
            crate::cache::Part::Strings => {
                v.extend_from_slice(&(self.string_opts.min_len as u64).to_le_bytes());
                v.push(self.string_opts.utf16 as u8);
                v.push(self.string_opts.in_code as u8);
            }
        }
        v
    }
}

/// A binary, analyzed.
pub struct Program {
    /// What the loader produced.
    pub object: Object,
    /// Functions by entry address.
    pub functions: BTreeMap<Addr, Function>,
    /// Every reference found.
    pub xrefs: XrefIndex,
    /// Every string found.
    pub strings: Vec<Found>,
    /// Rounds of discovery it took, for reporting.
    pub rounds: usize,
    /// Functions found never to return.
    pub noreturn: BTreeSet<Addr>,
    /// Regions that are provably data, each with its proof.
    ///
    /// Computed on the first ask rather than eagerly: finding literal pools
    /// means decoding every instruction a second time, and the partition has
    /// already stopped at what it needed. Pre-filled empty when the options
    /// turn it off.
    pub(crate) data: OnceLock<DataMap>,
}

impl Program {
    /// Regions that are provably data, computing them if needed.
    pub fn data(&self) -> &DataMap {
        self.data.get_or_init(|| {
            data::build(
                &self.object,
                &self.functions,
                data::Sources { pointers: true },
                Sink::none(),
            )
        })
    }

    /// Function whose blocks contain `addr`.
    pub fn function_at(&self, addr: Addr) -> Option<&Function> {
        // Hulls can overlap when a function is split, so a hull hit still has
        // to be confirmed against the blocks.
        self.functions
            .values()
            .filter(|f| f.range.contains(addr))
            .find(|f| f.cfg.blocks.values().any(|b| b.range.contains(addr)))
    }

    /// The function starting exactly at `addr`.
    pub fn function(&self, addr: Addr) -> Option<&Function> {
        self.functions.get(&addr)
    }

    /// Functions in address order.
    pub fn functions_by_address(&self) -> impl Iterator<Item = &Function> {
        self.functions.values()
    }

    /// Decode one function's instructions.
    pub fn instructions(&self, f: &Function) -> Vec<Insn> {
        cfg::instructions(&self.object.memory, &self.object.arch, &f.cfg)
    }

    /// Name for an address: an exact function, else a symbol, else nothing.
    pub fn name_of(&self, addr: Addr) -> Option<String> {
        if let Some(f) = self.functions.get(&addr) {
            return Some(f.display_name());
        }
        self.object
            .symbol_at(addr)
            // ARM mapping symbols ($x, $d) mark code and data boundaries, not
            // names; showing one as a label is worse than showing nothing.
            .filter(|s| !s.name.is_empty() && !s.name.starts_with('$'))
            .map(|s| {
                let name = e5r_types::pretty(&s.name);
                if s.addr == addr {
                    name
                } else {
                    format!("{name}+{:#x}", addr.get() - s.addr.get())
                }
            })
    }

    /// A NUL-terminated printable run at `addr`, for annotating a reference
    /// the string scan did not report (it is shorter than the floor, or sits
    /// in a section the scan skipped).
    pub fn text_at(&self, addr: Addr, max: usize) -> Option<String> {
        let bytes = self.object.memory.decode_window(addr, max as u64)?;
        let end = bytes.iter().position(|&b| b == 0)?;
        if end == 0 {
            return None;
        }
        let run = &bytes[..end];
        run.iter()
            .all(|&b| matches!(b, 0x20..=0x7e | b'\t' | b'\n' | b'\r'))
            .then(|| String::from_utf8_lossy(run).into_owned())
    }

    /// How many functions finished with nothing unresolved.
    pub fn complete_count(&self) -> usize {
        self.functions.values().filter(|f| f.is_complete()).count()
    }
}

/// Analyze a loaded object, eagerly.
///
/// Everything the options ask for is computed before this returns. It is a
/// [`Session`](crate::Session) with every part forced, and it stays because a
/// `Program` is what the rest of the workspace wants; a caller that needs only
/// one part should open a session and ask for that part instead.
pub fn analyze(object: Object, opts: &Options) -> Program {
    crate::Session::new(object, opts.clone()).into_program()
}

/// How many functions are walked in parallel before their blocks are interned.
/// The batch is the only thing ever held in the duplicated form, so it bounds
/// the peak; it is large enough to keep every thread busy.
const WALK_BATCH: usize = 8192;

/// Nothing is known never to return during discovery proper: the no-return
/// pass runs after it and re-walks the callers it affects.
static EMPTY: BTreeSet<Addr> = BTreeSet::new();

/// Intern one batch of walked functions and give them the table they name.
///
/// Every function in a batch is published together, because a function must
/// not be read before the table holding its blocks exists.
fn intern_batch(interner: &mut BlockInterner, walked: Vec<(Addr, RawCfg)>) -> Vec<(Addr, Cfg)> {
    let mut out: Vec<(Addr, Cfg)> = walked
        .into_iter()
        .map(|(a, raw)| (a, interner.install(raw)))
        .collect();
    interner.publish(out.iter_mut().map(|(_, c)| c));
    out
}

/// One seed: an address to walk and the evidence that put it there.
#[derive(Clone)]
struct Seed {
    addr: Addr,
    name: Option<String>,
    provenance: Provenance,
}

/// Find functions and walk each one's control flow.
///
/// The first stage and the only one the others depend on. Returns the
/// functions and how many rounds of discovery it took.
pub(crate) fn discover(
    object: &Object,
    opts: &Options,
    interner: &mut BlockInterner,
    sink: Sink<'_>,
) -> (BTreeMap<Addr, Function>, usize) {
    let arch = object.arch.clone();
    let mem = &object.memory;
    // Nothing is proved data yet: the proofs are read off the functions these
    // rounds are about to find.
    let nothing = DataMap::default();

    // Seeds from the loader, strongest evidence first. Only executable
    // addresses: a symbol table can name a function in a section that is not
    // mapped, and walking it would decode whatever is nearby.
    let mut pending: Vec<Seed> = object
        .function_hints
        .iter()
        .filter(|h| mem.is_executable(h.addr))
        .map(|h| Seed {
            addr: h.addr,
            name: h.name.clone(),
            provenance: h.provenance.clone(),
        })
        .collect();

    let mut known: BTreeMap<Addr, Function> = BTreeMap::new();
    let mut evidence: BTreeMap<Addr, (Provenance, Option<String>)> = BTreeMap::new();
    for s in &pending {
        merge_evidence(&mut evidence, s.addr, &s.provenance, s.name.clone());
    }
    let mut rounds = 0;

    // Entries known before a round starts are where a tail call may land.
    while !pending.is_empty() {
        rounds += 1;
        let stop_at: BTreeSet<Addr> = evidence.keys().copied().collect();

        let mut batch: Vec<Seed> = pending
            .drain(..)
            .filter(|s| !known.contains_key(&s.addr))
            .collect();
        batch.sort_by_key(|s| s.addr);
        batch.dedup_by_key(|s| s.addr);

        // A round's own total is known; the stage's is not, because what this
        // round walks is what queues the next one.
        let round_total = Some(batch.len() as u64);
        let mut done = 0u64;
        sink.report(Stage::Discovery, rounds as u32, 0, round_total);

        for slice in batch.chunks(WALK_BATCH) {
            let walked: Vec<(Addr, RawCfg)> = slice
                .par_iter()
                .map(|s| {
                    (
                        s.addr,
                        cfg::build_raw(mem, &arch, s.addr, &stop_at, &EMPTY, &opts.caps, &nothing),
                    )
                })
                .collect();

            for (addr, c) in intern_batch(interner, walked) {
                if c.blocks.is_empty() {
                    continue;
                }
                if opts.follow_calls {
                    for t in &c.calls {
                        if mem.is_executable(*t) && !evidence.contains_key(t) {
                            let p = Provenance::new(Evidence::CallTarget);
                            merge_evidence(&mut evidence, *t, &p, None);
                            pending.push(Seed {
                                addr: *t,
                                name: None,
                                provenance: p,
                            });
                        } else if mem.is_executable(*t) {
                            let p = Provenance::new(Evidence::CallTarget);
                            merge_evidence(&mut evidence, *t, &p, None);
                        }
                    }
                }
                let (provenance, name) = evidence
                    .get(&addr)
                    .cloned()
                    .unwrap_or((Provenance::new(Evidence::CallTarget), None));
                known.insert(
                    addr,
                    Function {
                        entry: addr,
                        name,
                        range: c.hull(),
                        cfg: c,
                        provenance,
                    },
                );
            }
            // Between batches, so the callback is entered from one thread and
            // never from inside the parallel walk.
            done += slice.len() as u64;
            sink.report(Stage::Discovery, rounds as u32, done, round_total);
        }

        // Gap scanning runs once, after the evidence-led rounds settle, so it
        // never invents a function the real evidence would have found.
        if pending.is_empty() && opts.scan_gaps {
            // What is provably data, worked out from everything the
            // evidence-led rounds found, and then used to keep the sweep out
            // of it. This is the one place the partition guesses, so it is the
            // one place the marking has to reach.
            //
            // Only where the sweep runs. It costs a pass over the instructions
            // to find the literal pools, and paying that for an architecture
            // whose gaps are never swept would be paying for nothing.
            let data = if opts.data && object.arch == Arch::AArch64 {
                data::build(object, &known, data::Sources { pointers: false }, sink)
            } else {
                DataMap::default()
            };
            let found = scan_gaps(object, &known, &opts.caps, &data);
            for a in found {
                let p = Provenance::new(Evidence::ProloguePattern);
                merge_evidence(&mut evidence, a, &p, None);
                pending.push(Seed {
                    addr: a,
                    name: None,
                    provenance: p,
                });
            }
            if !pending.is_empty() {
                // One pass only: what the gap scan found is walked, and what
                // that walk finds is not scanned for again.
                let batch = std::mem::take(&mut pending);
                walk_pending(
                    object,
                    &mut known,
                    &mut evidence,
                    batch,
                    interner,
                    Leftovers {
                        opts,
                        data: &data,
                        sink,
                        round: rounds as u32 + 1,
                    },
                );
                return (known, rounds);
            }
        }
    }

    (known, rounds)
}

/// What one leftover batch is walked under.
///
/// Bundled rather than passed one by one: these four travel together and
/// nothing else needs them.
#[derive(Clone, Copy)]
struct Leftovers<'a> {
    opts: &'a Options,
    /// What is known to be data by the time the gap scan runs.
    data: &'a DataMap,
    sink: Sink<'a>,
    /// The round number to report these under, which follows the last real
    /// round.
    round: u32,
}

/// Walk seeds that are left over, without following what they call.
///
/// These are the gap scan's guesses, so unlike the evidence-led rounds they
/// get the data map: a prologue pattern a few words before a literal pool
/// would otherwise decode straight into it.
fn walk_pending(
    object: &Object,
    known: &mut BTreeMap<Addr, Function>,
    evidence: &mut BTreeMap<Addr, (Provenance, Option<String>)>,
    pending: Vec<Seed>,
    interner: &mut BlockInterner,
    over: Leftovers<'_>,
) {
    if pending.is_empty() {
        return;
    }
    let Leftovers {
        opts,
        data,
        sink,
        round,
    } = over;
    let arch = object.arch.clone();
    let mem = &object.memory;
    let stop_at: BTreeSet<Addr> = evidence.keys().copied().collect();
    let mut batch = pending;
    batch.sort_by_key(|s| s.addr);
    batch.dedup_by_key(|s| s.addr);
    let total = Some(batch.len() as u64);
    let mut done = 0u64;
    sink.report(Stage::Discovery, round, 0, total);
    for slice in batch.chunks(WALK_BATCH) {
        let walked: Vec<(Addr, RawCfg)> = slice
            .par_iter()
            .filter(|s| !known.contains_key(&s.addr))
            .map(|s| {
                (
                    s.addr,
                    cfg::build_raw(mem, &arch, s.addr, &stop_at, &EMPTY, &opts.caps, data),
                )
            })
            .collect();
        for (addr, c) in intern_batch(interner, walked) {
            if c.blocks.is_empty() {
                continue;
            }
            let (provenance, name) = evidence
                .remove(&addr)
                .unwrap_or((Provenance::new(Evidence::ProloguePattern), None));
            known.insert(
                addr,
                Function {
                    entry: addr,
                    name,
                    range: c.hull(),
                    cfg: c,
                    provenance,
                },
            );
        }
        done += slice.len() as u64;
        sink.report(Stage::Discovery, round, done, total);
    }
}

/// Which functions never come back, and a re-walk of the callers that assumed
/// they did.
///
/// One pass: the set is computed from complete functions, and a re-walk only
/// ever shortens a function, so a second pass finds nothing the first did not.
/// Part of discovery rather than a stage after it, because it corrects the
/// functions themselves.
pub(crate) fn refine_noreturn(
    object: &Object,
    known: &mut BTreeMap<Addr, Function>,
    opts: &Options,
    interner: &mut BlockInterner,
    sink: Sink<'_>,
) -> BTreeSet<Addr> {
    if !opts.noreturn {
        return BTreeSet::new();
    }
    let arch = object.arch.clone();
    let mem = &object.memory;
    // The re-walk only ever shortens a function, so it cannot reach bytes the
    // first walk did not.
    let nothing = DataMap::default();
    let named: BTreeMap<Addr, Option<String>> =
        known.iter().map(|(a, f)| (*a, f.name.clone())).collect();
    let graph: BTreeMap<Addr, &Cfg> = known.iter().map(|(a, f)| (*a, &f.cfg)).collect();
    let set = noreturn::compute(&named, &graph);
    let affected: Vec<Addr> = known
        .iter()
        .filter(|(a, f)| !set.contains(a) && f.cfg.calls.iter().any(|c| set.contains(c)))
        .map(|(a, _)| *a)
        .collect();
    let stop_at: BTreeSet<Addr> = known.keys().copied().collect();
    let total = Some(affected.len() as u64);
    let mut rebuilt_count = 0u64;
    sink.report(Stage::NoReturn, 1, 0, total);
    for slice in affected.chunks(WALK_BATCH) {
        let rebuilt: Vec<(Addr, RawCfg)> = slice
            .par_iter()
            .map(|a| {
                (
                    *a,
                    cfg::build_raw(mem, &arch, *a, &stop_at, &set, &opts.caps, &nothing),
                )
            })
            .collect();
        for (a, c) in intern_batch(interner, rebuilt) {
            if c.blocks.is_empty() {
                continue;
            }
            if let Some(f) = known.get_mut(&a) {
                f.range = c.hull();
                f.cfg = c;
            }
        }
        rebuilt_count += slice.len() as u64;
        sink.report(Stage::NoReturn, 1, rebuilt_count, total);
    }
    set
}

/// Give every function the finished table, so the snapshots taken while
/// discovery was running can be dropped.
pub(crate) fn publish_blocks(known: &mut BTreeMap<Addr, Function>, interner: &mut BlockInterner) {
    interner.publish(known.values_mut().map(|f| &mut f.cfg));
}

/// Every reference the recovered functions make.
pub(crate) fn build_xrefs(
    object: &Object,
    known: &BTreeMap<Addr, Function>,
    sink: Sink<'_>,
) -> XrefIndex {
    let arch = object.arch.clone();
    let mem = &object.memory;
    // One list per unit of parallel work rather than one per function. A
    // function makes 25 references on average, so a list of its own is a few
    // hundred bytes that doubled its way there, and 127,229 of those left the
    // allocator holding several times what the finished index needs: the stage
    // cost 543 MB resident for 155 MB of index.
    let functions: Vec<&Function> = known.values().collect();
    let total = Some(functions.len() as u64);
    let mut done = 0u64;
    sink.report(Stage::Xrefs, 1, 0, total);
    let mut all: Vec<Vec<Xref>> = Vec::new();
    // Walked in batches rather than in one sweep, so there is a sequential
    // point to report from. The answer does not depend on the batching: the
    // index sorts what it is given.
    for slice in functions.chunks(WALK_BATCH) {
        let part: Vec<Vec<Xref>> = slice
            .par_iter()
            .fold(Vec::new, |mut out: Vec<Xref>, f| {
                let start = out.len();
                // Streamed rather than decoded into a list first: this runs on
                // every thread at once, and a decoded instruction is an order of
                // magnitude larger than the references it produces.
                let mut c = xref::Collector::new(mem, &mut out);
                let ordered = cfg::for_each_instruction(mem, &arch, &f.cfg, |i| c.push(i));
                c.finish();
                if !ordered {
                    // Overlapping blocks, which nothing in the corpus produces.
                    // The tracker reads instructions in address order, so pay for
                    // the sort rather than answer differently. Only this
                    // function's references are dropped, not the whole list.
                    out.truncate(start);
                    let insns = cfg::instructions(mem, &arch, &f.cfg);
                    xref::collect(&insns, mem, &mut out);
                }
                out
            })
            .collect();
        all.extend(part);
        done += slice.len() as u64;
        sink.report(Stage::Xrefs, 1, done, total);
    }
    // Concatenation order is not part of the answer: [`XrefIndex::build`]
    // sorts and deduplicates, and every field of a reference takes part in the
    // ordering, so the arrays it produces are the same set in the same order
    // whatever order the work finished in. That is gate G5.
    //
    // Sized up front: collecting from a flattening iterator has no size hint,
    // so it doubles its way there and holds twice the final index at the peak.
    let mut flat: Vec<Xref> = Vec::with_capacity(all.iter().map(Vec::len).sum());
    for v in all.drain(..) {
        flat.extend_from_slice(&v);
    }
    XrefIndex::build(flat)
}

/// Where to look for strings.
///
/// Sections when the container has them, because `.rodata` sits inside an
/// executable segment in the usual ELF layout and the segment's permission
/// says nothing useful about it. Segments otherwise.
pub(crate) fn scan_strings(object: &Object, opts: &strings::Options, sink: Sink<'_>) -> Vec<Found> {
    let mem = &object.memory;
    let mut ranges: Vec<AddrRange> = object
        .sections
        .iter()
        .filter(|s| !s.range.is_empty() && s.file_size > 0 && (opts.in_code || !s.exec))
        .map(|s| s.range)
        .collect();
    if ranges.is_empty() {
        ranges = mem
            .segments()
            .iter()
            .filter(|s| opts.in_code || !s.perms.exec)
            .map(|s| s.range)
            .collect();
    }
    // One range at a time, which is a section, so the report says which part
    // of the image is being read. Scanning them together and scanning them one
    // by one give the same answer: the sort and the deduplication below are
    // what the combined scan ends with anyway.
    let total = Some(ranges.len() as u64);
    sink.report(Stage::Strings, 1, 0, total);
    let mut out: Vec<Found> = Vec::new();
    for (n, r) in ranges.iter().enumerate() {
        out.extend(strings::scan_ranges(mem, std::slice::from_ref(r), opts));
        sink.report(Stage::Strings, 1, n as u64 + 1, total);
    }
    out.sort_by_key(|f| (f.addr, f.len));
    out.dedup_by_key(|f| f.addr);
    out
}

/// Record evidence for an address, keeping the strongest name.
fn merge_evidence(
    map: &mut BTreeMap<Addr, (Provenance, Option<String>)>,
    addr: Addr,
    p: &Provenance,
    name: Option<String>,
) {
    match map.get_mut(&addr) {
        Some((existing, existing_name)) => {
            existing.merge(p);
            if existing_name.is_none() {
                *existing_name = name;
            }
        }
        None => {
            map.insert(addr, (p.clone(), name));
        }
    }
}

/// Look for function prologues in executable bytes no function covers.
///
/// Heuristic by construction, so every hit is tagged as such. Runs only after
/// the evidence-led rounds finish, so it cannot pre-empt a real answer.
///
/// Covered ranges are merged into a sorted disjoint list first and the scan
/// walks the gaps between them. Testing each address against every block
/// instead is quadratic, and on a libc-sized binary that is the difference
/// between eight seconds and a tenth of one.
fn scan_gaps(
    object: &Object,
    known: &BTreeMap<Addr, Function>,
    caps: &Caps,
    data: &DataMap,
) -> Vec<Addr> {
    // Two architectures whose instructions are aligned and whose prologues are
    // a short list of encodings. x86 is not one of them: a one-byte alignment
    // makes every offset a candidate and every candidate plausible.
    let step = match object.arch {
        Arch::AArch64 => 4,
        Arch::Thumb => 2,
        _ => return Vec::new(),
    };
    let mem = &object.memory;
    let covered = merge_ranges(
        known
            .values()
            .flat_map(|f| f.cfg.blocks.values().map(|b| b.range)),
    );

    let mut out = Vec::new();
    for seg in mem.segments() {
        if !seg.perms.exec {
            continue;
        }
        for gap in gaps_in(seg.range, &covered) {
            let mut at = gap.start();
            while at < gap.end() {
                // A literal pool, a jump table or a declared object. Four
                // bytes of any of them match a prologue as readily as any
                // other four do, and a function invented there is a function
                // that does not exist.
                if let Some(end) = data.end_of_run(at) {
                    let past = Addr(end.get().next_multiple_of(step));
                    at = if past > at {
                        past
                    } else {
                        at.wrapping_offset(step as i64)
                    };
                    continue;
                }
                if is_prologue(mem, at, &object.arch) {
                    out.push(at);
                }
                at = at.wrapping_offset(step as i64);
            }
        }
        if out.len() as u64 > caps.function_blocks {
            break;
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Sort and coalesce ranges into a disjoint list.
pub(crate) fn merge_ranges(it: impl Iterator<Item = AddrRange>) -> Vec<AddrRange> {
    let mut v: Vec<AddrRange> = it.filter(|r| !r.is_empty()).collect();
    v.sort_unstable_by_key(|r| (r.start(), r.end()));
    let mut out: Vec<AddrRange> = Vec::with_capacity(v.len());
    for r in v {
        match out.last_mut() {
            Some(last) if r.start() <= last.end() => {
                if r.end() > last.end() {
                    *last = AddrRange::new(last.start(), r.end()).unwrap_or(*last);
                }
            }
            _ => out.push(r),
        }
    }
    out
}

/// The parts of `span` that `covered` does not cover. `covered` must be sorted
/// and disjoint, as [`merge_ranges`] returns.
fn gaps_in(span: AddrRange, covered: &[AddrRange]) -> Vec<AddrRange> {
    let mut out = Vec::new();
    let mut at = span.start();
    let first = covered.partition_point(|r| r.end() <= span.start());
    for r in &covered[first..] {
        if r.start() >= span.end() {
            break;
        }
        if r.start() > at {
            if let Some(g) = AddrRange::new(at, r.start().min(span.end())) {
                if !g.is_empty() {
                    out.push(g);
                }
            }
        }
        at = at.max(r.end());
    }
    if at < span.end() {
        if let Some(g) = AddrRange::new(at, span.end()) {
            out.push(g);
        }
    }
    out
}

/// AArch64 prologue shapes a compiler emits.
///
/// `stp x29, x30, [sp, #-N]!` is the frame setup, `paciasp`/`bti c` open a
/// pointer-authenticated or branch-target-hardened function, and `sub sp, sp,
/// #N` opens a leaf that needs stack.
fn is_prologue(mem: &e5r_core::MemoryMap, at: Addr, arch: &Arch) -> bool {
    if *arch == Arch::Thumb {
        return is_thumb_prologue(mem, at);
    }
    let Some(w) = mem.slice(at, 4) else {
        return false;
    };
    let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
    // stp x29, x30, [sp, #imm]! — pre-index store pair of the frame registers.
    let stp_frame = word & 0xffc0_7fff == 0xa980_7bfd;
    // paciasp / pacibsp.
    let pac = word == 0xd503_233f || word == 0xd503_237f;
    // bti c / bti jc.
    let bti = word == 0xd503_245f || word == 0xd503_247f;
    // sub sp, sp, #imm.
    let sub_sp = word & 0xffc0_03ff == 0xd100_03ff;
    stp_frame || pac || bti || sub_sp
}

/// The start of a Thumb function.
///
/// Every non-leaf function begins by saving the link register, which is the
/// `push` with bit 8 of its register list set, or its wide form. A leaf that
/// only needs stack space begins by taking it. Those three cover what a
/// compiler emits; a function that begins with anything else is found by a
/// call to it rather than by this.
fn is_thumb_prologue(mem: &e5r_core::MemoryMap, at: Addr) -> bool {
    let Some(w) = mem.slice(at, 2) else {
        return false;
    };
    let half = u16::from_le_bytes([w[0], w[1]]);
    // push {..., lr}
    if half & 0xff00 == 0xb500 {
        return true;
    }
    // push.w {..., lr}: the wide encoding, whose second halfword carries the
    // register list with the link register in bit 14.
    let Some(w) = mem.slice(at, 4) else {
        return false;
    };
    let (hi, lo) = (
        u16::from_le_bytes([w[0], w[1]]),
        u16::from_le_bytes([w[2], w[3]]),
    );
    hi == 0xe92d && lo & 0x4000 != 0
}

/// Summary counts, for reporting and for the JSON surface.
#[derive(Debug, Clone, Copy, Default)]
pub struct Stats {
    /// Functions found.
    pub functions: usize,
    /// Of those, how many finished with nothing unresolved.
    pub complete: usize,
    /// Basic blocks across all functions.
    pub blocks: usize,
    /// Instructions decoded.
    pub insns: u64,
    /// References found.
    pub xrefs: usize,
    /// Strings found.
    pub strings: usize,
    /// Functions that hit a resource cap.
    pub capped: usize,
    /// Functions found never to return.
    pub noreturn: usize,
    /// Jump tables resolved.
    pub tables: usize,
    /// Targets those tables contributed.
    pub table_targets: usize,
    /// Functions still holding an unresolved indirect branch.
    pub indirect: usize,
    /// Regions proved to hold data.
    pub data_regions: usize,
    /// Bytes those regions cover, counted once where proofs overlap.
    pub data_bytes: u64,
}

impl Program {
    /// Count everything worth reporting.
    pub fn stats(&self) -> Stats {
        Stats {
            functions: self.functions.len(),
            complete: self.complete_count(),
            blocks: self.functions.values().map(|f| f.cfg.blocks.len()).sum(),
            insns: self.functions.values().map(|f| f.cfg.insns() as u64).sum(),
            xrefs: self.xrefs.len(),
            strings: self.strings.len(),
            capped: self
                .functions
                .values()
                .filter(|f| matches!(f.cfg.halt, Halt::InstructionCap | Halt::BlockCap))
                .count(),
            noreturn: self.noreturn.len(),
            tables: self.functions.values().map(|f| f.cfg.tables.len()).sum(),
            table_targets: self
                .functions
                .values()
                .flat_map(|f| f.cfg.tables.iter())
                .map(|t| t.targets.len())
                .sum(),
            indirect: self
                .functions
                .values()
                .filter(|f| f.cfg.has_indirect)
                .count(),
            data_regions: self.data().len(),
            data_bytes: self.data().bytes(),
        }
    }

    /// Functions grouped by how strong their evidence is.
    pub fn by_strength(&self) -> BTreeMap<Strength, usize> {
        let mut out = BTreeMap::new();
        for f in self.functions.values() {
            *out.entry(f.provenance.strength()).or_insert(0) += 1;
        }
        out
    }
}
