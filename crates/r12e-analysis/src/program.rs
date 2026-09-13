//! The analyzed program: functions, their graphs, references and strings.
//!
//! Discovery runs in rounds. Each round walks every pending entry in parallel,
//! then merges the results in sorted order and queues what they found. Sorting
//! before the merge is what makes the answer independent of which thread
//! finished first, which is gate G5.

use std::collections::{BTreeMap, BTreeSet};

use r12e_arch::Insn;
use r12e_core::{Addr, AddrRange, Arch, Caps, Evidence, Provenance, Strength};
use r12e_format::Object;
use rayon::prelude::*;

use crate::cfg::{self, Cfg, Halt};
use crate::noreturn;
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
            Some(n) => r12e_types::pretty(n),
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
            threads: None,
        }
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
}

impl Program {
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
                let name = r12e_types::pretty(&s.name);
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

/// Analyze a loaded object.
pub fn analyze(object: Object, opts: &Options) -> Program {
    match opts.threads {
        Some(n) if n > 0 => rayon::ThreadPoolBuilder::new()
            .num_threads(n)
            .build()
            .map(|pool| pool.install(|| run(object.clone(), opts)))
            .unwrap_or_else(|_| run(object, opts)),
        _ => run(object, opts),
    }
}

/// One seed: an address to walk and the evidence that put it there.
#[derive(Clone)]
struct Seed {
    addr: Addr,
    name: Option<String>,
    provenance: Provenance,
}

fn run(object: Object, opts: &Options) -> Program {
    let arch = object.arch.clone();
    let mem = &object.memory;

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

        let walked: Vec<(Addr, Cfg)> = batch
            .par_iter()
            .map(|s| (s.addr, cfg::build(mem, &arch, s.addr, &stop_at, &opts.caps)))
            .collect();

        for (addr, c) in walked {
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

        // Gap scanning runs once, after the evidence-led rounds settle, so it
        // never invents a function the real evidence would have found.
        if pending.is_empty() && opts.scan_gaps {
            let found = scan_gaps(&object, &known, &opts.caps);
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
                // One pass only.
                let mut opts2 = opts.clone();
                opts2.scan_gaps = false;
                return finish(object, known, evidence, pending, &opts2, rounds);
            }
        }
    }

    finish(object, known, evidence, Vec::new(), opts, rounds)
}

/// Walk whatever is still pending, then build the references and strings.
fn finish(
    object: Object,
    mut known: BTreeMap<Addr, Function>,
    mut evidence: BTreeMap<Addr, (Provenance, Option<String>)>,
    pending: Vec<Seed>,
    opts: &Options,
    rounds: usize,
) -> Program {
    let arch = object.arch.clone();
    let mem = &object.memory;

    if !pending.is_empty() {
        let stop_at: BTreeSet<Addr> = evidence.keys().copied().collect();
        let mut batch = pending;
        batch.sort_by_key(|s| s.addr);
        batch.dedup_by_key(|s| s.addr);
        let walked: Vec<(Addr, Cfg)> = batch
            .par_iter()
            .filter(|s| !known.contains_key(&s.addr))
            .map(|s| (s.addr, cfg::build(mem, &arch, s.addr, &stop_at, &opts.caps)))
            .collect();
        for (addr, c) in walked {
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
    }

    // Which functions never return, and a re-walk of the callers that assumed
    // they did. One pass: the set is computed from complete functions, and a
    // re-walk only ever shortens a function, so a second pass finds nothing
    // the first did not.
    let noreturn = if opts.noreturn {
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
        let rebuilt: Vec<(Addr, Cfg)> = affected
            .par_iter()
            .map(|a| {
                (
                    *a,
                    cfg::build_with(mem, &arch, *a, &stop_at, &set, &opts.caps),
                )
            })
            .collect();
        for (a, c) in rebuilt {
            if c.blocks.is_empty() {
                continue;
            }
            if let Some(f) = known.get_mut(&a) {
                f.range = c.hull();
                f.cfg = c;
            }
        }
        set
    } else {
        BTreeSet::new()
    };

    let xrefs = if opts.xrefs {
        let mut all: Vec<Vec<Xref>> = known
            .values()
            .collect::<Vec<_>>()
            .par_iter()
            .map(|f| {
                let insns = cfg::instructions(mem, &arch, &f.cfg);
                let mut out = Vec::new();
                xref::collect(&insns, mem, &mut out);
                out
            })
            .collect();
        // Sorted concatenation, so thread completion order cannot reach the
        // result.
        all.sort_by_key(|v| v.first().map(|x| x.from));
        XrefIndex::build(all.into_iter().flatten().collect())
    } else {
        XrefIndex::default()
    };

    let strings = if opts.strings {
        string_ranges(&object, &opts.string_opts)
    } else {
        Vec::new()
    };

    Program {
        object,
        functions: known,
        xrefs,
        strings,
        rounds,
        noreturn,
    }
}

/// Where to look for strings.
///
/// Sections when the container has them, because `.rodata` sits inside an
/// executable segment in the usual ELF layout and the segment's permission
/// says nothing useful about it. Segments otherwise.
fn string_ranges(object: &Object, opts: &strings::Options) -> Vec<Found> {
    let mem = &object.memory;
    let ranges: Vec<AddrRange> = object
        .sections
        .iter()
        .filter(|s| !s.range.is_empty() && s.file_size > 0 && (opts.in_code || !s.exec))
        .map(|s| s.range)
        .collect();
    if ranges.is_empty() {
        strings::scan(mem, opts)
    } else {
        strings::scan_ranges(mem, &ranges, opts)
    }
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
fn scan_gaps(object: &Object, known: &BTreeMap<Addr, Function>, caps: &Caps) -> Vec<Addr> {
    if object.arch != Arch::AArch64 {
        return Vec::new();
    }
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
                if is_prologue(mem, at) {
                    out.push(at);
                }
                at = at.wrapping_offset(4);
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
fn merge_ranges(it: impl Iterator<Item = AddrRange>) -> Vec<AddrRange> {
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
fn is_prologue(mem: &r12e_core::MemoryMap, at: Addr) -> bool {
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
