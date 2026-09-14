//! Where the memory goes, stage by stage and structure by structure.
//!
//! Not a test and not wired into the CLI: it exists so the memory numbers in
//! docs/scorecard.md and in an M11 report are measured rather than guessed.
//!
//! A session is what makes this one run rather than four. Each part is forced
//! in turn and nothing is dropped, so the resident set after a part minus the
//! resident set before it is exactly what that part retains, and the peak
//! along the way is what it needed transiently to get there. An eager
//! `analyze` could only be priced by running it once per option, which prices
//! four analyses rather than four stages.
//!
//! The accounting at the end is the same quantity counted a second way, from
//! the sizes of what is actually stored. Two independent numbers that agree
//! are evidence; one number is a claim.
//!
//! Usage: cargo run --release -p r12e-analysis --example phases -- <binary> [no-scan]

use std::collections::BTreeMap;

use r12e_analysis::program::{Function, Options};
use r12e_analysis::{Cfg, Session};
use r12e_core::Addr;
use r12e_format::{LoadOptions, Object};

/// Current and peak resident set, in kilobytes, from the kernel.
fn rss() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let field = |name: &str| -> u64 {
        s.lines()
            .find(|l| l.starts_with(name))
            .and_then(|l| l.split_whitespace().nth(1))
            .and_then(|v| v.parse().ok())
            .unwrap_or(0)
    };
    (field("VmRSS:"), field("VmHWM:"))
}

/// Print one stage, and return the resident set so the caller can difference
/// it against the next.
fn mark(label: &str, prev: u64, note: String) -> u64 {
    let (now, peak) = rss();
    println!(
        "{label:<18} rss {:>8} KB  (+{:>8} KB)  peak {:>8} KB  {note}",
        now,
        now.saturating_sub(prev),
        peak
    );
    now
}

/// Rust's B-tree holds between 5 and 11 elements per node, plus a parent
/// pointer, an index and a length. Nodes are counted as three-quarters full,
/// which is what a map built by ascending insertion settles at; the number is
/// an estimate and is labelled as one.
fn btree_bytes(elements: usize, key: usize, value: usize) -> usize {
    if elements == 0 {
        return 0;
    }
    let per_node = 16 + 11 * (key + value);
    let nodes = elements.div_ceil(8).max(1);
    nodes * per_node
}

/// The accounting: bytes held, broken down by what holds them.
fn account(functions: &BTreeMap<Addr, Function>) {
    let map = btree_bytes(functions.len(), size_of::<Addr>(), size_of::<Function>());
    let mut names = 0usize;
    let mut blocks = 0usize;
    let mut succ = 0usize;
    let mut calls = 0usize;
    let mut tables = 0usize;
    let mut targets = 0usize;
    let mut provenance = 0usize;
    let mut nblocks = 0usize;
    let mut nsucc = 0usize;
    let mut ncalls = 0usize;
    let mut insns = 0u64;
    for f in functions.values() {
        names += f.name.as_ref().map_or(0, |n| n.capacity());
        provenance += f.provenance.corroborating.capacity() * size_of::<r12e_core::Evidence>();
        nblocks += f.cfg.blocks.len();
        // Four bytes per stored block: the block itself is in the shared
        // table, counted once below.
        blocks += f.cfg.blocks.len() * size_of::<u32>() + 32;
        for b in f.cfg.blocks.values() {
            nsucc += b.successors.len();
        }
        ncalls += f.cfg.calls.len();
        calls += f.cfg.calls.capacity() * size_of::<Addr>();
        tables += f.cfg.tables.capacity() * size_of::<r12e_analysis::JumpTable>();
        for t in &f.cfg.tables {
            targets += t.targets.capacity() * size_of::<Addr>();
        }
        insns += f.cfg.insns() as u64;
    }
    // The shared block table, counted once rather than once per function that
    // names a block. An entry is the block plus the address it starts at.
    let table = functions
        .values()
        .next()
        .map(|f| f.cfg.blocks.table())
        .expect("a program with no functions has nothing to account for");
    let distinct = table.len();
    let mut table_bytes = distinct * (size_of::<r12e_analysis::Block>() + size_of::<Addr>());
    for b in table.blocks() {
        // What the allocator hands out, not what the list holds: glibc rounds
        // a request up to a 16-byte multiple with an 8-byte header and never
        // gives out less than 32 bytes, so one or two successors cost 32.
        let want = b.successors.capacity() * size_of::<Addr>();
        succ += if want == 0 {
            0
        } else {
            (want + 8).next_multiple_of(16).max(32)
        };
    }
    table_bytes += succ;
    let total = map + names + blocks + table_bytes + calls + tables + targets + provenance;
    let kb = |n: usize| n / 1024;
    println!();
    println!("accounted bytes, by what holds them");
    println!(
        "  function map    {:>9} KB   {} functions at {} B each, in B-tree nodes",
        kb(map),
        functions.len(),
        size_of::<Function>()
    );
    println!(
        "  block ids       {:>9} KB   {nblocks} stored blocks at 4 B each",
        kb(blocks)
    );
    println!(
        "  block table     {:>9} KB   {distinct} distinct blocks at {} B each, plus {} KB of \
         successor lists for {nsucc} edges",
        kb(table_bytes),
        size_of::<r12e_analysis::Block>() + size_of::<Addr>(),
        kb(succ)
    );
    println!(
        "  call lists      {:>9} KB   {ncalls} call sites",
        kb(calls)
    );
    println!(
        "  jump tables     {:>9} KB   plus {} KB of targets",
        kb(tables),
        kb(targets)
    );
    println!("  function names  {:>9} KB", kb(names));
    println!(
        "  provenance      {:>9} KB   corroborating evidence",
        kb(provenance)
    );
    println!("  ---");
    println!("  total           {:>9} KB", kb(total));
    println!();
    println!(
        "per function {} B, per block {} B, per instruction {} B",
        total / functions.len().max(1),
        total / nblocks.max(1),
        total as u64 / insns.max(1)
    );
    println!(
        "{insns} instructions are decoded and thrown away; one decoded Insn is {} B, so keeping \
         them would cost {} MB",
        size_of::<r12e_arch::Insn>(),
        insns * size_of::<r12e_arch::Insn>() as u64 / (1024 * 1024)
    );

    // How much of what is stored is the same code stored twice. Functions
    // recovered from independent evidence can cover the same bytes, and a
    // block map is the largest thing this crate holds, so the answer decides
    // whether the memory ceiling is a question of representation or of
    // discovery. A sorted vector rather than a set, because a set of eight
    // million ranges costs more than the thing being measured.
    let mut ranges: Vec<(u64, u64)> = Vec::with_capacity(nblocks);
    for f in functions.values() {
        for b in f.cfg.blocks.values() {
            ranges.push((b.range.start().get(), b.range.end().get()));
        }
    }
    ranges.sort_unstable();
    let distinct = {
        let mut n = 0usize;
        let mut last = None;
        for r in &ranges {
            if Some(*r) != last {
                n += 1;
                last = Some(*r);
            }
        }
        n
    };
    // Union of the ranges, which is the code actually reached.
    let mut covered = 0u64;
    let mut end = 0u64;
    for (s, e) in &ranges {
        let from = (*s).max(end);
        if *e > from {
            covered += *e - from;
            end = *e;
        }
    }
    println!(
        "{nblocks} blocks are {distinct} distinct ranges covering {} KB of code, so {:.1}x of what \
         is stored is the same bytes held by more than one function",
        covered / 1024,
        nblocks as f64 / distinct.max(1) as f64
    );
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: phases <binary>");
    let mut at = mark("start", 0, String::new());

    // Read rather than mapped, unlike the CLI, so this line is the whole file
    // where `r12e` pays only for the pages it touches. Everything after it is
    // the same either way, which is the part being measured.
    let data = std::fs::read(&path).expect("read");
    at = mark("file read", at, format!("{} KB of file", data.len() / 1024));

    let object: Object = r12e_format::load(&data, &LoadOptions::default()).expect("load");
    at = mark(
        "load",
        at,
        format!(
            "{} symbols, {} hints",
            object.symbols.len(),
            object.function_hints.len()
        ),
    );

    // One session, each part forced in turn: nothing is dropped, so every
    // difference below is what that part keeps.
    // A second argument switches gap scanning off, because a prologue scan
    // invents functions that overlap the ones real evidence found, and the
    // block duplication printed at the end is the number that says whether
    // that is where the memory goes.
    let opts = Options {
        scan_gaps: std::env::args().nth(2).as_deref() != Some("no-scan"),
        ..Options::default()
    };
    let session = Session::new(object, opts);

    let functions = session.functions();
    let nblocks: usize = functions.values().map(|f| f.cfg.blocks.len()).sum();
    let insns: u64 = functions.values().map(|f| f.cfg.insns() as u64).sum();
    at = mark(
        "functions + cfg",
        at,
        format!(
            "{} functions, {nblocks} blocks, {insns} insns, {} noreturn",
            functions.len(),
            session.noreturn().len()
        ),
    );

    at = mark("xrefs", at, format!("{} xrefs", session.xrefs().len()));

    let bytes: usize = session.strings().iter().map(|f| f.text.len()).sum();
    mark(
        "strings",
        at,
        format!(
            "{} strings, {} KB of text",
            session.strings().len(),
            bytes / 1024
        ),
    );

    account(session.functions());

    let max_insns = functions.values().map(|f| f.cfg.insns()).max().unwrap_or(0);
    let max_blocks = functions
        .values()
        .map(|f| f.cfg.blocks.len())
        .max()
        .unwrap_or(0);
    println!(
        "largest function {max_insns} insns, {max_blocks} blocks, so decoding it into a list \
         costs {} KB on whichever thread has it",
        max_insns as usize * size_of::<r12e_arch::Insn>() / 1024
    );
    println!(
        "sizeof Function {}, Block {}, Cfg {}, Xref {}, Found {}, JumpTable {}",
        size_of::<Function>(),
        size_of::<r12e_analysis::Block>(),
        size_of::<Cfg>(),
        size_of::<r12e_analysis::Xref>(),
        size_of::<r12e_analysis::Found>(),
        size_of::<r12e_analysis::JumpTable>(),
    );
}
