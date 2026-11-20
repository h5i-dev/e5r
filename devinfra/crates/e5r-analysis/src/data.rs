//! Regions that are provably data, and the proof for each one.
//!
//! The code partition has two ways to reach an address: recursive descent from
//! evidence, which only ever follows a real control edge, and the linear sweep
//! over the gaps, which looks at bytes nobody claimed and asks whether they
//! open a function. The sweep is where a literal pool or a jump table gets
//! decoded as instructions, because four bytes of a pool are as likely to
//! match `sub sp, sp, #imm` as any other four bytes are. Marking what is data
//! and stopping the sweep at it is the fix.
//!
//! The rule the whole module is written to is **provably data, not probably
//! data**. A region marked as data that is really code loses a function with
//! no diagnostic anywhere, which is the worst thing this subsystem can
//! produce, so every region carries the [`Proof`] that put it there and
//! anything short of a proof is not marked at all. Two consequences:
//!
//! * A candidate that overlaps a block some function already walked is dropped
//!   rather than believed. Instructions were decoded there and control reached
//!   them, which outranks anything here.
//! * Nothing is inferred from shape. A run of bytes that looks like a pointer
//!   table is not marked; a run of bytes an instruction reads, a symbol
//!   declares, or a recovered jump table was read out of, is.
//!
//! What is still missing is relocation targets. A relocation says the linker
//! wrote a value at an address, which is as strong as evidence gets, but
//! `e5r_format::Object` does not carry the relocations it applied, so this
//! crate cannot see them.

use std::collections::BTreeMap;

use e5r_arch::{Insn, Operand};
use e5r_core::{Addr, AddrRange, Arch, MemoryMap};
use e5r_format::Object;
use rayon::prelude::*;
use serde::Serialize;

use crate::cfg;
use crate::program::Function;
use crate::progress::{Sink, Stage};

/// Why a region is known to hold data.
///
/// Every variant is something observed rather than something inferred: an
/// instruction that reads the bytes, a container that declares them, or a
/// table recovery that consumed them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Proof {
    /// The entries of a recovered jump table, with the indirect branch they
    /// resolve. Every byte in the range was read as a table entry and yielded
    /// an aligned, executable, in-section target.
    JumpTable {
        /// The branch the table resolves.
        branch: Addr,
    },
    /// The slots of a virtual table the container's own symbol table names and
    /// sizes. `_ZTV` under the Itanium ABI, `??_7` under Microsoft's.
    Vtable,
    /// An object the container's symbol table declares, with a size. The
    /// container is saying this is not code.
    DeclaredObject,
    /// A word an instruction reads through a pc-relative operand: an AArch64
    /// literal pool entry, or the x86-64 `[rip + disp]` form. The instruction
    /// that reads it is the proof, and its address is recorded.
    LiteralPool {
        /// The instruction that reads these bytes.
        read_by: Addr,
    },
    /// A run of pointer-sized words, in a section the container marks
    /// non-executable, each holding the address of something inside a declared
    /// section.
    ///
    /// No target address is carried. A run of pointers is thousands of words
    /// on a real binary and one region per word would cost more than the whole
    /// block table does; the words are still there to be read.
    Pointer,
}

impl Proof {
    /// A short name for reporting.
    pub fn label(&self) -> &'static str {
        match self {
            Proof::JumpTable { .. } => "jump table",
            Proof::Vtable => "vtable",
            Proof::DeclaredObject => "declared object",
            Proof::LiteralPool { .. } => "literal pool",
            Proof::Pointer => "pointer",
        }
    }
}

/// One region of data and what proves it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct Region {
    /// The bytes.
    pub range: AddrRange,
    /// What put it here.
    pub proof: Proof,
}

/// Every region of a program that is known to hold data.
///
/// Regions may overlap, because two different proofs can cover the same bytes
/// and throwing one away would throw away a reason. Containment questions go
/// through a separate merged list, so asking whether an address is data is a
/// binary search and does not care how many proofs agree.
#[derive(Debug, Clone, Default)]
pub struct DataMap {
    regions: Vec<Region>,
    /// The same bytes, merged into a disjoint sorted list.
    covered: Vec<AddrRange>,
    refused: usize,
}

impl DataMap {
    /// Every region with its proof, sorted by address then by proof.
    pub fn regions(&self) -> &[Region] {
        &self.regions
    }

    /// How many regions there are.
    pub fn len(&self) -> usize {
        self.regions.len()
    }

    /// Candidates dropped because a block some function actually walked
    /// covered them.
    ///
    /// Zero is the expected answer. A nonzero count is a disagreement between
    /// a proof here and the code partition, and one of the two is wrong; it is
    /// reported rather than resolved, because resolving it silently either way
    /// is how a function or a data region disappears without a trace.
    pub fn refused(&self) -> usize {
        self.refused
    }

    /// True when nothing is marked.
    pub fn is_empty(&self) -> bool {
        self.regions.is_empty()
    }

    /// True when this address is inside a region that is known to be data.
    pub fn contains(&self, at: Addr) -> bool {
        self.run_at(at).is_some()
    }

    /// The first proof covering this address, when there is one.
    ///
    /// Linear, unlike [`DataMap::contains`]: it is for explaining one address
    /// to a person, not for a scan.
    pub fn proof_at(&self, at: Addr) -> Option<&Region> {
        self.regions.iter().find(|r| r.range.contains(at))
    }

    /// One past the last byte of the unbroken data run containing `at`, so a
    /// scan can step over the whole of it instead of one unit at a time.
    pub fn end_of_run(&self, at: Addr) -> Option<Addr> {
        self.run_at(at).map(|r| r.end())
    }

    /// Total bytes marked.
    pub fn bytes(&self) -> u64 {
        self.covered.iter().map(|r| r.len()).sum()
    }

    /// Bytes marked inside a range, which is how a report says what fraction
    /// of `.text` this accounts for.
    pub fn bytes_in(&self, span: AddrRange) -> u64 {
        self.covered
            .iter()
            .filter_map(|r| AddrRange::new(r.start().max(span.start()), r.end().min(span.end())))
            .map(|r| r.len())
            .sum()
    }

    fn run_at(&self, at: Addr) -> Option<AddrRange> {
        let i = self.covered.partition_point(|r| r.end() <= at);
        self.covered.get(i).copied().filter(|r| r.contains(at))
    }

    /// Assemble from candidate regions, refusing anything that overlaps code
    /// that was actually walked.
    ///
    /// `code` must be sorted and disjoint, as [`crate::program::merge_ranges`]
    /// returns. Overlap is the one case where the decision is not close: a
    /// block is instructions that control reached, and no proof here outranks
    /// that.
    fn assemble(mut candidates: Vec<Region>, code: &[AddrRange]) -> DataMap {
        let before = candidates.len();
        candidates.retain(|r| !r.range.is_empty() && !overlaps(r.range, code));
        let refused = before - candidates.len();
        // Sorted and deduplicated so the answer does not depend on which
        // thread produced which region, which is gate G5.
        candidates.sort_unstable_by_key(|r| (r.range.start(), r.range.end(), r.proof));
        candidates.dedup();

        let mut covered: Vec<AddrRange> = Vec::with_capacity(candidates.len());
        for r in &candidates {
            match covered.last_mut() {
                Some(last) if r.range.start() <= last.end() => {
                    if r.range.end() > last.end() {
                        *last = AddrRange::new(last.start(), r.range.end()).unwrap_or(*last);
                    }
                }
                _ => covered.push(r.range),
            }
        }
        DataMap {
            regions: candidates,
            covered,
            refused,
        }
    }
}

/// True when `r` overlaps any of a sorted disjoint list.
fn overlaps(r: AddrRange, sorted: &[AddrRange]) -> bool {
    let i = sorted.partition_point(|c| c.end() <= r.start());
    sorted.get(i).is_some_and(|c| c.start() < r.end())
}

/// What a build should look for.
///
/// Split because the two callers want different things. The partition asks
/// before the gap scan and only cares about executable bytes, where scanning a
/// literal pool would invent a function; the published map is for consumers
/// and reports on the data sections too.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Sources {
    /// Walk the data sections looking for runs of pointers.
    pub(crate) pointers: bool,
}

/// Everything provably data in this program.
pub(crate) fn build(
    object: &Object,
    functions: &BTreeMap<Addr, Function>,
    sources: Sources,
    sink: Sink<'_>,
) -> DataMap {
    // Four sources, so four steps. Each is one pass and none of them is
    // interruptible part way, which is why the unit is the source rather than
    // the region.
    let steps = Some(if sources.pointers { 4 } else { 3 });
    sink.report(Stage::Data, 1, 0, steps);
    let mut candidates = declared_objects(object);
    sink.report(Stage::Data, 1, 1, steps);
    candidates.extend(jump_table_entries(functions));
    sink.report(Stage::Data, 1, 2, steps);
    candidates.extend(literal_pools(object, functions));
    sink.report(Stage::Data, 1, 3, steps);
    if sources.pointers {
        candidates.extend(pointer_runs(object));
        sink.report(Stage::Data, 1, 4, steps);
    }
    let code = crate::program::merge_ranges(
        functions
            .values()
            .flat_map(|f| f.cfg.blocks.values().map(|b| b.range)),
    );
    DataMap::assemble(candidates, &code)
}

/// Data the container's own symbol table declares, with its declared size.
///
/// A symbol of object kind with a size is the container saying, in the file,
/// that these bytes are not instructions. It is the only proof available for a
/// vtable from inside this crate: the scanning recovery that finds unnamed
/// ones lives above us, and a scan is an inference anyway.
fn declared_objects(object: &Object) -> Vec<Region> {
    let mem = &object.memory;
    object
        .symbols
        .iter()
        .filter(|s| {
            s.kind == e5r_format::SymbolKind::Object
                && s.size > 0
                && s.addr != Addr::ZERO
                && mem.is_mapped(s.addr)
        })
        .filter_map(|s| {
            let range = AddrRange::sized(s.addr, s.size)?;
            // The declared size can run past what is mapped in a malformed or
            // unusual file; the claim is only about bytes that exist.
            let end = range.end().min(mem.bounds()?.end());
            let range = AddrRange::new(range.start(), end)?;
            let proof = if is_vtable_name(&s.name) {
                Proof::Vtable
            } else {
                Proof::DeclaredObject
            };
            Some(Region { range, proof })
        })
        .collect()
}

/// Whether a mangled name is a virtual table.
fn is_vtable_name(name: &str) -> bool {
    // Itanium: `_ZTV<class>`, plus the construction tables a class with
    // virtual bases carries. Microsoft: `??_7<class>@@6B@`.
    name.starts_with("_ZTV") || name.starts_with("_ZTT") || name.starts_with("??_7")
}

/// The entries every recovered jump table was read out of.
fn jump_table_entries(functions: &BTreeMap<Addr, Function>) -> Vec<Region> {
    functions
        .values()
        .flat_map(|f| f.cfg.tables.iter())
        .filter_map(|t| {
            let len = t.entry_size.checked_mul(t.targets.len() as u64)?;
            Some(Region {
                range: AddrRange::sized(t.table, len)?,
                proof: Proof::JumpTable { branch: t.at },
            })
        })
        .collect()
}

/// Words an instruction reads through a pc-relative operand.
///
/// One streaming pass over the instructions of every function, on the same
/// threads the rest of analysis runs on. Streamed rather than decoded into a
/// list first, for the reason [`crate::program::build_xrefs`] gives: a decoded
/// instruction is much larger than what it contributes.
fn literal_pools(object: &Object, functions: &BTreeMap<Addr, Function>) -> Vec<Region> {
    let mem = &object.memory;
    let arch = object.arch.clone();
    let per_thread: Vec<Vec<Region>> = functions
        .values()
        .collect::<Vec<_>>()
        .par_iter()
        .fold(Vec::new, |mut out: Vec<Region>, f| {
            cfg::for_each_instruction(mem, &arch, &f.cfg, |i| {
                if let Some(r) = literal_read(&i, &arch, mem) {
                    out.push(r);
                }
            });
            out
        })
        .collect();
    per_thread.concat()
}

/// The bytes one instruction reads as data, when it names them pc-relatively.
fn literal_read(i: &Insn, arch: &Arch, mem: &MemoryMap) -> Option<Region> {
    let (at, size) = match arch {
        // A64 has one pc-relative load and the decoder resolves its target to
        // an `Addr` operand. `adr` and `adrp` carry an `Addr` too and read
        // nothing, so the mnemonic has to say which this is.
        Arch::AArch64 => {
            let size = match i.mnemonic {
                // The register width is the transfer width, except for the
                // sign-extending form, which writes 64 bits from 32.
                "ldrsw" => 4,
                "ldr" => match i.operands().first() {
                    Some(Operand::Reg(r)) => r.width.bytes(),
                    _ => return None,
                },
                _ => return None,
            };
            match i.operands().get(1) {
                Some(Operand::Addr(a)) => (*a, size),
                _ => return None,
            }
        }
        // Everywhere else, a memory operand whose base is the program counter.
        // A zero transfer size is an address computation such as `lea`, which
        // says nothing about what is there.
        _ => i.operands().iter().find_map(|o| match o {
            Operand::Mem(m) if m.size > 0 => Some((m.pc_target(i.end())?, m.size)),
            _ => None,
        })?,
    };
    if !mem.is_mapped(at) {
        return None;
    }
    Some(Region {
        range: AddrRange::sized(at, size)?,
        proof: Proof::LiteralPool { read_by: i.addr },
    })
}

/// Runs of pointer-sized words in the data sections.
///
/// Only in sections the container marks non-executable and that have bytes in
/// the file, so nothing here can cost a function: the partition never looks
/// there. What it buys is a map of the pointer tables an analyst and a later
/// data-to-data cross reference pass both want, and the claim it makes is
/// weaker than the other four, which is why it is its own proof.
fn pointer_runs(object: &Object) -> Vec<Region> {
    let width = object.bits.bytes();
    if !(2..=8).contains(&width) {
        return Vec::new();
    }
    let little = object.endian == e5r_core::Endian::Little;
    let mem = &object.memory;
    // Merged first, so "points into a known section" is one binary search per
    // word. It runs over every pointer-aligned word of every data section, and
    // a linear walk of the section list there is the difference between a pass
    // that costs nothing and one that shows up in the wall time.
    let known = crate::program::merge_ranges(
        object
            .sections
            .iter()
            .filter(|s| !s.range.is_empty())
            .map(|s| s.range),
    );

    let mut out: Vec<Region> = Vec::new();
    for s in &object.sections {
        if s.exec || s.file_size == 0 || s.range.is_empty() {
            continue;
        }
        let start = Addr(s.range.start().get().next_multiple_of(width));
        // Borrowed once rather than read word by word: `read_ptr` finds the
        // segment again for every call, which on a megabyte of `.data.rel.ro`
        // is a million lookups for the same segment.
        let len = s.range.end().get().saturating_sub(start.get()) & !(width - 1);
        let Some(bytes) = mem.slice(start, len) else {
            continue;
        };
        // A run in progress, so a table of a thousand pointers is one region
        // rather than a thousand.
        let mut run: Option<(Addr, Addr)> = None;
        for (n, word) in bytes.chunks_exact(width as usize).enumerate() {
            let at = start.wrapping_offset((n as u64 * width) as i64);
            let value = word_value(word, little);
            let points_in = value != 0 && in_any(Addr(value), &known);
            let next = at.wrapping_offset(width as i64);
            match (&mut run, points_in) {
                (Some((_, end)), true) => *end = next,
                (None, true) => run = Some((at, next)),
                (Some(_), false) => {
                    if let Some((lo, hi)) = run.take()
                        && let Some(range) = AddrRange::new(lo, hi)
                    {
                        out.push(Region {
                            range,
                            proof: Proof::Pointer,
                        });
                    }
                }
                (None, false) => {}
            }
        }
        if let Some((lo, hi)) = run
            && let Some(range) = AddrRange::new(lo, hi)
        {
            out.push(Region {
                range,
                proof: Proof::Pointer,
            });
        }
    }
    out
}

/// One word of a data section, in the image's byte order.
fn word_value(word: &[u8], little: bool) -> u64 {
    let mut v = 0u64;
    if little {
        for b in word.iter().rev() {
            v = (v << 8) | *b as u64;
        }
    } else {
        for b in word {
            v = (v << 8) | *b as u64;
        }
    }
    v
}

/// True when an address falls inside one of a sorted disjoint list of ranges.
fn in_any(at: Addr, sorted: &[AddrRange]) -> bool {
    let i = sorted.partition_point(|r| r.end() <= at);
    sorted.get(i).is_some_and(|r| r.contains(at))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(lo: u64, hi: u64, proof: Proof) -> Region {
        Region {
            range: AddrRange::new(Addr(lo), Addr(hi)).unwrap(),
            proof,
        }
    }

    #[test]
    fn a_region_that_overlaps_a_walked_block_is_refused() {
        // The one rule that matters: instructions control reached outrank
        // every proof in this module, because marking them data loses the
        // function silently.
        let code = [AddrRange::new(Addr(0x1000), Addr(0x1020)).unwrap()];
        let map = DataMap::assemble(
            vec![
                r(0x1010, 0x1018, Proof::DeclaredObject),
                r(0x1020, 0x1030, Proof::DeclaredObject),
            ],
            &code,
        );
        assert_eq!(map.len(), 1);
        assert_eq!(map.regions()[0].range.start(), Addr(0x1020));
        assert!(!map.contains(Addr(0x1010)));
        assert!(map.contains(Addr(0x1028)));
    }

    #[test]
    fn overlapping_proofs_are_both_kept_and_counted_once() {
        let map = DataMap::assemble(
            vec![
                r(0x2000, 0x2010, Proof::DeclaredObject),
                r(0x2000, 0x2008, Proof::JumpTable { branch: Addr(0x40) }),
            ],
            &[],
        );
        assert_eq!(map.len(), 2, "both reasons are worth keeping");
        assert_eq!(map.bytes(), 0x10, "the bytes are counted once");
        assert_eq!(map.end_of_run(Addr(0x2004)), Some(Addr(0x2010)));
    }

    #[test]
    fn a_run_skips_in_one_step() {
        // What the gap scan needs: adjacent regions are one run, so a pool of
        // a hundred words costs one step rather than a hundred.
        let map = DataMap::assemble(
            vec![
                r(0x3000, 0x3008, Proof::LiteralPool { read_by: Addr(1) }),
                r(0x3008, 0x3010, Proof::LiteralPool { read_by: Addr(2) }),
                r(0x3020, 0x3028, Proof::Pointer),
            ],
            &[],
        );
        assert_eq!(map.end_of_run(Addr(0x3000)), Some(Addr(0x3010)));
        assert_eq!(map.end_of_run(Addr(0x3018)), None);
        assert_eq!(map.bytes(), 0x18);
        assert_eq!(
            map.bytes_in(AddrRange::new(Addr(0x3004), Addr(0x3024)).unwrap()),
            0x0c + 0x04
        );
    }

    #[test]
    fn a_vtable_symbol_is_told_from_an_ordinary_object() {
        assert!(is_vtable_name("_ZTV7Derived"));
        assert!(is_vtable_name("??_7Shape@@6B@"));
        assert!(!is_vtable_name("_ZTS7Derived"));
        assert!(!is_vtable_name("some_table"));
    }
}
