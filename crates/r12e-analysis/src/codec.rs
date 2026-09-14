//! Turning analysis results into cache payloads and back.
//!
//! Fixed-width little-endian fields, no self-description, no schema in the
//! file: the version in the entry header says what the layout is, and a
//! mismatch is a miss rather than a negotiation. Enum values are mapped
//! through an explicit match in both directions, so adding a variant upstream
//! fails the build here instead of silently changing what an old cache file
//! means.
//!
//! Every decoder returns `Option` and every count is checked against the bytes
//! remaining before anything is allocated. A damaged file makes the decode
//! return `None`; it never panics and never returns a half-built answer.

use std::collections::{BTreeMap, BTreeSet};

use r12e_core::{Addr, AddrRange, Evidence, Provenance};

use crate::cache::{Dec, Enc};
use crate::cfg::{Block, BlockInterner, Cfg, Halt, RawCfg, Terminator};
use crate::jumptable::{JumpTable, TableKind};
use crate::program::Function;
use crate::strings::{Encoding, Found};
use crate::xref::{Xref, XrefIndex, XrefKind};

/// Smallest number of bytes one encoded item of each kind can occupy, used to
/// reject a count that the rest of the file could not possibly hold.
const MIN_FUNCTION: usize = 8 + 1 + 16 + 2 + 8 + 8 + 4 + 1 + 4;
const MIN_BLOCK: usize = 8 + 8 + 4 + 1 + 1 + 8;
const MIN_XREF: usize = 8 + 8 + 1;
const MIN_STRING: usize = 8 + 8 + 1 + 4;
const MIN_TABLE: usize = 8 + 8 + 8 + 1 + 8 + 1 + 8 + 1;

/// Functions, their graphs, the round count and the no-return set.
pub(crate) fn encode_functions(
    functions: &BTreeMap<Addr, Function>,
    noreturn: &BTreeSet<Addr>,
    rounds: usize,
) -> Vec<u8> {
    // Sized from what is actually there rather than from a guess per function:
    // on a 139 MB binary the payload is 350 MB, and letting a Vec double its
    // way there copies most of that several times over on a machine that is
    // already short of memory. The per-item figures are the encoded sizes
    // below, rounded up.
    let blocks: usize = functions.values().map(|f| f.cfg.blocks.len()).sum();
    let successors: usize = functions
        .values()
        .flat_map(|f| f.cfg.blocks.values())
        .map(|b| b.successors.len())
        .sum();
    let calls: usize = functions.values().map(|f| f.cfg.calls.len()).sum();
    let mut e = Enc::with_capacity(
        64 + functions.len() * 64 + blocks * 26 + successors * 8 + calls * 8 + noreturn.len() * 8,
    );
    e.u64(rounds as u64);
    e.u64(functions.len() as u64);
    for f in functions.values() {
        e.u64(f.entry.get());
        e.opt_str(f.name.as_deref());
        e.u64(f.range.start().get());
        e.u64(f.range.end().get());
        encode_provenance(&mut e, &f.provenance);
        encode_cfg(&mut e, &f.cfg);
    }
    e.u64(noreturn.len() as u64);
    for a in noreturn {
        e.u64(a.get());
    }
    e.finish()
}

/// The inverse of [`encode_functions`]. `None` on any damage.
#[allow(clippy::type_complexity)]
pub(crate) fn decode_functions(
    bytes: &[u8],
) -> Option<(BTreeMap<Addr, Function>, BTreeSet<Addr>, usize)> {
    let mut d = Dec::new(bytes);
    let rounds = usize::try_from(d.u64()?).ok()?;
    let n = d.count(MIN_FUNCTION)?;
    let mut functions = BTreeMap::new();
    // A cache entry is read back into the same one-table-per-program shape the
    // analysis builds, so a hit costs what a miss would have kept.
    let mut interner = BlockInterner::default();
    for _ in 0..n {
        let entry = Addr::new(d.u64()?);
        let name = d.opt_str()?;
        let range = AddrRange::new(Addr::new(d.u64()?), Addr::new(d.u64()?))?;
        let provenance = decode_provenance(&mut d)?;
        let cfg = interner.install(decode_cfg(&mut d)?);
        functions.insert(
            entry,
            Function {
                entry,
                name,
                range,
                cfg,
                provenance,
            },
        );
    }
    interner.publish(functions.values_mut().map(|f| &mut f.cfg));
    let n = d.count(8)?;
    let mut noreturn = BTreeSet::new();
    for _ in 0..n {
        noreturn.insert(Addr::new(d.u64()?));
    }
    // A file with bytes left over is a file written by something else.
    (d.remaining() == 0).then_some((functions, noreturn, rounds))
}

fn encode_provenance(e: &mut Enc, p: &Provenance) {
    e.u8(evidence_code(p.best));
    e.u8(p.corroborating.len().min(u8::MAX as usize) as u8);
    for ev in p.corroborating.iter().take(u8::MAX as usize) {
        e.u8(evidence_code(*ev));
    }
}

fn decode_provenance(d: &mut Dec<'_>) -> Option<Provenance> {
    let best = evidence_from(d.u8()?)?;
    let n = d.u8()? as usize;
    if n > d.remaining() {
        return None;
    }
    let mut corroborating = Vec::with_capacity(n);
    for _ in 0..n {
        corroborating.push(evidence_from(d.u8()?)?);
    }
    Some(Provenance {
        best,
        corroborating,
    })
}

fn encode_cfg(e: &mut Enc, c: &Cfg) {
    e.u64(c.entry.get());
    e.u64(c.blocks.len() as u64);
    for b in c.blocks.values() {
        e.u64(b.range.start().get());
        e.u64(b.range.end().get());
        e.u32(b.insns);
        e.u8(terminator_code(b.terminator));
        e.bool(b.unresolved);
        e.u32(b.successors.len() as u32);
        for s in &b.successors {
            e.u64(s.get());
        }
    }
    e.u32(c.calls.len() as u32);
    for a in &c.calls {
        e.u64(a.get());
    }
    e.bool(c.has_indirect);
    e.u8(halt_code(c.halt));
    e.u32(c.tables.len() as u32);
    for t in &c.tables {
        encode_table(e, t);
    }
}

fn decode_cfg(d: &mut Dec<'_>) -> Option<RawCfg> {
    let entry = Addr::new(d.u64()?);
    let n = d.count(MIN_BLOCK)?;
    let mut blocks = Vec::with_capacity(n);
    for _ in 0..n {
        let range = AddrRange::new(Addr::new(d.u64()?), Addr::new(d.u64()?))?;
        let insns = d.u32()?;
        let terminator = terminator_from(d.u8()?)?;
        let unresolved = d.bool()?;
        let nsucc = d.u32()? as usize;
        if nsucc.saturating_mul(8) > d.remaining() {
            return None;
        }
        let mut successors = Vec::with_capacity(nsucc);
        for _ in 0..nsucc {
            successors.push(Addr::new(d.u64()?));
        }
        blocks.push((
            range.start(),
            Block {
                range,
                successors,
                insns,
                unresolved,
                terminator,
            },
        ));
    }
    let ncalls = d.u32()? as usize;
    if ncalls.saturating_mul(8) > d.remaining() {
        return None;
    }
    let mut calls = Vec::with_capacity(ncalls);
    for _ in 0..ncalls {
        calls.push(Addr::new(d.u64()?));
    }
    let has_indirect = d.bool()?;
    let halt = halt_from(d.u8()?)?;
    let ntables = d.u32()? as usize;
    if ntables.saturating_mul(MIN_TABLE) > d.remaining() {
        return None;
    }
    let mut tables = Vec::with_capacity(ntables);
    for _ in 0..ntables {
        tables.push(decode_table(d)?);
    }
    Some(RawCfg {
        entry,
        blocks,
        calls,
        has_indirect,
        tables,
        halt,
    })
}

fn encode_table(e: &mut Enc, t: &JumpTable) {
    e.u64(t.at.get());
    e.u64(t.table.get());
    e.u64(t.entry_size);
    e.u8(table_kind_code(t.kind));
    e.u64(t.base.get());
    e.u8(t.shift);
    e.bool(t.bounded_by_scan);
    e.u64(t.targets.len() as u64);
    for a in &t.targets {
        e.u64(a.get());
    }
}

fn decode_table(d: &mut Dec<'_>) -> Option<JumpTable> {
    let at = Addr::new(d.u64()?);
    let table = Addr::new(d.u64()?);
    let entry_size = d.u64()?;
    let kind = table_kind_from(d.u8()?)?;
    let base = Addr::new(d.u64()?);
    let shift = d.u8()?;
    let bounded_by_scan = d.bool()?;
    let n = d.count(8)?;
    let mut targets = Vec::with_capacity(n);
    for _ in 0..n {
        targets.push(Addr::new(d.u64()?));
    }
    Some(JumpTable {
        at,
        table,
        entry_size,
        kind,
        base,
        shift,
        targets,
        bounded_by_scan,
    })
}

/// The cross reference index, in `by_from` order.
pub(crate) fn encode_xrefs(index: &XrefIndex) -> Vec<u8> {
    let all = index.all();
    let mut e = Enc::with_capacity(8 + all.len() * MIN_XREF);
    e.u64(all.len() as u64);
    for x in all {
        e.u64(x.from.get());
        e.u64(x.to.get());
        e.u8(xref_kind_code(x.kind));
    }
    e.finish()
}

/// The inverse of [`encode_xrefs`]. `None` on any damage.
pub(crate) fn decode_xrefs(bytes: &[u8]) -> Option<XrefIndex> {
    let mut d = Dec::new(bytes);
    let n = d.count(MIN_XREF)?;
    let mut refs = Vec::with_capacity(n);
    for _ in 0..n {
        refs.push(Xref {
            from: Addr::new(d.u64()?),
            to: Addr::new(d.u64()?),
            kind: xref_kind_from(d.u8()?)?,
        });
    }
    (d.remaining() == 0).then(|| XrefIndex::build(refs))
}

/// Extracted strings, in the order the scan reported them.
pub(crate) fn encode_strings(found: &[Found]) -> Vec<u8> {
    let mut e = Enc::with_capacity(8 + found.len() * 48);
    e.u64(found.len() as u64);
    for f in found {
        e.u64(f.addr.get());
        e.u64(f.len);
        e.u8(encoding_code(f.encoding));
        e.str(&f.text);
    }
    e.finish()
}

/// The inverse of [`encode_strings`]. `None` on any damage.
pub(crate) fn decode_strings(bytes: &[u8]) -> Option<Vec<Found>> {
    let mut d = Dec::new(bytes);
    let n = d.count(MIN_STRING)?;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(Found {
            addr: Addr::new(d.u64()?),
            len: d.u64()?,
            encoding: encoding_from(d.u8()?)?,
            text: d.str()?,
        });
    }
    (d.remaining() == 0).then_some(out)
}

/// Evidence is written as a number, so the mapping is spelled out rather than
/// taken from the declaration order of the enum: a variant inserted upstream
/// must not change what an existing cache file says.
fn evidence_code(e: Evidence) -> u8 {
    match e {
        Evidence::SymbolTable => 1,
        Evidence::DebugInfo => 2,
        Evidence::CodeSymbol => 3,
        Evidence::DynamicSymbol => 4,
        Evidence::EntryPoint => 5,
        Evidence::InitArray => 6,
        Evidence::EhFrame => 7,
        Evidence::PeUnwind => 8,
        Evidence::GuardTable => 9,
        Evidence::MachFunctionStarts => 10,
        Evidence::GoPclntab => 11,
        Evidence::ObjcMetadata => 12,
        Evidence::SwiftMetadata => 13,
        Evidence::RustPanic => 14,
        Evidence::Pdb => 15,
        Evidence::Export => 16,
        Evidence::ImportThunk => 17,
        Evidence::CallTarget => 18,
        Evidence::BranchTarget => 19,
        Evidence::JumpTable => 20,
        Evidence::ProloguePattern => 21,
        Evidence::LinearSweep => 22,
        Evidence::DataPointer => 23,
        Evidence::Annotation => 24,
    }
}

fn evidence_from(v: u8) -> Option<Evidence> {
    Some(match v {
        1 => Evidence::SymbolTable,
        2 => Evidence::DebugInfo,
        3 => Evidence::CodeSymbol,
        4 => Evidence::DynamicSymbol,
        5 => Evidence::EntryPoint,
        6 => Evidence::InitArray,
        7 => Evidence::EhFrame,
        8 => Evidence::PeUnwind,
        9 => Evidence::GuardTable,
        10 => Evidence::MachFunctionStarts,
        11 => Evidence::GoPclntab,
        12 => Evidence::ObjcMetadata,
        13 => Evidence::SwiftMetadata,
        14 => Evidence::RustPanic,
        15 => Evidence::Pdb,
        16 => Evidence::Export,
        17 => Evidence::ImportThunk,
        18 => Evidence::CallTarget,
        19 => Evidence::BranchTarget,
        20 => Evidence::JumpTable,
        21 => Evidence::ProloguePattern,
        22 => Evidence::LinearSweep,
        23 => Evidence::DataPointer,
        24 => Evidence::Annotation,
        _ => return None,
    })
}

fn terminator_code(t: Terminator) -> u8 {
    match t {
        Terminator::Flow => 1,
        Terminator::Return => 2,
        Terminator::TailCall => 3,
        Terminator::NoReturnCall => 4,
        Terminator::Trap => 5,
        Terminator::Unresolved => 6,
    }
}

fn terminator_from(v: u8) -> Option<Terminator> {
    Some(match v {
        1 => Terminator::Flow,
        2 => Terminator::Return,
        3 => Terminator::TailCall,
        4 => Terminator::NoReturnCall,
        5 => Terminator::Trap,
        6 => Terminator::Unresolved,
        _ => return None,
    })
}

fn halt_code(h: Halt) -> u8 {
    match h {
        Halt::Complete => 1,
        Halt::InstructionCap => 2,
        Halt::BlockCap => 3,
        Halt::Undecodable => 4,
    }
}

fn halt_from(v: u8) -> Option<Halt> {
    Some(match v {
        1 => Halt::Complete,
        2 => Halt::InstructionCap,
        3 => Halt::BlockCap,
        4 => Halt::Undecodable,
        _ => return None,
    })
}

fn table_kind_code(k: TableKind) -> u8 {
    match k {
        TableKind::Absolute => 1,
        TableKind::RelativeToBase => 2,
        TableKind::RelativeToEntry => 3,
    }
}

fn table_kind_from(v: u8) -> Option<TableKind> {
    Some(match v {
        1 => TableKind::Absolute,
        2 => TableKind::RelativeToBase,
        3 => TableKind::RelativeToEntry,
        _ => return None,
    })
}

fn xref_kind_code(k: XrefKind) -> u8 {
    match k {
        XrefKind::Call => 1,
        XrefKind::Branch => 2,
        XrefKind::Data => 3,
        XrefKind::Read => 4,
        XrefKind::Write => 5,
    }
}

fn xref_kind_from(v: u8) -> Option<XrefKind> {
    Some(match v {
        1 => XrefKind::Call,
        2 => XrefKind::Branch,
        3 => XrefKind::Data,
        4 => XrefKind::Read,
        5 => XrefKind::Write,
        _ => return None,
    })
}

fn encoding_code(e: Encoding) -> u8 {
    match e {
        Encoding::Ascii => 1,
        Encoding::Utf8 => 2,
        Encoding::Utf16 => 3,
    }
}

fn encoding_from(v: u8) -> Option<Encoding> {
    Some(match v {
        1 => Encoding::Ascii,
        2 => Encoding::Utf8,
        3 => Encoding::Utf16,
        _ => return None,
    })
}
