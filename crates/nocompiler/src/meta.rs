//! The `.nocompiler.struct` section (docs/isa/metadata.md), version 2: per
//! function, the block/loop tree with labels, the callees by symbol, the
//! frame's partition into slots and address-taken ranges, the level the
//! checker reached and the stack depth. Little-endian; every position is an
//! offset from the function's entry, so a table stays true wherever the
//! linker puts the function.
//!
//! ```text
//! table    "NCST" version:u16 = 2 reserved:u16 = 0 nfunc:u32 func*
//! func     name:str size:u32 level:u8 reserved:u8 reserved:u16 frame:u32 depth:u32
//!          ncallees:u16 callee:str*
//!          nnodes:u32 node*                                   (pre-order)
//!          nslots:u16 slot*   nranges:u16 range*   next:u32 ext:[u8; next]
//! node     kind:u8 (0 block, 1 loop) depth:u8 reserved:u16 start:u32 end:u32 label:str
//! slot     off:u32 kind:u8 (0 save, 1 spill) reg:u8 reserved:u16
//! range    off:u32 len:u32 source:u8 (0 declared, 1 dwarf, 2 heuristic) reserved:u8 reserved:u16
//! str      len:u16 bytes:[u8; len]                             (UTF-8; len 0 = none for labels)
//! ```
//!
//! A section is one or more tables back to back: a linker concatenates the
//! sections of its inputs. Version 1 tables (absolute addresses, no labels or
//! partition) are still read. The section is not allocated, so stripping it or
//! never loading it changes nothing about how the binary runs.

use crate::isa::Reg;
use crate::profile::{FuncMeta, Kind, Level, Node, Range, RangeSource, Slot, SlotKind};
use std::collections::BTreeMap;

pub const SECTION: &str = ".nocompiler.struct";
const MAGIC: &[u8; 4] = b"NCST";
pub const VERSION: u16 = 2;
/// `depth` when it is not known.
const NO_DEPTH: u32 = u32::MAX;

/// A callee, as a table names it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Callee {
    /// By symbol (version 2).
    Sym(String),
    /// By entry address (version 1).
    Entry(u64),
}

/// One function as a table records it: `meta` at entry 0 (node positions
/// are offsets from the entry) with `meta.callees` empty, and the callees
/// as the table names them. `place` puts it at its entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub meta: FuncMeta,
    pub callees: Vec<Callee>,
    /// The table's version; version 1 records no frame partition.
    pub version: u16,
}

fn shift(nodes: &[Node], by: i128) -> Result<Vec<Node>, String> {
    nodes
        .iter()
        .map(|n| {
            let mv = |a: u64| {
                u64::try_from(a as i128 + by)
                    .map_err(|_| format!("{SECTION}: node at {a:#x} out of range"))
            };
            Ok(Node {
                kind: n.kind,
                start: mv(n.start)?,
                end: mv(n.end)?,
                label: n.label.clone(),
                children: shift(&n.children, by)?,
            })
        })
        .collect()
}

impl Record {
    /// The function at `entry`, its callees resolved through `entries`
    /// (symbol name to entry).
    pub fn place(&self, entry: u64, entries: &BTreeMap<String, u64>) -> Result<FuncMeta, String> {
        let mut callees = Vec::new();
        for c in &self.callees {
            callees.push(match c {
                Callee::Entry(e) => *e,
                Callee::Sym(s) => *entries.get(s).ok_or_else(|| {
                    format!(
                        "{SECTION}: {} calls {s}, which is not a function here",
                        self.meta.name
                    )
                })?,
            });
        }
        callees.sort();
        callees.dedup();
        Ok(FuncMeta {
            entry,
            nodes: shift(&self.meta.nodes, entry as i128)?,
            callees,
            ..self.meta.clone()
        })
    }
}

fn put_u16(o: &mut Vec<u8>, x: u16) {
    o.extend_from_slice(&x.to_le_bytes());
}
fn put_u32(o: &mut Vec<u8>, x: u32) {
    o.extend_from_slice(&x.to_le_bytes());
}
fn put_str(o: &mut Vec<u8>, s: &str) -> Result<(), String> {
    let n = u16::try_from(s.len()).map_err(|_| format!("{SECTION}: name {s:?} too long"))?;
    put_u16(o, n);
    o.extend_from_slice(s.as_bytes());
    Ok(())
}
fn rel(a: u64, entry: u64, what: &str) -> Result<u32, String> {
    a.checked_sub(entry)
        .and_then(|x| u32::try_from(x).ok())
        .ok_or_else(|| {
            format!("{SECTION}: {what} {a:#x} is not within 4 GiB after the entry {entry:#x}")
        })
}
fn u32_of(x: u64, what: &str) -> Result<u32, String> {
    u32::try_from(x).map_err(|_| format!("{SECTION}: {what} {x} does not fit in 32 bits"))
}

fn put_nodes(o: &mut Vec<u8>, nodes: &[Node], depth: u8, entry: u64) -> Result<(), String> {
    for n in nodes {
        o.push(match n.kind {
            Kind::Block => 0,
            Kind::Loop => 1,
        });
        o.push(depth);
        put_u16(o, 0);
        put_u32(o, rel(n.start, entry, "node start")?);
        put_u32(o, rel(n.end, entry, "node end")?);
        match &n.label {
            Some(l) if l.is_empty() => return Err(format!("{SECTION}: empty label")),
            Some(l) => put_str(o, l)?,
            None => put_u16(o, 0),
        }
        put_nodes(o, &n.children, depth + 1, entry)?;
    }
    Ok(())
}

fn count(nodes: &[Node]) -> u32 {
    nodes.iter().map(|n| 1 + count(&n.children)).sum()
}

/// One version-2 table of `funcs`; a callee's entry is written as the name
/// `names` gives it.
pub fn encode(funcs: &[FuncMeta], names: &BTreeMap<u64, String>) -> Result<Vec<u8>, String> {
    let mut o = Vec::new();
    o.extend_from_slice(MAGIC);
    put_u16(&mut o, VERSION);
    put_u16(&mut o, 0);
    put_u32(&mut o, funcs.len() as u32);
    for f in funcs {
        put_str(&mut o, &f.name)?;
        put_u32(&mut o, u32_of(f.size, "size")?);
        o.push(match f.level {
            Level::L0 => 0,
            Level::L1 => 1,
            Level::L2 => 2,
        });
        o.push(0);
        put_u16(&mut o, 0);
        put_u32(&mut o, u32_of(f.frame, "frame")?);
        put_u32(
            &mut o,
            match f.depth {
                None => NO_DEPTH,
                Some(d) if d < NO_DEPTH as u64 => d as u32,
                Some(d) => return Err(format!("{SECTION}: depth {d} too large")),
            },
        );
        let mut cs: Vec<&String> = Vec::new();
        for c in &f.callees {
            cs.push(names.get(c).ok_or_else(|| {
                format!("{SECTION}: {} calls {c:#x}, which has no symbol", f.name)
            })?);
        }
        cs.sort();
        cs.dedup();
        put_u16(
            &mut o,
            u16::try_from(cs.len()).map_err(|_| "too many callees")?,
        );
        for c in cs {
            put_str(&mut o, c)?;
        }
        put_u32(&mut o, count(&f.nodes));
        put_nodes(&mut o, &f.nodes, 0, f.entry)?;
        put_u16(
            &mut o,
            u16::try_from(f.slots.len()).map_err(|_| "too many slots")?,
        );
        for s in &f.slots {
            put_u32(&mut o, u32_of(s.off, "slot offset")?);
            match s.kind {
                SlotKind::Save(r) => {
                    o.push(0);
                    o.push(r.0);
                }
                SlotKind::Spill => {
                    o.push(1);
                    o.push(0);
                }
            }
            put_u16(&mut o, 0);
        }
        put_u16(
            &mut o,
            u16::try_from(f.ranges.len()).map_err(|_| "too many ranges")?,
        );
        for r in &f.ranges {
            put_u32(&mut o, u32_of(r.off, "range offset")?);
            put_u32(&mut o, u32_of(r.len, "range length")?);
            o.push(match r.source {
                RangeSource::Declared => 0,
                RangeSource::Dwarf => 1,
                RangeSource::Heuristic => 2,
            });
            o.push(0);
            put_u16(&mut o, 0);
        }
        put_u32(&mut o, u32_of(f.ext.len() as u64, "extension length")?);
        o.extend_from_slice(&f.ext);
    }
    Ok(o)
}

struct Reader<'a> {
    d: &'a [u8],
    o: usize,
}

impl Reader<'_> {
    fn take(&mut self, n: usize) -> Result<&[u8], String> {
        let s = self
            .d
            .get(self.o..self.o + n)
            .ok_or_else(|| format!("{SECTION} truncated at {}", self.o))?;
        self.o += n;
        Ok(s)
    }
    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }
    fn u16(&mut self) -> Result<u16, String> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn str(&mut self) -> Result<String, String> {
        let n = self.u16()? as usize;
        String::from_utf8(self.take(n)?.to_vec())
            .map_err(|_| format!("{SECTION}: a name is not UTF-8"))
    }
    fn zero(&mut self, n: usize) -> Result<(), String> {
        if self.take(n)?.iter().any(|&b| b != 0) {
            return Err(format!(
                "{SECTION}: reserved bytes not zero at {}",
                self.o - n
            ));
        }
        Ok(())
    }
}

/// Rebuild the tree from (depth, node) in pre-order.
fn build(flat: &[(u8, Node)], i: &mut usize, depth: u8) -> Result<Vec<Node>, String> {
    let mut out = Vec::new();
    while *i < flat.len() && flat[*i].0 >= depth {
        if flat[*i].0 > depth {
            return Err(format!(
                "{SECTION}: node depth jumps from {depth} to {}",
                flat[*i].0
            ));
        }
        let mut n = flat[*i].1.clone();
        *i += 1;
        n.children = build(flat, i, depth + 1)?;
        out.push(n);
    }
    Ok(out)
}

fn tree(flat: Vec<(u8, Node)>, name: &str) -> Result<Vec<Node>, String> {
    let mut i = 0;
    let nodes = build(&flat, &mut i, 0)?;
    if i != flat.len() {
        return Err(format!("{SECTION}: {name}: first node is not at depth 0"));
    }
    Ok(nodes)
}

fn kind(k: u8) -> Result<Kind, String> {
    match k {
        0 => Ok(Kind::Block),
        1 => Ok(Kind::Loop),
        k => Err(format!("{SECTION}: node kind {k}")),
    }
}

fn func_v2(r: &mut Reader) -> Result<Record, String> {
    let name = r.str()?;
    let size = r.u32()? as u64;
    let level = match r.u8()? {
        0 => Level::L0,
        1 => Level::L1,
        2 => Level::L2,
        l => return Err(format!("{SECTION}: {name}: level {l}")),
    };
    r.zero(3)?;
    let frame = r.u32()? as u64;
    let depth = match r.u32()? {
        NO_DEPTH => None,
        d => Some(d as u64),
    };
    let nc = r.u16()?;
    let mut callees = Vec::new();
    for _ in 0..nc {
        callees.push(Callee::Sym(r.str()?));
    }
    let nn = r.u32()?;
    let mut flat = Vec::new();
    for _ in 0..nn {
        let k = kind(r.u8()?)?;
        let d = r.u8()?;
        r.zero(2)?;
        let start = r.u32()? as u64;
        let end = r.u32()? as u64;
        let label = r.str()?;
        flat.push((
            d,
            Node {
                kind: k,
                start,
                end,
                label: (!label.is_empty()).then_some(label),
                children: vec![],
            },
        ));
    }
    let nodes = tree(flat, &name)?;
    let mut slots = Vec::new();
    for _ in 0..r.u16()? {
        let off = r.u32()? as u64;
        let k = r.u8()?;
        let reg = r.u8()?;
        r.zero(2)?;
        let kind = match (k, reg) {
            (0, reg) if reg < 32 => SlotKind::Save(Reg(reg)),
            (1, 0) => SlotKind::Spill,
            _ => return Err(format!("{SECTION}: {name}: slot kind {k} register {reg}")),
        };
        slots.push(Slot { off, kind });
    }
    let mut ranges = Vec::new();
    for _ in 0..r.u16()? {
        let off = r.u32()? as u64;
        let len = r.u32()? as u64;
        let source = match r.u8()? {
            0 => RangeSource::Declared,
            1 => RangeSource::Dwarf,
            2 => RangeSource::Heuristic,
            s => return Err(format!("{SECTION}: {name}: range source {s}")),
        };
        r.zero(3)?;
        ranges.push(Range { off, len, source });
    }
    let next = r.u32()? as usize;
    let ext = r.take(next)?.to_vec();
    Ok(Record {
        meta: FuncMeta {
            name,
            entry: 0,
            size,
            level,
            frame,
            depth,
            callees: vec![],
            nodes,
            slots,
            ranges,
            ext,
        },
        callees,
        version: 2,
    })
}

/// A version-1 function: absolute addresses, made relative to its entry.
fn func_v1(r: &mut Reader) -> Result<Record, String> {
    let entry = r.u64()?;
    let size = r.u64()?;
    let frame = r.u64()?;
    let len = r.u16()? as usize;
    let name = String::from_utf8(r.take(len)?.to_vec())
        .map_err(|_| format!("{SECTION}: name not UTF-8"))?;
    let mut callees = Vec::new();
    for _ in 0..r.u32()? {
        callees.push(Callee::Entry(r.u64()?));
    }
    let nn = r.u32()?;
    let mut flat = Vec::new();
    for _ in 0..nn {
        let k = kind(r.u8()?)?;
        let d = r.u8()?;
        r.u16()?;
        let start = r.u64()?;
        let end = r.u64()?;
        flat.push((
            d,
            Node {
                kind: k,
                start,
                end,
                label: None,
                children: vec![],
            },
        ));
    }
    let nodes = shift(&tree(flat, &name)?, -(entry as i128))?;
    Ok(Record {
        meta: FuncMeta {
            name,
            entry: 0,
            size,
            level: Level::L1,
            frame,
            depth: None,
            callees: vec![],
            nodes,
            slots: vec![],
            ranges: vec![],
            ext: vec![],
        },
        callees,
        version: 1,
    })
}

/// Every function of every table in the section.
pub fn decode(d: &[u8]) -> Result<Vec<Record>, String> {
    let mut r = Reader { d, o: 0 };
    let mut out = Vec::new();
    if d.is_empty() {
        return Err(format!("{SECTION}: empty"));
    }
    while r.o < d.len() {
        if r.take(4)? != MAGIC {
            return Err(format!("{SECTION}: bad magic at {}", r.o - 4));
        }
        let ver = r.u16()?;
        r.zero(2)?;
        let n = r.u32()?;
        for _ in 0..n {
            out.push(match ver {
                1 => func_v1(&mut r)?,
                2 => func_v2(&mut r)?,
                v => return Err(format!("{SECTION}: version {v}; this tool reads 1 and 2")),
            });
        }
    }
    Ok(out)
}
