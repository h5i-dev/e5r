//! The `.nocompiler.struct` section (docs/isa/metadata.md): the block/loop tree,
//! frame size and callees of every function, little-endian.
//!
//! ```text
//! header   "NCST"         version:u16 = 1  reserved:u16 = 0  nfunc:u32
//! func     entry:u64 size:u64 frame:u64 name_len:u16 name:[u8]
//!          ncallees:u32 callee:u64*
//!          nnodes:u32 node*                      (pre-order)
//! node     kind:u8 (0 block, 1 loop) depth:u8 reserved:u16 start:u64 end:u64
//! ```
//!
//! The section is not allocated, so stripping it or never loading it changes
//! nothing about how the binary runs.

use crate::profile::{FuncMeta, Kind, Node};

pub const SECTION: &str = ".nocompiler.struct";
const MAGIC: &[u8; 4] = b"NCST";
const VERSION: u16 = 1;

fn put_nodes(out: &mut Vec<u8>, nodes: &[Node], depth: u8) {
    for n in nodes {
        out.push(match n.kind {
            Kind::Block => 0,
            Kind::Loop => 1,
        });
        out.push(depth);
        out.extend_from_slice(&0u16.to_le_bytes());
        out.extend_from_slice(&n.start.to_le_bytes());
        out.extend_from_slice(&n.end.to_le_bytes());
        put_nodes(out, &n.children, depth + 1);
    }
}

fn count(nodes: &[Node]) -> u32 {
    nodes.iter().map(|n| 1 + count(&n.children)).sum()
}

pub fn encode(funcs: &[FuncMeta]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&VERSION.to_le_bytes());
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&(funcs.len() as u32).to_le_bytes());
    for f in funcs {
        out.extend_from_slice(&f.entry.to_le_bytes());
        out.extend_from_slice(&f.size.to_le_bytes());
        out.extend_from_slice(&f.frame.to_le_bytes());
        out.extend_from_slice(&(f.name.len() as u16).to_le_bytes());
        out.extend_from_slice(f.name.as_bytes());
        out.extend_from_slice(&(f.callees.len() as u32).to_le_bytes());
        for c in &f.callees {
            out.extend_from_slice(&c.to_le_bytes());
        }
        out.extend_from_slice(&count(&f.nodes).to_le_bytes());
        put_nodes(&mut out, &f.nodes, 0);
    }
    out
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

pub fn decode(d: &[u8]) -> Result<Vec<FuncMeta>, String> {
    let mut r = Reader { d, o: 0 };
    if r.take(4)? != MAGIC {
        return Err(format!("{SECTION}: bad magic"));
    }
    let ver = r.u16()?;
    if ver != VERSION {
        return Err(format!(
            "{SECTION}: version {ver}, this tool reads {VERSION}"
        ));
    }
    r.u16()?;
    let n = r.u32()?;
    let mut funcs = Vec::new();
    for _ in 0..n {
        let entry = r.u64()?;
        let size = r.u64()?;
        let frame = r.u64()?;
        let len = r.u16()? as usize;
        let name = String::from_utf8(r.take(len)?.to_vec())
            .map_err(|_| format!("{SECTION}: name not UTF-8"))?;
        let nc = r.u32()?;
        let mut callees = Vec::new();
        for _ in 0..nc {
            callees.push(r.u64()?);
        }
        let nn = r.u32()?;
        let mut flat = Vec::new();
        for _ in 0..nn {
            let kind = match r.u8()? {
                0 => Kind::Block,
                1 => Kind::Loop,
                k => return Err(format!("{SECTION}: node kind {k}")),
            };
            let depth = r.u8()?;
            r.u16()?;
            let start = r.u64()?;
            let end = r.u64()?;
            flat.push((
                depth,
                Node {
                    kind,
                    start,
                    end,
                    children: vec![],
                },
            ));
        }
        let mut i = 0;
        let nodes = build(&flat, &mut i, 0)?;
        if i != flat.len() {
            return Err(format!("{SECTION}: {name}: first node is not at depth 0"));
        }
        funcs.push(FuncMeta {
            name,
            entry,
            size,
            frame,
            callees,
            nodes,
        });
    }
    if r.o != d.len() {
        return Err(format!("{SECTION}: {} trailing bytes", d.len() - r.o));
    }
    Ok(funcs)
}
