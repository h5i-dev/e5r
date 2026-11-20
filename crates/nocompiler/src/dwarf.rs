//! Just enough DWARF (versions 4 and 5) to give the frame rule R6 the
//! lengths of address-taken stack variables (v1 decision 5): for every
//! function, the variables the debug information places in its frame, as
//! frame offset (from the bottom of the frame) and size in bytes.
//!
//! A variable is in the frame when its location is `DW_OP_fbreg k` with the
//! function's frame base `DW_OP_reg2` (`sp`, which after the prologue is the
//! bottom of the frame), or `DW_OP_breg2 k`, directly or in any entry of a
//! location list. Sizes come from the type: `DW_AT_byte_size`, through
//! typedefs and qualifiers, arrays as element size times the counts.
//!
//! Not trusted, and not even needed: without debug information `annotate`
//! falls back to a heuristic, and either way a wrong length only makes a
//! function miss L2 or a proof fail. Anything this reader does not
//! understand ends its reading of that unit, silently.

use crate::elf::Elf;
use std::collections::BTreeMap;

/// Function entry (`DW_AT_low_pc`) to (frame offset, size) of its variables.
pub type FrameVars = BTreeMap<u64, BTreeMap<u64, u64>>;

struct R<'a> {
    d: &'a [u8],
    o: usize,
}

impl<'a> R<'a> {
    fn new(d: &'a [u8], o: usize) -> Self {
        R { d, o }
    }
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let s = self.d.get(self.o..self.o.checked_add(n)?)?;
        self.o += n;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }
    fn uint(&mut self, n: usize) -> Option<u64> {
        let s = self.take(n)?;
        Some(s.iter().rev().fold(0u64, |a, &b| a << 8 | b as u64))
    }
    fn uleb(&mut self) -> Option<u64> {
        let (mut v, mut sh) = (0u64, 0);
        loop {
            let b = self.u8()?;
            if sh < 64 {
                v |= ((b & 0x7f) as u64) << sh;
            }
            sh += 7;
            if b & 0x80 == 0 {
                return Some(v);
            }
        }
    }
    fn sleb(&mut self) -> Option<i64> {
        let (mut v, mut sh) = (0i64, 0);
        loop {
            let b = self.u8()?;
            if sh < 64 {
                v |= ((b & 0x7f) as i64) << sh;
            }
            sh += 7;
            if b & 0x80 == 0 {
                if sh < 64 && b & 0x40 != 0 {
                    v |= -1i64 << sh;
                }
                return Some(v);
            }
        }
    }
    fn cstr(&mut self) -> Option<()> {
        while self.u8()? != 0 {}
        Some(())
    }
}

#[derive(Clone, Copy)]
struct Spec {
    at: u64,
    form: u64,
    implicit: i64,
}

struct Abbrev {
    tag: u64,
    children: bool,
    attrs: Vec<Spec>,
}

fn abbrevs(d: &[u8], off: usize) -> Option<BTreeMap<u64, Abbrev>> {
    let mut r = R::new(d, off);
    let mut out = BTreeMap::new();
    loop {
        let code = r.uleb()?;
        if code == 0 {
            return Some(out);
        }
        let tag = r.uleb()?;
        let children = r.u8()? != 0;
        let mut attrs = Vec::new();
        loop {
            let at = r.uleb()?;
            let form = r.uleb()?;
            if at == 0 && form == 0 {
                break;
            }
            let implicit = if form == 0x21 { r.sleb()? } else { 0 };
            attrs.push(Spec { at, form, implicit });
        }
        out.insert(
            code,
            Abbrev {
                tag,
                children,
                attrs,
            },
        );
    }
}

/// An attribute's value, as far as this reader needs it.
#[derive(Clone, Debug)]
enum Val {
    U(u64),
    /// An index into `.debug_addr` (DWARF 5).
    AddrX(u64),
    /// A reference, as an offset in `.debug_info`.
    Ref(u64),
    /// A location expression.
    Expr(Vec<u8>),
    /// An offset into a location-list section, or a `loclistx` index.
    Sec(u64),
    LocX(u64),
    Other,
}

struct Unit {
    off: usize,
    end: usize,
    version: u16,
    addr_size: u8,
    hdr_end: usize,
}

struct Ctx<'a> {
    info: &'a [u8],
    addr: &'a [u8],
    loc: &'a [u8],
    loclists: &'a [u8],
}

fn value(r: &mut R, form: u64, u: &Unit, implicit: i64) -> Option<Val> {
    let off64 = |r: &mut R| r.uint(4); // 32-bit DWARF only
    Some(match form {
        0x01 => Val::U(r.uint(u.addr_size as usize)?), // addr
        0x0b => Val::U(r.uint(1)?),                    // data1
        0x05 => Val::U(r.uint(2)?),                    // data2
        0x06 => Val::U(r.uint(4)?),                    // data4
        0x07 => Val::U(r.uint(8)?),                    // data8
        0x1e => Val::U(r.take(16).map(|_| 0)?),        // data16
        0x0d => Val::U(r.sleb()? as u64),              // sdata
        0x0f => Val::U(r.uleb()?),                     // udata
        0x21 => Val::U(implicit as u64),               // implicit_const
        0x08 => {
            r.cstr()?;
            Val::Other
        } // string
        0x0e | 0x1f => Val::U(off64(r)?),              // strp, line_strp
        0x1a => Val::U(r.uleb()?),                     // strx
        0x25 => Val::U(r.uint(1)?),                    // strx1..4
        0x26 => Val::U(r.uint(2)?),
        0x27 => Val::U(r.uint(3)?),
        0x28 => Val::U(r.uint(4)?),
        0x1b => Val::AddrX(r.uleb()?),  // addrx
        0x29 => Val::AddrX(r.uint(1)?), // addrx1..4
        0x2a => Val::AddrX(r.uint(2)?),
        0x2b => Val::AddrX(r.uint(3)?),
        0x2c => Val::AddrX(r.uint(4)?),
        0x11 => Val::Ref(u.off as u64 + r.uint(1)?), // ref1..8, ref_udata
        0x12 => Val::Ref(u.off as u64 + r.uint(2)?),
        0x13 => Val::Ref(u.off as u64 + r.uint(4)?),
        0x14 => Val::Ref(u.off as u64 + r.uint(8)?),
        0x15 => Val::Ref(u.off as u64 + r.uleb()?),
        0x10 => Val::Ref(off64(r)?),  // ref_addr
        0x20 => Val::U(r.uint(8)?),   // ref_sig8
        0x17 => Val::Sec(off64(r)?),  // sec_offset
        0x22 => Val::LocX(r.uleb()?), // loclistx
        0x23 => Val::U(r.uleb()?),    // rnglistx
        0x18 => {
            let n = r.uleb()? as usize;
            Val::Expr(r.take(n)?.to_vec())
        } // exprloc
        0x0a => {
            let n = r.uint(1)? as usize;
            Val::Expr(r.take(n)?.to_vec())
        } // block1
        0x03 => {
            let n = r.uint(2)? as usize;
            Val::Expr(r.take(n)?.to_vec())
        }
        0x04 => {
            let n = r.uint(4)? as usize;
            Val::Expr(r.take(n)?.to_vec())
        }
        0x09 => {
            let n = r.uleb()? as usize;
            Val::Expr(r.take(n)?.to_vec())
        }
        0x0c => Val::U(r.uint(1)?), // flag
        0x19 => Val::U(1),          // flag_present
        _ => return None,
    })
}

const AT_LOCATION: u64 = 0x02;
const AT_BYTE_SIZE: u64 = 0x0b;
const AT_LOW_PC: u64 = 0x11;
const AT_COUNT: u64 = 0x37;
const AT_UPPER_BOUND: u64 = 0x2f;
const AT_TYPE: u64 = 0x49;
const AT_FRAME_BASE: u64 = 0x40;
const AT_ADDR_BASE: u64 = 0x73;
const AT_LOCLISTS_BASE: u64 = 0x8c;

struct Die {
    tag: u64,
    attrs: Vec<(u64, Val)>,
    parent: Option<usize>,
}

impl Die {
    fn get(&self, at: u64) -> Option<&Val> {
        self.attrs.iter().find(|a| a.0 == at).map(|a| &a.1)
    }
}

/// The frame offset an expression names, if it is `fbreg k` or `breg2 k`.
fn frame_off(e: &[u8]) -> Option<i64> {
    let mut r = R::new(e, 0);
    match r.u8()? {
        0x91 | 0x72 => {
            let k = r.sleb()?;
            (r.o == e.len()).then_some(k)
        }
        _ => None,
    }
}

/// The expressions of a DWARF 4 location list at `off` in `.debug_loc`.
fn loc4(d: &[u8], off: usize, asz: usize) -> Vec<Vec<u8>> {
    let mut r = R::new(d, off);
    let mut out = Vec::new();
    while let (Some(a), Some(b)) = (r.uint(asz), r.uint(asz)) {
        if a == 0 && b == 0 {
            break;
        }
        if a == u64::MAX >> (64 - 8 * asz as u32) {
            continue; // base address selection
        }
        let Some(n) = r.uint(2) else { break };
        let Some(e) = r.take(n as usize) else { break };
        out.push(e.to_vec());
    }
    out
}

/// The expressions of a DWARF 5 location list at `off` in `.debug_loclists`.
fn loc5(d: &[u8], off: usize, asz: usize) -> Vec<Vec<u8>> {
    let mut r = R::new(d, off);
    let mut out = Vec::new();
    let expr = |r: &mut R, out: &mut Vec<Vec<u8>>| -> Option<()> {
        let n = r.uleb()? as usize;
        out.push(r.take(n)?.to_vec());
        Some(())
    };
    while let Some(k) = r.u8() {
        let ok = match k {
            0x00 => break,                // end_of_list
            0x01 => r.uleb().map(|_| ()), // base_addressx
            0x02 | 0x04 => (|| {
                r.uleb()?;
                r.uleb()?;
                expr(&mut r, &mut out)
            })(), // startx_endx, offset_pair
            0x03 => (|| {
                r.uleb()?;
                r.uleb()?;
                expr(&mut r, &mut out)
            })(), // startx_length
            0x05 => expr(&mut r, &mut out), // default_location
            0x06 => r.uint(asz).map(|_| ()), // base_address
            0x07 => (|| {
                r.uint(asz)?;
                r.uint(asz)?;
                expr(&mut r, &mut out)
            })(), // start_end
            0x08 => (|| {
                r.uint(asz)?;
                r.uleb()?;
                expr(&mut r, &mut out)
            })(), // start_length
            _ => None,
        };
        if ok.is_none() {
            break;
        }
    }
    out
}

fn units(info: &[u8]) -> Vec<Unit> {
    let mut out = Vec::new();
    let mut o = 0;
    while o + 11 <= info.len() {
        let mut r = R::new(info, o);
        let Some(len) = r.uint(4) else { break };
        if len >= 0xffff_fff0 {
            break; // 64-bit DWARF: not produced for this target
        }
        let end = o + 4 + len as usize;
        let Some(version) = r.uint(2) else { break };
        let (asz, hdr_end) = if version >= 5 {
            let _ut = r.u8();
            let a = r.u8();
            let _ab = r.uint(4);
            (a, r.o)
        } else {
            let _ab = r.uint(4);
            let a = r.u8();
            (a, r.o)
        };
        let Some(addr_size) = asz else { break };
        if end > info.len() {
            break;
        }
        out.push(Unit {
            off: o,
            end,
            version: version as u16,
            addr_size,
            hdr_end,
        });
        o = end;
    }
    out
}

fn abbrev_off(info: &[u8], u: &Unit) -> Option<usize> {
    let mut r = R::new(info, u.off + 6);
    if u.version >= 5 {
        r.take(2)?;
    }
    Some(r.uint(4)? as usize)
}

/// The size in bytes of the type at `off`.
fn type_size(dies: &BTreeMap<u64, usize>, all: &[Die], off: u64, fuel: u32) -> Option<u64> {
    if fuel == 0 {
        return None;
    }
    let d = &all[*dies.get(&off)?];
    if let Some(Val::U(n)) = d.get(AT_BYTE_SIZE) {
        if d.tag != 0x01 {
            return Some(*n);
        }
    }
    let inner = |at: u64| match d.get(at) {
        Some(Val::Ref(t)) => Some(*t),
        _ => None,
    };
    match d.tag {
        // typedef, const, volatile, restrict, atomic
        0x16 | 0x26 | 0x35 | 0x37 | 0x47 => type_size(dies, all, inner(AT_TYPE)?, fuel - 1),
        0x0f | 0x10 | 0x42 => Some(8), // pointer, reference, rvalue reference
        0x01 => {
            // array: element size times the count of every subrange child
            let elem = type_size(dies, all, inner(AT_TYPE)?, fuel - 1)?;
            let me = *dies.get(&off)?;
            let mut n = 1u64;
            let mut any = false;
            for (i, c) in all.iter().enumerate().skip(me + 1) {
                if c.parent != Some(me) {
                    if c.parent.is_none_or(|p| p < me) {
                        break;
                    }
                    continue;
                }
                let _ = i;
                if c.tag == 0x21 {
                    let count = match (c.get(AT_COUNT), c.get(AT_UPPER_BOUND)) {
                        (Some(Val::U(k)), _) => *k,
                        (_, Some(Val::U(ub))) => ub + 1,
                        _ => return None,
                    };
                    n = n.checked_mul(count)?;
                    any = true;
                }
            }
            any.then(|| elem.checked_mul(n)).flatten()
        }
        _ => None,
    }
}

fn read_unit(cx: &Ctx, u: &Unit, abbr: &[u8], out: &mut FrameVars) -> Option<()> {
    let ab = abbrevs(abbr, abbrev_off(cx.info, u)?)?;
    let mut r = R::new(cx.info, u.hdr_end);
    let mut all: Vec<Die> = Vec::new();
    let mut by_off: BTreeMap<u64, usize> = BTreeMap::new();
    let mut stack: Vec<usize> = Vec::new();
    while r.o < u.end {
        let off = r.o as u64;
        let code = r.uleb()?;
        if code == 0 {
            stack.pop();
            continue;
        }
        let a = ab.get(&code)?;
        let mut attrs = Vec::new();
        for s in &a.attrs {
            attrs.push((s.at, value(&mut r, s.form, u, s.implicit)?));
        }
        let idx = all.len();
        all.push(Die {
            tag: a.tag,
            attrs,
            parent: stack.last().copied(),
        });
        by_off.insert(off, idx);
        if a.children {
            stack.push(idx);
        }
    }
    let cu = all.first()?;
    let addr_base = match cu.get(AT_ADDR_BASE) {
        Some(Val::Sec(b)) | Some(Val::U(b)) => *b as usize,
        _ => 8,
    };
    let loclists_base = match cu.get(AT_LOCLISTS_BASE) {
        Some(Val::Sec(b)) | Some(Val::U(b)) => *b as usize,
        _ => 12,
    };
    let asz = u.addr_size as usize;
    let addr = |v: &Val| -> Option<u64> {
        match v {
            Val::U(a) => Some(*a),
            Val::AddrX(i) => R::new(cx.addr, addr_base + *i as usize * asz).uint(asz),
            _ => None,
        }
    };
    // The function a DIE belongs to: its nearest subprogram ancestor.
    let func_of = |mut i: usize| -> Option<usize> {
        loop {
            i = all[i].parent?;
            if all[i].tag == 0x2e {
                return Some(i);
            }
        }
    };
    for (i, d) in all.iter().enumerate() {
        if d.tag != 0x34 && d.tag != 0x05 {
            continue; // variable, formal_parameter
        }
        let Some(fi) = func_of(i) else { continue };
        let f = &all[fi];
        if !matches!(f.get(AT_FRAME_BASE), Some(Val::Expr(e)) if e.as_slice() == [0x52]) {
            continue; // frame base not sp
        }
        let Some(entry) = f.get(AT_LOW_PC).and_then(addr) else {
            continue;
        };
        let exprs: Vec<Vec<u8>> = match d.get(AT_LOCATION) {
            Some(Val::Expr(e)) => vec![e.clone()],
            Some(Val::Sec(o)) if u.version < 5 => loc4(cx.loc, *o as usize, asz),
            Some(Val::Sec(o)) => loc5(cx.loclists, *o as usize, asz),
            Some(Val::LocX(i)) => {
                let Some(o) = R::new(cx.loclists, loclists_base + 4 * *i as usize).uint(4) else {
                    continue;
                };
                loc5(cx.loclists, loclists_base + o as usize, asz)
            }
            _ => continue,
        };
        let Some(Val::Ref(t)) = d.get(AT_TYPE) else {
            continue;
        };
        let Some(size) = type_size(&by_off, &all, *t, 32) else {
            continue;
        };
        for e in exprs {
            if let Some(k) = frame_off(&e) {
                if k >= 0 && size > 0 {
                    out.entry(entry).or_default().insert(k as u64, size);
                }
            }
        }
    }
    Some(())
}

/// Every function's frame variables, or an empty map without `.debug_info`.
pub fn frame_vars(e: &Elf) -> FrameVars {
    let sec = |n: &str| e.section(n).map(|s| e.bytes(s)).unwrap_or(&[]);
    let cx = Ctx {
        info: sec(".debug_info"),
        addr: sec(".debug_addr"),
        loc: sec(".debug_loc"),
        loclists: sec(".debug_loclists"),
    };
    let abbr = sec(".debug_abbrev");
    let mut out = FrameVars::new();
    for u in units(cx.info) {
        let _ = read_unit(&cx, &u, abbr, &mut out);
    }
    out
}
