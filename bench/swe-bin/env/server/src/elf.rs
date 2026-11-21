//! A small ELF64 little-endian reader and the two rewrites the environment makes on RISC-V
//! binaries:
//!
//! * `link`: put the code and data of a relocatable object (what `nocompiler asm` writes) into
//!   a linked static binary, resolve its relocations against the object's own symbols and the
//!   binary's, and send every existing function the object defines to its new code. This is how
//!   an agent's structured text gets into the binary. It is a linker, not a compiler: it only
//!   places bytes the agent assembled and fills in addresses.
//! * `stub`: replace functions by a stub that exits with status 127 and erase the rest of their
//!   bytes (scratch mode's starting binary).
//!
//! `link` adds one PT_LOAD segment (RWX) after the last one, by turning the PT_GNU_STACK program
//! header into it (a static binary has no free program header slot; on RISC-V Linux the stack
//! is not executable without PT_GNU_STACK either). Linking again grows that segment. The alloc
//! contents of the binary keep their file offsets; the non-alloc sections (symbols, debug info,
//! the relocations from --emit-relocs) are rewritten after the new segment.

use std::collections::HashMap;
use std::fmt;

pub const EM_RISCV: u16 = 243;
const PT_LOAD: u32 = 1;
const PT_GNU_STACK: u32 = 0x6474_e551;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHF_WRITE: u64 = 1;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;
const STT_FUNC: u8 = 2;
const STB_GLOBAL: u8 = 1;
const SWB_SECTION: &str = ".swb";
const PAGE: u64 = 0x1000;

#[derive(Debug)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

fn err<T>(s: impl Into<String>) -> Result<T, Error> {
    Err(Error(s.into()))
}

fn rd(b: &[u8], off: usize, n: usize) -> Result<u64, Error> {
    let Some(s) = b.get(off..off + n) else {
        return err(format!("truncated ELF at offset {off}"));
    };
    let mut v = 0u64;
    for (i, x) in s.iter().enumerate() {
        v |= (*x as u64) << (8 * i);
    }
    Ok(v)
}

fn wr(b: &mut [u8], off: usize, n: usize, v: u64) -> Result<(), Error> {
    let Some(s) = b.get_mut(off..off + n) else {
        return err(format!("write outside the image at {off}"));
    };
    for (i, x) in s.iter_mut().enumerate() {
        *x = (v >> (8 * i)) as u8;
    }
    Ok(())
}

#[derive(Clone, Debug)]
pub struct Phdr {
    pub p_type: u32,
    pub flags: u32,
    pub offset: u64,
    pub vaddr: u64,
    pub filesz: u64,
    pub memsz: u64,
    pub align: u64,
}

#[derive(Clone, Debug)]
pub struct Shdr {
    pub name: String,
    pub name_off: u32,
    pub sh_type: u32,
    pub flags: u64,
    pub addr: u64,
    pub offset: u64,
    pub size: u64,
    pub link: u32,
    pub info: u32,
    pub align: u64,
    pub entsize: u64,
}

#[derive(Clone, Debug)]
pub struct Sym {
    pub name: String,
    pub value: u64,
    pub size: u64,
    pub info: u8,
    pub other: u8,
    pub shndx: u16,
}

impl Sym {
    pub fn is_func(&self) -> bool {
        self.info & 0xf == STT_FUNC
    }
    pub fn is_global(&self) -> bool {
        self.info >> 4 != 0
    }
}

pub struct Elf {
    pub data: Vec<u8>,
    pub e_type: u16,
    pub machine: u16,
    pub flags: u32,
    pub phdrs: Vec<Phdr>,
    pub shdrs: Vec<Shdr>,
    pub phoff: u64,
    pub symtab: Option<usize>,
}

fn cstr(b: &[u8], off: usize) -> String {
    let end = b[off.min(b.len())..].iter().position(|&c| c == 0).map_or(b.len(), |p| off + p);
    String::from_utf8_lossy(&b[off.min(b.len())..end]).into_owned()
}

impl Elf {
    pub fn parse(data: Vec<u8>) -> Result<Elf, Error> {
        if data.len() < 64 || &data[0..4] != b"\x7fELF" {
            return err("not an ELF file");
        }
        if data[4] != 2 || data[5] != 1 {
            return err("not a 64-bit little-endian ELF");
        }
        let e_type = rd(&data, 16, 2)? as u16;
        let machine = rd(&data, 18, 2)? as u16;
        let phoff = rd(&data, 32, 8)?;
        let shoff = rd(&data, 40, 8)? as usize;
        let flags = rd(&data, 48, 4)? as u32;
        let phnum = rd(&data, 56, 2)? as usize;
        let shnum = rd(&data, 60, 2)? as usize;
        let shstrndx = rd(&data, 62, 2)? as usize;
        let mut phdrs = Vec::new();
        for i in 0..phnum {
            let o = phoff as usize + i * 56;
            phdrs.push(Phdr {
                p_type: rd(&data, o, 4)? as u32,
                flags: rd(&data, o + 4, 4)? as u32,
                offset: rd(&data, o + 8, 8)?,
                vaddr: rd(&data, o + 16, 8)?,
                filesz: rd(&data, o + 32, 8)?,
                memsz: rd(&data, o + 40, 8)?,
                align: rd(&data, o + 48, 8)?,
            });
        }
        let mut shdrs = Vec::new();
        for i in 0..shnum {
            let o = shoff + i * 64;
            shdrs.push(Shdr {
                name: String::new(),
                name_off: rd(&data, o, 4)? as u32,
                sh_type: rd(&data, o + 4, 4)? as u32,
                flags: rd(&data, o + 8, 8)?,
                addr: rd(&data, o + 16, 8)?,
                offset: rd(&data, o + 24, 8)?,
                size: rd(&data, o + 32, 8)?,
                link: rd(&data, o + 40, 4)? as u32,
                info: rd(&data, o + 44, 4)? as u32,
                align: rd(&data, o + 48, 8)?,
                entsize: rd(&data, o + 56, 8)?,
            });
        }
        if let Some(st) = shdrs.get(shstrndx).cloned() {
            for s in shdrs.iter_mut() {
                s.name = cstr(&data, st.offset as usize + s.name_off as usize);
            }
        }
        let symtab = shdrs.iter().position(|s| s.sh_type == SHT_SYMTAB);
        Ok(Elf { data, e_type, machine, flags, phdrs, shdrs, phoff, symtab })
    }

    pub fn section(&self, i: usize) -> Result<&[u8], Error> {
        let s = &self.shdrs[i];
        if s.sh_type == SHT_NOBITS {
            return Ok(&[]);
        }
        match self.data.get(s.offset as usize..(s.offset + s.size) as usize) {
            Some(b) => Ok(b),
            None => err(format!("section {} outside the file", s.name)),
        }
    }

    pub fn symbols(&self) -> Result<Vec<Sym>, Error> {
        let Some(i) = self.symtab else { return Ok(Vec::new()) };
        let st = &self.shdrs[i];
        let strs = self.section(st.link as usize)?.to_vec();
        let b = self.section(i)?;
        let mut out = Vec::new();
        for k in 0..(b.len() / 24) {
            let o = k * 24;
            out.push(Sym {
                name: cstr(&strs, rd(b, o, 4)? as usize),
                info: b[o + 4],
                other: b[o + 5],
                shndx: rd(b, o + 6, 2)? as u16,
                value: rd(b, o + 8, 8)?,
                size: rd(b, o + 16, 8)?,
            });
        }
        Ok(out)
    }

    /// (offset, type, symbol index, addend) of a RELA section.
    pub fn relas(&self, i: usize) -> Result<Vec<(u64, u32, usize, i64)>, Error> {
        let b = self.section(i)?;
        let mut out = Vec::new();
        for k in 0..(b.len() / 24) {
            let o = k * 24;
            let info = rd(b, o + 8, 8)?;
            out.push((rd(b, o, 8)?, (info & 0xffff_ffff) as u32, (info >> 32) as usize, rd(b, o + 16, 8)? as i64));
        }
        Ok(out)
    }

    /// The file offset of virtual address `va` (in a PT_LOAD's file image), if any.
    pub fn file_offset(&self, va: u64, len: u64) -> Option<usize> {
        for p in &self.phdrs {
            if p.p_type == PT_LOAD && p.vaddr <= va && va + len <= p.vaddr + p.filesz {
                return Some((p.offset + va - p.vaddr) as usize);
            }
        }
        None
    }
}

/// Is this a static RISC-V 64 executable the environment accepts as a submission?
pub fn check_submission(data: &[u8]) -> Result<(), Error> {
    let e = Elf::parse(data.to_vec())?;
    if e.machine != EM_RISCV {
        return err(format!("e_machine is {}, not RISC-V ({EM_RISCV})", e.machine));
    }
    if e.e_type != 2 {
        return err(format!("e_type is {}, not an executable (2)", e.e_type));
    }
    if e.phdrs.iter().any(|p| p.p_type == 3) {
        return err("the binary asks for a program interpreter (PT_INTERP): it must be static");
    }
    if !e.phdrs.iter().any(|p| p.p_type == PT_LOAD) {
        return err("no PT_LOAD segment");
    }
    Ok(())
}

// ---- instruction field encoding -------------------------------------------------------------

fn hi20(v: i64) -> u32 {
    (((v + 0x800) >> 12) as u32 & 0xfffff) << 12
}
fn lo12(v: i64) -> i64 {
    v - (((v + 0x800) >> 12) << 12)
}
fn set_i(w: u32, imm: i64) -> u32 {
    (w & 0x000f_ffff) | (((imm as u32) & 0xfff) << 20)
}
fn set_s(w: u32, imm: i64) -> u32 {
    let i = imm as u32;
    (w & 0x01ff_f07f) | ((i & 0xfe0) << 20) | ((i & 0x1f) << 7)
}
fn set_b(w: u32, imm: i64) -> u32 {
    let i = imm as u32;
    (w & 0x01ff_f07f)
        | (((i >> 12) & 1) << 31)
        | (((i >> 5) & 0x3f) << 25)
        | (((i >> 1) & 0xf) << 8)
        | (((i >> 11) & 1) << 7)
}
fn set_j(w: u32, imm: i64) -> u32 {
    let i = imm as u32;
    (w & 0xfff)
        | (((i >> 20) & 1) << 31)
        | (((i >> 1) & 0x3ff) << 21)
        | (((i >> 11) & 1) << 20)
        | (((i >> 12) & 0xff) << 12)
}
fn fits(v: i64, bits: u32) -> bool {
    let m = 1i64 << (bits - 1);
    -m <= v && v < m
}

/// `auipc t1, hi(d); jalr zero, lo(d)(t1)`: a jump from `from` to `to` that clobbers only t1
/// (a temporary the calling convention does not preserve).
fn far_jump(from: u64, to: u64) -> [u32; 2] {
    let d = to.wrapping_sub(from) as i64;
    let auipc = 0x0000_0317 | hi20(d); // auipc x6
    let jalr = set_i(0x0003_0067, lo12(d)); // jalr x0, 0(x6)
    [auipc, jalr]
}

// ---- link ------------------------------------------------------------------------------------

pub struct LinkReport {
    pub segment: (u64, u64),
    pub replaced: Vec<String>,
    pub added: Vec<String>,
}

struct Placed {
    sec: usize,
    addr: u64,
}

fn align_up(v: u64, a: u64) -> u64 {
    if a <= 1 { v } else { v.div_ceil(a) * a }
}

/// Link object `obj` into binary `bin` (see the module comment). Returns the new binary.
pub fn link(bin: &[u8], obj: &[u8]) -> Result<(Vec<u8>, LinkReport), Error> {
    let b = Elf::parse(bin.to_vec())?;
    let o = Elf::parse(obj.to_vec())?;
    if b.machine != EM_RISCV || o.machine != EM_RISCV {
        return err("both files must be RISC-V");
    }
    if o.e_type != 1 {
        return err("the second file must be a relocatable object (what `nocompiler asm` writes)");
    }
    let bsyms = b.symbols()?;
    let osyms = o.symbols()?;

    // the segment: the existing .swb one (to grow), or a new one after every PT_LOAD
    let swb_sec = b.shdrs.iter().position(|s| s.name == SWB_SECTION);
    let (seg_va, old_seg): (u64, Vec<u8>) = match swb_sec {
        Some(i) => (b.shdrs[i].addr, b.section(i)?.to_vec()),
        None => {
            let end = b.phdrs.iter().filter(|p| p.p_type == PT_LOAD).map(|p| p.vaddr + p.memsz).max().unwrap_or(0);
            (align_up(end, PAGE) + PAGE, Vec::new())
        }
    };
    let ph_idx = match swb_sec {
        Some(_) => b.phdrs.iter().position(|p| p.p_type == PT_LOAD && p.vaddr == seg_va),
        None => b.phdrs.iter().position(|p| p.p_type == PT_GNU_STACK),
    };
    let Some(ph_idx) = ph_idx else {
        return err("no PT_GNU_STACK program header to turn into the new segment");
    };

    // place every alloc section of the object
    let mut seg = old_seg.clone();
    let mut placed: Vec<Placed> = Vec::new();
    for (i, s) in o.shdrs.iter().enumerate() {
        if s.flags & SHF_ALLOC == 0 || s.size == 0 {
            continue;
        }
        let off = align_up(seg.len() as u64, s.align.max(4));
        seg.resize(off as usize, 0);
        if s.sh_type == SHT_NOBITS {
            seg.resize((off + s.size) as usize, 0);
        } else {
            seg.extend_from_slice(o.section(i)?);
        }
        placed.push(Placed { sec: i, addr: seg_va + off });
    }
    let sec_addr = |i: usize| placed.iter().find(|p| p.sec == i).map(|p| p.addr);

    // symbol values in the object
    let mut by_name_b: HashMap<&str, Vec<&Sym>> = HashMap::new();
    for s in &bsyms {
        if !s.name.is_empty() && s.shndx != 0 {
            by_name_b.entry(s.name.as_str()).or_default().push(s);
        }
    }
    let resolve = |k: usize| -> Result<u64, Error> {
        let s = &osyms[k];
        if s.shndx != 0 && s.shndx < 0xff00 {
            let Some(a) = sec_addr(s.shndx as usize) else {
                return err(format!("symbol {} is in a section that is not loaded", s.name));
            };
            return Ok(a + s.value);
        }
        if s.shndx == 0xfff1 {
            return Ok(s.value);
        }
        match by_name_b.get(s.name.as_str()).map(|v| v.as_slice()) {
            Some([one]) => Ok(one.value),
            Some(many) => match many.iter().filter(|x| x.is_global()).collect::<Vec<_>>().as_slice() {
                [g] => Ok(g.value),
                _ => err(format!("symbol {} is defined {} times in the binary", s.name, many.len())),
            },
            None => err(format!("undefined symbol {}", s.name)),
        }
    };

    // relocations
    for (ri, rs) in o.shdrs.iter().enumerate() {
        if rs.sh_type != SHT_RELA {
            continue;
        }
        let tgt = rs.info as usize;
        let Some(base) = sec_addr(tgt) else { continue };
        let seg_off = (base - seg_va) as usize;
        let relas = o.relas(ri)?;
        // PCREL_HI20 values by the address of their auipc, for the PCREL_LO12 that point at it
        let mut hi: HashMap<u64, i64> = HashMap::new();
        for &(off, ty, sym, add) in &relas {
            if ty == 23 {
                let p = base + off;
                hi.insert(p, (resolve(sym)? as i64 + add) - p as i64);
            }
        }
        for &(off, ty, sym, add) in &relas {
            let p = base + off;
            let at = seg_off + off as usize;
            let w = rd(&seg, at, 4).unwrap_or(0) as u32;
            let s = || -> Result<i64, Error> { Ok(resolve(sym)? as i64 + add) };
            let pc = |v: i64| v - p as i64;
            match ty {
                43 | 51 => {} // ALIGN, RELAX
                1 => wr(&mut seg, at, 4, s()? as u64)?,
                2 => wr(&mut seg, at, 8, s()? as u64)?,
                16 => {
                    let d = pc(s()?);
                    if !fits(d, 13) {
                        return err(format!("branch at +{off} out of range"));
                    }
                    wr(&mut seg, at, 4, set_b(w, d) as u64)?
                }
                17 => {
                    let d = pc(s()?);
                    if !fits(d, 21) {
                        return err(format!("jal at +{off} out of range"));
                    }
                    wr(&mut seg, at, 4, set_j(w, d) as u64)?
                }
                18 | 19 => {
                    let d = pc(s()?);
                    let w2 = rd(&seg, at + 4, 4)? as u32;
                    wr(&mut seg, at, 4, ((w & 0xfff) | hi20(d)) as u64)?;
                    wr(&mut seg, at + 4, 4, set_i(w2, lo12(d)) as u64)?
                }
                23 => wr(&mut seg, at, 4, ((w & 0xfff) | hi20(pc(s()?))) as u64)?,
                24 | 25 => {
                    // the symbol is the auipc's label
                    let auipc = resolve(sym)?;
                    let Some(v) = hi.get(&auipc) else {
                        return err(format!("PCREL_LO12 at +{off} without its PCREL_HI20"));
                    };
                    let l = lo12(*v);
                    let nw = if ty == 24 { set_i(w, l) } else { set_s(w, l) };
                    wr(&mut seg, at, 4, nw as u64)?
                }
                26 => wr(&mut seg, at, 4, ((w & 0xfff) | hi20(s()?)) as u64)?,
                27 => wr(&mut seg, at, 4, set_i(w, lo12(s()?)) as u64)?,
                28 => wr(&mut seg, at, 4, set_s(w, lo12(s()?)) as u64)?,
                _ => return err(format!("relocation type {ty} at +{off} is not supported")),
            }
        }
    }

    // the functions the object defines: replace the binary's, or add new ones
    let mut out = b.data.clone();
    let mut new_syms = bsyms.clone();
    let mut replaced = Vec::new();
    let mut added = Vec::new();
    let new_shndx = match swb_sec {
        Some(i) => i as u16,
        None => b.shdrs.len() as u16, // appended below
    };
    for s in &osyms {
        if !s.is_func() || !s.is_global() || s.shndx == 0 || s.shndx >= 0xff00 {
            continue;
        }
        let Some(a) = sec_addr(s.shndx as usize) else { continue };
        let addr = a + s.value;
        let size = if s.size > 0 {
            s.size
        } else {
            // nocompiler asm gives functions no size: up to the next symbol of the section
            let next = osyms
                .iter()
                .filter(|t| t.shndx == s.shndx && t.value > s.value && !t.name.is_empty())
                .map(|t| t.value)
                .min()
                .unwrap_or(o.shdrs[s.shndx as usize].size);
            next - s.value
        };
        let olds: Vec<usize> =
            (0..new_syms.len()).filter(|&k| new_syms[k].is_func() && new_syms[k].name == s.name).collect();
        match olds.as_slice() {
            [k] => {
                let f = new_syms[*k].clone();
                if f.size < 8 {
                    return err(format!("{} is {} bytes: too small for the 8-byte jump", f.name, f.size));
                }
                let j = far_jump(f.value, addr);
                if seg_va <= f.value && f.value + 8 <= seg_va + old_seg.len() as u64 {
                    // a function an earlier link put in the segment: the jump goes in the segment
                    let so = (f.value - seg_va) as usize;
                    wr(&mut seg, so, 4, j[0] as u64)?;
                    wr(&mut seg, so + 4, 4, j[1] as u64)?;
                } else {
                    let Some(fo) = b.file_offset(f.value, 8) else {
                        return err(format!("{} is not in a loaded segment", f.name));
                    };
                    wr(&mut out, fo, 4, j[0] as u64)?;
                    wr(&mut out, fo + 4, 4, j[1] as u64)?;
                }
                new_syms[*k].value = addr;
                new_syms[*k].size = size;
                new_syms[*k].shndx = new_shndx;
                replaced.push(s.name.clone());
            }
            [] => {
                new_syms.push(Sym {
                    name: s.name.clone(),
                    value: addr,
                    size,
                    info: (STB_GLOBAL << 4) | STT_FUNC,
                    other: 0,
                    shndx: new_shndx,
                });
                added.push(s.name.clone());
            }
            _ => return err(format!("{} names {} functions in the binary", s.name, olds.len())),
        }
    }

    let image = rebuild(&b, &mut out, seg_va, &seg, ph_idx, swb_sec, &new_syms)?;
    Ok((image, LinkReport { segment: (seg_va, seg.len() as u64), replaced, added }))
}

/// Write the binary: alloc contents unchanged at their offsets (`out`), then the segment, then
/// every non-alloc section, then the section headers.
fn rebuild(
    b: &Elf,
    out: &mut Vec<u8>,
    seg_va: u64,
    seg: &[u8],
    ph_idx: usize,
    swb_sec: Option<usize>,
    syms: &[Sym],
) -> Result<Vec<u8>, Error> {
    // the end of everything loaded
    let mut end = b.phdrs.iter().filter(|p| p.p_type == PT_LOAD).map(|p| p.offset + p.filesz).max().unwrap_or(0);
    end = end.max(b.phoff + 56 * b.phdrs.len() as u64);
    if let Some(i) = swb_sec {
        // the old segment is replaced: anything loaded before it stays
        end = b.phdrs.iter()
            .filter(|p| p.p_type == PT_LOAD && p.vaddr != b.shdrs[i].addr)
            .map(|p| p.offset + p.filesz).max().unwrap_or(0);
    }
    let mut img: Vec<u8> = out[..end as usize].to_vec();
    // segment: file offset congruent to its address modulo the page size
    let mut seg_off = align_up(img.len() as u64, PAGE);
    seg_off += (seg_va % PAGE + PAGE - seg_off % PAGE) % PAGE;
    img.resize(seg_off as usize, 0);
    img.extend_from_slice(seg);

    // symbol and string tables, rebuilt
    let mut strtab = vec![0u8];
    let mut symtab = Vec::new();
    for s in syms {
        let name = if s.name.is_empty() {
            0
        } else {
            let n = strtab.len();
            strtab.extend_from_slice(s.name.as_bytes());
            strtab.push(0);
            n
        };
        let mut e = [0u8; 24];
        wr(&mut e, 0, 4, name as u64)?;
        e[4] = s.info;
        e[5] = s.other;
        wr(&mut e, 6, 2, s.shndx as u64)?;
        wr(&mut e, 8, 8, s.value)?;
        wr(&mut e, 16, 8, s.size)?;
        symtab.extend_from_slice(&e);
    }

    let mut shdrs = b.shdrs.clone();
    let sym_i = b.symtab;
    let str_i = sym_i.map(|i| b.shdrs[i].link as usize);
    match swb_sec {
        Some(i) => {
            shdrs[i].offset = seg_off;
            shdrs[i].size = seg.len() as u64;
        }
        None => shdrs.push(Shdr {
            name: SWB_SECTION.into(),
            name_off: 0,
            sh_type: 1,
            flags: SHF_ALLOC | SHF_WRITE | SHF_EXECINSTR,
            addr: seg_va,
            offset: seg_off,
            size: seg.len() as u64,
            link: 0,
            info: 0,
            align: 16,
            entsize: 0,
        }),
    }
    // the section-name table, rebuilt with every name
    let mut shstr = vec![0u8];
    for s in shdrs.iter_mut() {
        if s.name.is_empty() {
            s.name_off = 0;
            continue;
        }
        s.name_off = shstr.len() as u32;
        shstr.extend_from_slice(s.name.as_bytes());
        shstr.push(0);
    }
    let shstrndx = rd(&b.data, 62, 2)? as usize;
    for (i, s) in shdrs.iter_mut().enumerate() {
        if s.flags & SHF_ALLOC != 0 || s.sh_type == 0 {
            continue;
        }
        let content: Vec<u8> = if Some(i) == sym_i {
            symtab.clone()
        } else if Some(i) == str_i && Some(i) != Some(shstrndx) {
            strtab.clone()
        } else if i == shstrndx {
            shstr.clone()
        } else if i < b.shdrs.len() {
            b.section(i)?.to_vec()
        } else {
            Vec::new()
        };
        let off = align_up(img.len() as u64, s.align.max(1));
        img.resize(off as usize, 0);
        img.extend_from_slice(&content);
        s.offset = off;
        s.size = content.len() as u64;
        if Some(i) == sym_i {
            // sh_info: one past the last local symbol
            let last_local = syms.iter().rposition(|x| !x.is_global()).map_or(0, |p| p + 1);
            s.info = last_local as u32;
        }
    }
    if str_i == Some(shstrndx) {
        return err("the binary shares its symbol and section name tables: not supported");
    }
    // program headers that point at a non-alloc section (PT_RISCV_ATTRIBUTES) follow it
    for (k, ph) in b.phdrs.iter().enumerate() {
        if ph.p_type == PT_LOAD || k == ph_idx {
            continue;
        }
        if let Some(i) = b.shdrs.iter().position(|x| x.flags & SHF_ALLOC == 0 && x.sh_type != 0 && x.offset == ph.offset && ph.filesz > 0) {
            wr(&mut img, b.phoff as usize + k * 56 + 8, 8, shdrs[i].offset)?;
        }
    }
    let shoff = align_up(img.len() as u64, 8);
    img.resize(shoff as usize, 0);
    for s in &shdrs {
        let mut e = [0u8; 64];
        wr(&mut e, 0, 4, s.name_off as u64)?;
        wr(&mut e, 4, 4, s.sh_type as u64)?;
        wr(&mut e, 8, 8, s.flags)?;
        wr(&mut e, 16, 8, s.addr)?;
        wr(&mut e, 24, 8, s.offset)?;
        wr(&mut e, 32, 8, s.size)?;
        wr(&mut e, 40, 4, s.link as u64)?;
        wr(&mut e, 44, 4, s.info as u64)?;
        wr(&mut e, 48, 8, s.align)?;
        wr(&mut e, 56, 8, s.entsize)?;
        img.extend_from_slice(&e);
    }
    wr(&mut img, 40, 8, shoff)?;
    wr(&mut img, 60, 2, shdrs.len() as u64)?;
    // the program header: the new (or grown) PT_LOAD, RWX
    let o = b.phoff as usize + ph_idx * 56;
    wr(&mut img, o, 4, PT_LOAD as u64)?;
    wr(&mut img, o + 4, 4, 7)?;
    wr(&mut img, o + 8, 8, seg_off)?;
    wr(&mut img, o + 16, 8, seg_va)?;
    wr(&mut img, o + 24, 8, seg_va)?;
    wr(&mut img, o + 32, 8, seg.len() as u64)?;
    wr(&mut img, o + 40, 8, seg.len() as u64)?;
    wr(&mut img, o + 48, 8, PAGE)?;
    // PT_LOADs must be in address order: the new one is last in memory; move it after the
    // others in the table if the GNU_STACK entry came before one of them
    sort_loads(&mut img, b.phoff as usize, b.phdrs.len())?;
    Ok(img)
}

fn sort_loads(img: &mut [u8], phoff: usize, n: usize) -> Result<(), Error> {
    let mut ents: Vec<[u8; 56]> = Vec::new();
    for i in 0..n {
        let mut e = [0u8; 56];
        e.copy_from_slice(&img[phoff + i * 56..phoff + i * 56 + 56]);
        ents.push(e);
    }
    let is_load = |e: &[u8; 56]| rd(e, 0, 4).map(|t| t as u32 == PT_LOAD).unwrap_or(false);
    let mut loads: Vec<[u8; 56]> = ents.iter().filter(|e| is_load(e)).cloned().collect();
    loads.sort_by_key(|e| rd(e, 16, 8).unwrap_or(0));
    let mut li = 0;
    for e in ents.iter_mut() {
        if is_load(e) {
            *e = loads[li];
            li += 1;
        }
    }
    for (i, e) in ents.iter().enumerate() {
        img[phoff + i * 56..phoff + i * 56 + 56].copy_from_slice(e);
    }
    Ok(())
}

// ---- isolate ---------------------------------------------------------------------------------

/// A copy of `bin` in which every function but `keep` is `ret` (each word). nocompiler recovers
/// the relocatable module of the whole binary before it prints structured text, and gives up on
/// the first function outside the profile; in this copy every other function is trivially in
/// it, so `nocompiler disasm COPY keep` prints `keep`. Only for printing: never run or submitted.
pub fn isolate(bin: &[u8], keep: &str) -> Result<Vec<u8>, Error> {
    let b = Elf::parse(bin.to_vec())?;
    let syms = b.symbols()?;
    if !syms.iter().any(|s| s.is_func() && s.name == keep) {
        return err(format!("no function {keep}"));
    }
    let mut out = b.data.clone();
    for s in &syms {
        if !s.is_func() || s.name == keep || s.size < 4 {
            continue;
        }
        let Some(fo) = b.file_offset(s.value, s.size) else { continue };
        for k in 0..(s.size / 4) as usize {
            wr(&mut out, fo + 4 * k, 4, 0x0000_8067)?;
        }
    }
    Ok(out)
}

// ---- stub ------------------------------------------------------------------------------------

/// `addi a0, zero, 127; addi a7, zero, 94; ecall` (exit_group(127)), then `ebreak` to the end.
pub fn stub(bin: &[u8], names: &[String]) -> Result<(Vec<u8>, Vec<(String, u64)>), Error> {
    let b = Elf::parse(bin.to_vec())?;
    let syms = b.symbols()?;
    let mut out = b.data.clone();
    let mut done = Vec::new();
    for n in names {
        let fs: Vec<&Sym> = syms.iter().filter(|s| s.is_func() && &s.name == n && s.size > 0).collect();
        let [f] = fs.as_slice() else {
            return err(format!("{n}: {} functions with that name", fs.len()));
        };
        if f.size < 12 {
            return err(format!("{n} is {} bytes: too small for the stub", f.size));
        }
        let Some(fo) = b.file_offset(f.value, f.size) else {
            return err(format!("{n} is not in a loaded segment"));
        };
        let code = [0x07f0_0513u32, 0x05e0_0893, 0x0000_0073];
        for k in 0..(f.size / 4) as usize {
            let w = if k < 3 { code[k] } else { 0x0010_0073 };
            wr(&mut out, fo + 4 * k, 4, w as u64)?;
        }
        done.push((n.clone(), f.size / 4));
    }
    Ok((out, done))
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn encodings_round_trip() {
        // jal x0, +2048 and beq x0, x0, -4096
        assert_eq!(set_j(0x6f, 2048), 0x0010_006f);
        assert_eq!(set_b(0x63, -4096), 0x8000_0063);
        let [a, j] = far_jump(0x1000, 0x1234_5678);
        let d = 0x1234_5678i64 - 0x1000;
        let hi = (a >> 12) as i64;
        let lo = ((j as i32) >> 20) as i64;
        assert_eq!((hi << 12) + lo, d);
    }
}
