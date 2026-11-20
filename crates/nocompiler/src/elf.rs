//! A minimal ELF64 little-endian reader: section headers, section names and
//! the symbol table. That is all the profile tooling needs, and reading only
//! that keeps the reader short enough to review against the gABI.
//!
//! Every offset and size is bounds-checked; a malformed file is an error, not
//! a panic.

use std::fmt;

#[derive(Debug)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

fn err<T>(m: impl Into<String>) -> Result<T, Error> {
    Err(Error(m.into()))
}

pub const EM_RISCV: u16 = 243;
pub const SHT_PROGBITS: u32 = 1;
pub const SHT_SYMTAB: u32 = 2;
pub const SHT_NOBITS: u32 = 8;
pub const SHF_WRITE: u64 = 1;
pub const SHF_ALLOC: u64 = 2;
pub const SHF_EXECINSTR: u64 = 4;
pub const STT_FUNC: u8 = 2;

#[derive(Debug, Clone)]
pub struct Section {
    pub name: String,
    pub kind: u32,
    pub flags: u64,
    pub addr: u64,
    pub offset: u64,
    pub size: u64,
    pub link: u32,
    pub entsize: u64,
    /// sh_addralign.
    pub align: u64,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub value: u64,
    pub size: u64,
    pub kind: u8,
    pub shndx: u16,
}

#[derive(Debug)]
pub struct Elf<'a> {
    pub data: &'a [u8],
    pub machine: u16,
    pub entry: u64,
    /// ELF header `e_flags`; for RISC-V, bit 0 is RVC (compressed code).
    pub flags: u32,
    pub sections: Vec<Section>,
    pub symbols: Vec<Symbol>,
}

fn u16_at(d: &[u8], o: usize) -> Result<u16, Error> {
    d.get(o..o + 2)
        .map(|b| u16::from_le_bytes([b[0], b[1]]))
        .ok_or_else(|| Error(format!("truncated at {o:#x}")))
}

fn u32_at(d: &[u8], o: usize) -> Result<u32, Error> {
    d.get(o..o + 4)
        .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
        .ok_or_else(|| Error(format!("truncated at {o:#x}")))
}

fn u64_at(d: &[u8], o: usize) -> Result<u64, Error> {
    d.get(o..o + 8)
        .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
        .ok_or_else(|| Error(format!("truncated at {o:#x}")))
}

fn cstr(d: &[u8], o: usize) -> Result<String, Error> {
    let tail = d
        .get(o..)
        .ok_or_else(|| Error(format!("string at {o:#x} out of range")))?;
    let end = tail
        .iter()
        .position(|&b| b == 0)
        .ok_or_else(|| Error(format!("unterminated string at {o:#x}")))?;
    String::from_utf8(tail[..end].to_vec()).map_err(|_| Error(format!("non-UTF-8 name at {o:#x}")))
}

impl<'a> Elf<'a> {
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        if data.len() < 64 || &data[..4] != b"\x7fELF" {
            return err("not an ELF file");
        }
        if data[4] != 2 {
            return err("not ELF64");
        }
        if data[5] != 1 {
            return err("not little-endian");
        }
        let machine = u16_at(data, 18)?;
        let entry = u64_at(data, 24)?;
        let shoff = u64_at(data, 40)? as usize;
        let flags = u32_at(data, 48)?;
        let shentsize = u16_at(data, 58)? as usize;
        let shnum = u16_at(data, 60)? as usize;
        let shstrndx = u16_at(data, 62)? as usize;
        if shnum > 0 && shentsize < 64 {
            return err("section header entries too small");
        }
        let mut raw = Vec::with_capacity(shnum);
        for i in 0..shnum {
            let o = shoff
                .checked_add(
                    i.checked_mul(shentsize)
                        .ok_or_else(|| Error("overflow".into()))?,
                )
                .ok_or_else(|| Error("section header offset overflows".into()))?;
            raw.push((
                u32_at(data, o)?,
                u32_at(data, o + 4)?,
                u64_at(data, o + 8)?,
                u64_at(data, o + 16)?,
                u64_at(data, o + 24)?,
                u64_at(data, o + 32)?,
                u32_at(data, o + 40)?,
                u64_at(data, o + 56)?,
                u64_at(data, o + 48)?,
            ));
        }
        let strtab = raw.get(shstrndx).map(|r| r.4 as usize);
        let mut sections = Vec::with_capacity(shnum);
        for &(name, kind, flags, addr, offset, size, link, entsize, align) in &raw {
            let name = match strtab {
                Some(base) => cstr(data, base + name as usize)?,
                None => String::new(),
            };
            if kind != SHT_NOBITS && (offset as u128 + size as u128) > data.len() as u128 {
                return err(format!("section {name} extends past the end of the file"));
            }
            sections.push(Section {
                name,
                kind,
                flags,
                addr,
                offset,
                size,
                link,
                entsize,
                align,
            });
        }
        let mut symbols = Vec::new();
        if let Some(st) = sections.iter().find(|s| s.kind == SHT_SYMTAB) {
            let names = sections
                .get(st.link as usize)
                .ok_or_else(|| Error("symbol table has no string table".into()))?
                .offset as usize;
            let ent = if st.entsize == 0 {
                24
            } else {
                st.entsize as usize
            };
            if ent < 24 {
                return err("symbol entries too small");
            }
            for i in 0..(st.size as usize / ent) {
                let o = st.offset as usize + i * ent;
                let name = cstr(data, names + u32_at(data, o)? as usize)?;
                symbols.push(Symbol {
                    name,
                    kind: data[o + 4] & 0xf,
                    shndx: u16_at(data, o + 6)?,
                    value: u64_at(data, o + 8)?,
                    size: u64_at(data, o + 16)?,
                });
            }
        }
        Ok(Elf {
            data,
            machine,
            entry,
            flags,
            sections,
            symbols,
        })
    }

    pub fn section(&self, name: &str) -> Option<&Section> {
        self.sections.iter().find(|s| s.name == name)
    }

    pub fn bytes(&self, s: &Section) -> &'a [u8] {
        if s.kind == SHT_NOBITS {
            return &[];
        }
        &self.data[s.offset as usize..(s.offset + s.size) as usize]
    }

    /// Function symbols with a nonzero size, by address, one per address.
    pub fn functions(&self) -> Vec<&Symbol> {
        let mut f: Vec<&Symbol> = self
            .symbols
            .iter()
            .filter(|s| s.kind == STT_FUNC && s.size > 0)
            .collect();
        f.sort_by_key(|s| (s.value, s.name.clone()));
        f.dedup_by_key(|s| s.value);
        f
    }
}
