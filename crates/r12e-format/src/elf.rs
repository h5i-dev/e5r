//! ELF, 32- and 64-bit, both byte orders.
//!
//! Structure layout differs between the two classes in ways that are easy to
//! get wrong: ELF32 program headers put `p_flags` last, ELF64 puts it second,
//! and the two `Elf_Sym` layouts interleave their fields differently. Each is
//! read field by field rather than cast over, so the difference is visible.
//!
//! A relocatable object has no program headers and every section sits at
//! address zero. Those get synthetic addresses, assigned in section order with
//! alignment respected, so an `.o` file is analyzable like anything else.

use std::collections::BTreeMap;

use r12e_core::{
    Addr, AddrRange, Arch, Bits, Endian, Error, Evidence, MemoryMap, Perms, Provenance, Reader,
    Result, Segment,
};

use crate::{
    Binding, Export, Format, FunctionHint, Import, LoadOptions, Object, Section, Symbol, SymbolKind,
};

const MAGIC: [u8; 4] = [0x7f, b'E', b'L', b'F'];

// e_type
const ET_REL: u16 = 1;
const ET_EXEC: u16 = 2;
const ET_DYN: u16 = 3;
const ET_CORE: u16 = 4;

// p_type
const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_INTERP: u32 = 3;
const PT_NOTE: u32 = 4;
const PT_GNU_EH_FRAME: u32 = 0x6474_e550;
const PT_GNU_STACK: u32 = 0x6474_e551;
const PT_GNU_RELRO: u32 = 0x6474_e552;

// sh_type
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHT_REL: u32 = 9;
const SHT_DYNSYM: u32 = 11;
const SHT_INIT_ARRAY: u32 = 14;
const SHT_FINI_ARRAY: u32 = 15;

// sh_flags
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;

// d_tag
const DT_NULL: u64 = 0;
const DT_NEEDED: u64 = 1;
const DT_PLTGOT: u64 = 3;
const DT_SONAME: u64 = 14;
const DT_INIT: u64 = 12;
const DT_FINI: u64 = 13;
const DT_RPATH: u64 = 15;
const DT_RUNPATH: u64 = 29;
const DT_FLAGS_1: u64 = 0x6fff_fffb;
const DF_1_PIE: u64 = 0x0800_0000;

// ST_TYPE
const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;
const STT_FILE: u8 = 4;
const STT_TLS: u8 = 6;
const STT_GNU_IFUNC: u8 = 10;

const SHN_UNDEF: u16 = 0;

/// Raw section header, before names are resolved.
struct SecHdr {
    name_off: u32,
    kind: u32,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
    /// The section these entries apply to. Read for the record rather than
    /// used: identifying the PLT relocation table through it does not work,
    /// because it names `.got.plt` rather than `.plt`.
    #[allow(dead_code)]
    info: u32,
    addralign: u64,
    entsize: u64,
}

/// Raw program header.
struct ProgHdr {
    kind: u32,
    flags: u32,
    offset: u64,
    vaddr: u64,
    filesz: u64,
    memsz: u64,
}

/// True when the buffer starts with the ELF magic.
pub fn is_elf(data: &[u8]) -> bool {
    data.len() >= 4 && data[..4] == MAGIC
}

/// Parse an ELF file.
pub fn load(data: &[u8], opts: &LoadOptions) -> Result<Object> {
    if !is_elf(data) {
        return Err(Error::NotRecognized { expected: "ELF" });
    }
    let caps = &opts.caps;
    let mut warnings = Vec::new();

    // Read through the reader rather than indexing: a five-byte file that
    // starts with the magic is a real fuzz case, and indexing panicked on it.
    let ident = Reader::le(data);
    let class = ident.bytes_at("e_ident[EI_CLASS]", 4, 1)?[0];
    let data_encoding = ident.bytes_at("e_ident[EI_DATA]", 5, 1)?[0];
    let wide = match class {
        1 => false,
        2 => true,
        other => {
            return Err(Error::BadField {
                field: "e_ident[EI_CLASS]",
                value: other as u64,
                reason: "is neither ELFCLASS32 (1) nor ELFCLASS64 (2)",
            });
        }
    };
    let endian = match data_encoding {
        1 => Endian::Little,
        2 => Endian::Big,
        other => {
            return Err(Error::BadField {
                field: "e_ident[EI_DATA]",
                value: other as u64,
                reason: "is neither ELFDATA2LSB (1) nor ELFDATA2MSB (2)",
            });
        }
    };
    let bits = if wide { Bits::Bits64 } else { Bits::Bits32 };

    let r = Reader::new(data, endian);
    let mut h = r;
    h.seek("e_type", 16)?;
    let e_type = h.u16("e_type")?;
    let e_machine = h.u16("e_machine")?;
    let _e_version = h.u32("e_version")?;
    let e_entry = h.uword("e_entry", wide)?;
    let e_phoff = h.uword("e_phoff", wide)?;
    let e_shoff = h.uword("e_shoff", wide)?;
    let _e_flags = h.u32("e_flags")?;
    let _e_ehsize = h.u16("e_ehsize")?;
    let e_phentsize = h.u16("e_phentsize")?;
    let e_phnum = h.u16("e_phnum")?;
    let e_shentsize = h.u16("e_shentsize")?;
    let e_shnum = h.u16("e_shnum")?;
    let e_shstrndx = h.u16("e_shstrndx")?;

    let arch = machine_to_arch(e_machine, bits);

    let phdrs = read_program_headers(&r, wide, e_phoff, e_phentsize, e_phnum, caps, &mut warnings)?;
    let (shdrs, shstrndx) = read_section_headers(
        &r,
        wide,
        e_shoff,
        e_shentsize,
        e_shnum,
        e_shstrndx,
        caps,
        &mut warnings,
    )?;

    // Section names come from the section named by e_shstrndx. A file may lie
    // about which section that is; a bad index costs the names, not the load.
    let shstr = shdrs
        .get(shstrndx as usize)
        .and_then(|s| r.slice_at("shstrtab", s.offset, s.size).ok());
    if shstr.is_none() && !shdrs.is_empty() {
        warnings.push(format!(
            "e_shstrndx is {shstrndx}, which does not name a readable string table; \
             section names are unavailable"
        ));
    }

    let mut sections = Vec::with_capacity(shdrs.len());
    for sh in &shdrs {
        let name = shstr
            .and_then(|t| {
                t.cstr_at("section name", sh.name_off as u64, caps.string_len)
                    .ok()
            })
            .map(|b| String::from_utf8_lossy(b).into_owned())
            .unwrap_or_default();
        let file_size = if sh.kind == SHT_NOBITS { 0 } else { sh.size };
        sections.push(Section {
            name,
            range: AddrRange::sized(Addr(sh.addr), sh.size)
                .unwrap_or(AddrRange::empty_at(Addr(sh.addr))),
            file_offset: sh.offset,
            file_size,
            exec: sh.flags & SHF_EXECINSTR != 0,
            write: sh.flags & SHF_WRITE != 0,
            kind: sh.kind,
        });
    }

    let relocatable = e_type == ET_REL;
    let memory = if relocatable {
        map_relocatable(&r, &shdrs, &mut sections, opts, &mut warnings)?
    } else {
        map_loadable(&r, &phdrs, &shdrs, &sections, opts, &mut warnings)?
    };

    let image_base = phdrs
        .iter()
        .filter(|p| p.kind == PT_LOAD)
        .map(|p| p.vaddr)
        .min()
        .map(Addr)
        .unwrap_or(Addr::ZERO);

    let mut obj = Object {
        debug: None,
        format: Format::Elf,
        arch,
        endian,
        bits,
        entry: (e_entry != 0).then_some(Addr(e_entry)),
        image_base,
        pic: e_type == ET_DYN,
        memory,
        sections,
        symbols: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        function_hints: Vec::new(),
        metadata: BTreeMap::new(),
        warnings,
    };

    obj.metadata
        .insert("elf.type".into(), type_name(e_type).into());
    obj.metadata
        .insert("elf.machine".into(), format!("{e_machine}"));
    obj.metadata.insert("elf.class".into(), bits.to_string());

    let dynsym_names = read_symbols(&r, &shdrs, &mut obj, caps)?;
    read_dynamic(&r, &phdrs, &shdrs, &mut obj, caps);
    read_notes(&r, &phdrs, &shdrs, &mut obj);
    read_init_arrays(&r, &shdrs, wide, &mut obj, caps);
    read_plt_relocations(&r, &shdrs, wide, &dynsym_names, &mut obj, caps);

    if opts.eh_frame {
        read_eh_frame(&r, &phdrs, &mut obj);
    }

    if relocatable {
        // A relocatable object writes zero where an address goes: without the
        // relocations, every call inside it points at itself and the call
        // graph is fiction.
        apply_code_relocations(&r, &shdrs, &mut obj);
    }

    if opts.debug_info {
        // A relocatable object's debug addresses are section-relative and need
        // the relocations applied; its symbol table already names every
        // function, so the types and lines are read and the hints are not.
        read_debug_info(&r, &shdrs, &mut obj, !relocatable);
    }

    if let Some(entry) = obj.entry {
        obj.function_hints.push(FunctionHint {
            addr: entry,
            size: None,
            name: Some("_start".into()),
            provenance: Provenance::new(Evidence::EntryPoint),
        });
    }

    obj.normalize_symbols();
    obj.normalize_hints();
    Ok(obj)
}

fn type_name(t: u16) -> &'static str {
    match t {
        ET_REL => "relocatable",
        ET_EXEC => "executable",
        ET_DYN => "shared object or PIE",
        ET_CORE => "core dump",
        _ => "unknown",
    }
}

/// `e_machine` to an architecture. Unrecognized machines load as a container
/// without a decoder rather than failing.
fn machine_to_arch(m: u16, bits: Bits) -> Arch {
    match m {
        3 => Arch::X86,
        62 => Arch::X86_64,
        40 => Arch::Arm,
        183 => Arch::AArch64,
        // Reachable through a SLEIGH language; the id is what the spec calls it.
        8 => Arch::Sleigh(format!("MIPS:BE:{bits}:default")),
        20 => Arch::Sleigh("PowerPC:BE:32:default".into()),
        21 => Arch::Sleigh("PowerPC:BE:64:default".into()),
        2 => Arch::Sleigh("sparc:BE:32:default".into()),
        22 => Arch::Sleigh("s390:BE:64:default".into()),
        243 => Arch::Sleigh(format!("RISCV:LE:{bits}:default")),
        258 => Arch::Sleigh(format!("Loongarch:LE:{bits}:default")),
        other => Arch::Unknown(other as u32),
    }
}

fn read_program_headers(
    r: &Reader<'_>,
    wide: bool,
    off: u64,
    entsize: u16,
    num: u16,
    caps: &r12e_core::Caps,
    warnings: &mut Vec<String>,
) -> Result<Vec<ProgHdr>> {
    if num == 0 || off == 0 {
        return Ok(Vec::new());
    }
    caps.check("program headers", num as u64, caps.sections)?;
    let want = if wide { 56 } else { 32 };
    if (entsize as u64) < want {
        warnings.push(format!(
            "e_phentsize is {entsize}, smaller than the {want} bytes this class needs; \
             program headers skipped"
        ));
        return Ok(Vec::new());
    }
    let mut out = Vec::with_capacity(num as usize);
    for i in 0..num as u64 {
        let at = off + i * entsize as u64;
        let mut p = match r.slice_at("program header", at, want) {
            Ok(p) => p,
            Err(e) => {
                warnings.push(format!("program header {i}: {e}"));
                break;
            }
        };
        // The one field whose position differs between the classes.
        let (kind, flags, offset, vaddr, filesz, memsz) = if wide {
            let kind = p.u32("p_type")?;
            let flags = p.u32("p_flags")?;
            let offset = p.u64("p_offset")?;
            let vaddr = p.u64("p_vaddr")?;
            let _paddr = p.u64("p_paddr")?;
            (
                kind,
                flags,
                offset,
                vaddr,
                p.u64("p_filesz")?,
                p.u64("p_memsz")?,
            )
        } else {
            let kind = p.u32("p_type")?;
            let offset = p.u32("p_offset")? as u64;
            let vaddr = p.u32("p_vaddr")? as u64;
            let _paddr = p.u32("p_paddr")?;
            let filesz = p.u32("p_filesz")? as u64;
            let memsz = p.u32("p_memsz")? as u64;
            (kind, p.u32("p_flags")?, offset, vaddr, filesz, memsz)
        };
        out.push(ProgHdr {
            kind,
            flags,
            offset,
            vaddr,
            filesz,
            memsz,
        });
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn read_section_headers(
    r: &Reader<'_>,
    wide: bool,
    off: u64,
    entsize: u16,
    num: u16,
    shstrndx: u16,
    caps: &r12e_core::Caps,
    warnings: &mut Vec<String>,
) -> Result<(Vec<SecHdr>, u32)> {
    if off == 0 {
        return Ok((Vec::new(), 0));
    }
    let want = if wide { 64 } else { 40 };
    if (entsize as u64) < want {
        warnings.push(format!(
            "e_shentsize is {entsize}, smaller than the {want} bytes this class needs; \
             sections skipped"
        ));
        return Ok((Vec::new(), 0));
    }

    // e_shnum of zero means the real count is in section 0's sh_size, the
    // escape hatch for files with more than 0xffff sections.
    let mut count = num as u64;
    let mut index = shstrndx as u32;
    if count == 0 {
        let mut z = r.slice_at("section header 0", off, want)?;
        z.skip("sh_name..sh_addr", if wide { 24 } else { 12 })?;
        count = z.uword("sh_size", wide)?;
        // SHN_XINDEX: section 0's sh_link holds the real shstrndx.
        if shstrndx == 0xffff {
            let mut z2 = r.slice_at("section header 0", off, want)?;
            z2.skip("to sh_link", if wide { 40 } else { 24 })?;
            index = z2.u32("sh_link")?;
        }
    }
    caps.check("sections", count, caps.sections)?;

    let mut out = Vec::with_capacity(count as usize);
    for i in 0..count {
        let at = off + i * entsize as u64;
        let mut s = match r.slice_at("section header", at, want) {
            Ok(s) => s,
            Err(e) => {
                warnings.push(format!("section header {i}: {e}"));
                break;
            }
        };
        out.push(SecHdr {
            name_off: s.u32("sh_name")?,
            kind: s.u32("sh_type")?,
            flags: s.uword("sh_flags", wide)?,
            addr: s.uword("sh_addr", wide)?,
            offset: s.uword("sh_offset", wide)?,
            size: s.uword("sh_size", wide)?,
            link: s.u32("sh_link")?,
            info: s.u32("sh_info")?,
            addralign: s.uword("sh_addralign", wide)?,
            entsize: s.uword("sh_entsize", wide)?,
        });
    }
    Ok((out, index))
}

fn perms_of(flags: u32) -> Perms {
    Perms::new(flags & 4 != 0, flags & 2 != 0, flags & 1 != 0)
}

/// Map PT_LOAD segments, naming each after the sections that fall inside it.
fn map_loadable(
    r: &Reader<'_>,
    phdrs: &[ProgHdr],
    shdrs: &[SecHdr],
    sections: &[Section],
    opts: &LoadOptions,
    warnings: &mut Vec<String>,
) -> Result<MemoryMap> {
    let mut mem = MemoryMap::new();
    let slide = opts.base.map(|b| b.get()).unwrap_or(0);

    for (i, p) in phdrs.iter().enumerate().filter(|(_, p)| p.kind == PT_LOAD) {
        if p.memsz == 0 {
            continue;
        }
        let vaddr = p.vaddr.wrapping_add(slide);
        let Some(range) = AddrRange::sized(Addr(vaddr), p.memsz) else {
            warnings.push(format!(
                "PT_LOAD {i} at {vaddr:#x} for {:#x} bytes wraps the address space; skipped",
                p.memsz
            ));
            continue;
        };
        // filesz above memsz is a lie; take the smaller and say so.
        let filesz = if p.filesz > p.memsz {
            warnings.push(format!(
                "PT_LOAD {i}: p_filesz {:#x} exceeds p_memsz {:#x}; truncated",
                p.filesz, p.memsz
            ));
            p.memsz
        } else {
            p.filesz
        };
        let data = match r.bytes_at("segment body", p.offset, filesz) {
            Ok(b) => b.to_vec(),
            Err(e) => {
                warnings.push(format!("PT_LOAD {i}: {e}; mapped as zeros"));
                Vec::new()
            }
        };
        let name = sections
            .iter()
            .filter(|s| {
                !s.range.is_empty() && range.contains_range(s.range) && s.name.starts_with('.')
            })
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>()
            .join(",");
        mem.add(Segment::new(
            range,
            perms_of(p.flags),
            name,
            p.offset,
            data,
        )?);
    }

    // A file with sections but no loadable segments still deserves a map: a
    // core dump, or a stripped-down object that kept SHF_ALLOC sections.
    if mem.is_empty() && !shdrs.is_empty() {
        warnings.push("no loadable segments; mapping allocated sections instead".into());
        for (sh, sec) in shdrs.iter().zip(sections) {
            if sh.flags & SHF_ALLOC == 0 || sh.size == 0 {
                continue;
            }
            let Some(range) = AddrRange::sized(Addr(sh.addr.wrapping_add(slide)), sh.size) else {
                continue;
            };
            let perms = Perms::new(
                true,
                sh.flags & SHF_WRITE != 0,
                sh.flags & SHF_EXECINSTR != 0,
            );
            let data = if sh.kind == SHT_NOBITS {
                Vec::new()
            } else {
                r.bytes_at("section body", sh.offset, sh.size)
                    .map(|b| b.to_vec())
                    .unwrap_or_default()
            };
            mem.add(Segment::new(
                range,
                perms,
                sec.name.clone(),
                sh.offset,
                data,
            )?);
        }
    }
    Ok(mem)
}

/// Give a relocatable object's sections synthetic addresses so it can be
/// analyzed. Section order is preserved and alignment respected, which keeps
/// the layout deterministic and close to what a link would produce.
fn map_relocatable(
    r: &Reader<'_>,
    shdrs: &[SecHdr],
    sections: &mut [Section],
    opts: &LoadOptions,
    warnings: &mut Vec<String>,
) -> Result<MemoryMap> {
    let mut mem = MemoryMap::new();
    let mut next = opts.base.unwrap_or(Addr(0x10_0000));

    for (sh, sec) in shdrs.iter().zip(sections.iter_mut()) {
        if sh.flags & SHF_ALLOC == 0 || sh.size == 0 {
            continue;
        }
        let align = sh.addralign.max(1).next_power_of_two();
        let Some(at) = next.align_up(align) else {
            warnings.push(format!(
                "section {} does not fit the address space",
                sec.name
            ));
            continue;
        };
        let Some(range) = AddrRange::sized(at, sh.size) else {
            continue;
        };
        let data = if sh.kind == SHT_NOBITS {
            Vec::new()
        } else {
            match r.bytes_at("section body", sh.offset, sh.size) {
                Ok(b) => b.to_vec(),
                Err(e) => {
                    warnings.push(format!("section {}: {e}", sec.name));
                    continue;
                }
            }
        };
        let perms = Perms::new(
            true,
            sh.flags & SHF_WRITE != 0,
            sh.flags & SHF_EXECINSTR != 0,
        );
        mem.add(Segment::new(
            range,
            perms,
            sec.name.clone(),
            sh.offset,
            data,
        )?);
        sec.range = range;
        next = range.end();
    }
    Ok(mem)
}

/// Walk `.symtab` and `.dynsym`.
fn read_symbols(
    r: &Reader<'_>,
    shdrs: &[SecHdr],
    obj: &mut Object,
    caps: &r12e_core::Caps,
) -> Result<Vec<String>> {
    // Dynamic symbol names by their index in the table, including the entries
    // that are skipped as symbols. A relocation names a symbol by that index,
    // so a vector that drops entries would name the wrong one.
    let mut dynsym_names: Vec<String> = Vec::new();
    let wide = obj.bits == Bits::Bits64;
    let entsize = if wide { 24 } else { 16 };

    // Section index to the address it was mapped at, so a relocatable object's
    // symbols land where its sections did.
    let relocatable = obj.metadata.get("elf.type").map(String::as_str) == Some("relocatable");

    for sh in shdrs
        .iter()
        .filter(|s| s.kind == SHT_SYMTAB || s.kind == SHT_DYNSYM)
    {
        let dynamic = sh.kind == SHT_DYNSYM;
        let Some(strtab) = shdrs
            .get(sh.link as usize)
            .and_then(|s| r.slice_at("symbol strtab", s.offset, s.size).ok())
        else {
            obj.warnings.push(format!(
                "symbol table sh_link is {}, which is not a readable string table",
                sh.link
            ));
            continue;
        };
        let step = if sh.entsize >= entsize {
            sh.entsize
        } else {
            entsize
        };
        let count = sh.size / step;
        caps.check("symbols", count, caps.symbols)?;

        if dynamic {
            dynsym_names.resize(count as usize, String::new());
        }
        for i in 0..count {
            let Ok(mut s) = r.slice_at("symbol", sh.offset + i * step, entsize) else {
                break;
            };
            // ELF32 and ELF64 interleave these differently.
            let (name_off, info, shndx, value, size) = if wide {
                let n = s.u32("st_name")?;
                let info = s.u8("st_info")?;
                let _other = s.u8("st_other")?;
                let shndx = s.u16("st_shndx")?;
                (n, info, shndx, s.u64("st_value")?, s.u64("st_size")?)
            } else {
                let n = s.u32("st_name")?;
                let value = s.u32("st_value")? as u64;
                let size = s.u32("st_size")? as u64;
                let info = s.u8("st_info")?;
                let _other = s.u8("st_other")?;
                (n, info, s.u16("st_shndx")?, value, size)
            };
            if name_off == 0 && value == 0 && info == 0 {
                continue;
            }
            let name = strtab
                .cstr_at("symbol name", name_off as u64, caps.string_len)
                .map(|b| String::from_utf8_lossy(b).into_owned())
                .unwrap_or_default();
            if dynamic {
                if let Some(slot) = dynsym_names.get_mut(i as usize) {
                    slot.clone_from(&name);
                }
            }
            if name.is_empty() && info >> 4 == 0 {
                continue;
            }

            let kind = match info & 0xf {
                STT_FUNC | STT_GNU_IFUNC => SymbolKind::Function,
                STT_OBJECT => SymbolKind::Object,
                STT_SECTION => SymbolKind::Section,
                STT_FILE => SymbolKind::File,
                STT_TLS => SymbolKind::Tls,
                _ if shndx == SHN_UNDEF => SymbolKind::Undefined,
                _ => SymbolKind::Other,
            };
            let binding = match info >> 4 {
                0 => Binding::Local,
                2 => Binding::Weak,
                _ => Binding::Global,
            };

            // In a relocatable object st_value is an offset into its section.
            let addr = if relocatable && shndx != SHN_UNDEF && (shndx as usize) < obj.sections.len()
            {
                Addr(
                    obj.sections[shndx as usize]
                        .range
                        .start()
                        .get()
                        .wrapping_add(value),
                )
            } else {
                Addr(value)
            };
            let undefined = shndx == SHN_UNDEF;

            if undefined && !name.is_empty() {
                obj.imports.push(Import {
                    name: name.clone(),
                    library: None,
                    thunk: None,
                });
            } else if dynamic && binding != Binding::Local && !name.is_empty() && addr != Addr::ZERO
            {
                obj.exports.push(Export {
                    name: name.clone(),
                    addr,
                    ordinal: None,
                });
            }

            if kind == SymbolKind::Function && !undefined && addr != Addr::ZERO {
                obj.function_hints.push(FunctionHint {
                    addr,
                    size: (size != 0).then_some(size),
                    name: Some(name.clone()),
                    provenance: Provenance::new(if dynamic {
                        Evidence::DynamicSymbol
                    } else {
                        Evidence::SymbolTable
                    }),
                });
            } else if kind == SymbolKind::Other
                && !undefined
                && addr != Addr::ZERO
                && is_code_name(&name)
                && in_executable_section(obj, addr)
            {
                // A symbol with no declared type sitting in an executable
                // section names code: assemblers write them for hand-written
                // entry points and linkers for wrappers. Claiming a function
                // here is an inference, not a fact, and says so.
                obj.function_hints.push(FunctionHint {
                    addr,
                    size: (size != 0).then_some(size),
                    name: Some(name.clone()),
                    provenance: Provenance::new(Evidence::CodeSymbol),
                });
            }

            obj.symbols.push(Symbol {
                name,
                addr: if undefined { Addr::ZERO } else { addr },
                size,
                kind: if undefined {
                    SymbolKind::Undefined
                } else {
                    kind
                },
                binding,
                dynamic,
            });
        }
    }
    Ok(dynsym_names)
}

/// Read `.dynamic` for needed libraries, soname, and init/fini.
fn read_dynamic(
    r: &Reader<'_>,
    phdrs: &[ProgHdr],
    shdrs: &[SecHdr],
    obj: &mut Object,
    caps: &r12e_core::Caps,
) {
    let wide = obj.bits == Bits::Bits64;
    let step = if wide { 16 } else { 8 };

    let Some((off, size)) = phdrs
        .iter()
        .find(|p| p.kind == PT_DYNAMIC)
        .map(|p| (p.offset, p.filesz))
        .or_else(|| {
            shdrs
                .iter()
                .find(|s| s.kind == 6)
                .map(|s| (s.offset, s.size))
        })
    else {
        return;
    };

    // The string table .dynamic refers to by address; find the section that
    // holds it rather than trusting DT_STRTAB's address to be mapped.
    let dynstr = shdrs
        .iter()
        .find(|s| s.kind == SHT_STRTAB && s.flags & SHF_ALLOC != 0)
        .and_then(|s| r.slice_at("dynstr", s.offset, s.size).ok());

    let mut needed = Vec::new();
    for i in 0..(size / step) {
        let Ok(mut d) = r.slice_at("dynamic entry", off + i * step, step) else {
            break;
        };
        let (Ok(tag), Ok(val)) = (d.uword("d_tag", wide), d.uword("d_val", wide)) else {
            break;
        };
        let name_of = |v: u64| {
            dynstr
                .and_then(|t| t.cstr_at("dynamic string", v, caps.string_len).ok())
                .map(|b| String::from_utf8_lossy(b).into_owned())
        };
        match tag {
            DT_NULL => break,
            DT_NEEDED => {
                if let Some(n) = name_of(val) {
                    needed.push(n);
                }
            }
            DT_SONAME => {
                if let Some(n) = name_of(val) {
                    obj.metadata.insert("elf.soname".into(), n);
                }
            }
            DT_RPATH | DT_RUNPATH => {
                if let Some(n) = name_of(val) {
                    obj.metadata.insert("elf.runpath".into(), n);
                }
            }
            DT_INIT | DT_FINI => {
                if val != 0 {
                    obj.function_hints.push(FunctionHint {
                        addr: Addr(val),
                        size: None,
                        name: Some(if tag == DT_INIT {
                            "_init".into()
                        } else {
                            "_fini".into()
                        }),
                        provenance: Provenance::new(Evidence::InitArray),
                    });
                }
            }
            DT_PLTGOT => {
                obj.metadata
                    .insert("elf.pltgot".into(), format!("{val:#x}"));
            }
            DT_FLAGS_1 if val & DF_1_PIE != 0 => {
                obj.metadata.insert("elf.pie".into(), "true".into());
            }
            _ => {}
        }
    }
    if !needed.is_empty() {
        for imp in &mut obj.imports {
            if imp.library.is_none() && needed.len() == 1 {
                imp.library = Some(needed[0].clone());
            }
        }
        obj.metadata.insert("elf.needed".into(), needed.join(", "));
    }
}

/// `.init_array` and `.fini_array` hold pointers to functions that run before
/// and after main. Nothing else names them, so they are the only evidence for a
/// static constructor.
fn read_init_arrays(
    r: &Reader<'_>,
    shdrs: &[SecHdr],
    wide: bool,
    obj: &mut Object,
    caps: &r12e_core::Caps,
) {
    let step = if wide { 8 } else { 4 };
    for sh in shdrs
        .iter()
        .filter(|s| s.kind == SHT_INIT_ARRAY || s.kind == SHT_FINI_ARRAY)
    {
        let count = sh.size / step;
        if caps
            .check("init array entries", count, caps.symbols)
            .is_err()
        {
            continue;
        }
        for i in 0..count {
            let Ok(mut e) = r.slice_at("init array entry", sh.offset + i * step, step) else {
                break;
            };
            let Ok(v) = e.uword("pointer", wide) else {
                break;
            };
            // 0 and -1 are the "empty slot" conventions.
            if v == 0 || v == u64::MAX || v == u32::MAX as u64 {
                continue;
            }
            obj.function_hints.push(FunctionHint {
                addr: Addr(v),
                size: None,
                name: None,
                provenance: Provenance::new(Evidence::InitArray),
            });
        }
    }
}

/// Map PLT entries to the names they call, so an indirect call prints a name.
///
/// `.rela.plt` entries are in PLT slot order, and the PLT's first entry is the
/// resolver stub, so slot `i` of `.plt` corresponds to relocation `i - 1`.
fn read_plt_relocations(
    r: &Reader<'_>,
    shdrs: &[SecHdr],
    wide: bool,
    dynsym_names: &[String],
    obj: &mut Object,
    caps: &r12e_core::Caps,
) {
    let Some(plt) = obj.section(".plt").cloned() else {
        return;
    };
    if dynsym_names.is_empty() || plt.range.is_empty() {
        return;
    }

    // The PLT relocation table is the one named `.rela.plt` or `.rel.plt`.
    // Finding it through `sh_info` does not work: that field names the section
    // the relocations apply to, which is `.got.plt`, not the PLT.
    let Some((sh, _)) = shdrs.iter().zip(&obj.sections).find(|(sh, sec)| {
        (sh.kind == SHT_RELA || sh.kind == SHT_REL)
            && (sec.name == ".rela.plt" || sec.name == ".rel.plt")
    }) else {
        return;
    };

    let is_rela = sh.kind == SHT_RELA;
    let step = match (wide, is_rela) {
        (true, true) => 24,
        (true, false) => 16,
        (false, true) => 12,
        (false, false) => 8,
    };
    let count = sh.size / step;
    if count == 0 || caps.check("relocations", count, caps.relocations).is_err() {
        return;
    }
    // The PLT's layout is fixed per architecture: a resolver stub of one size
    // followed by entries of another. Dividing the section's length by the
    // relocation count instead gives the wrong answer whenever the section
    // also holds IFUNC entries, which it usually does.
    let (header, entry_size) = plt_layout(&obj.arch);
    if plt.range.len() < header + count * entry_size {
        obj.warnings.push(format!(
            ".plt is {:#x} bytes, too small for {count} entries of {entry_size:#x} \
             after a {header:#x}-byte header; thunks not named",
            plt.range.len()
        ));
        return;
    }

    for i in 0..count {
        let Ok(mut e) = r.slice_at("relocation", sh.offset + i * step, step) else {
            break;
        };
        if e.uword("r_offset", wide).is_err() {
            break;
        }
        let sym_index = if wide {
            let Ok(info) = e.u64("r_info") else { break };
            (info >> 32) as usize
        } else {
            let Ok(info) = e.u32("r_info") else { break };
            (info >> 8) as usize
        };
        let Some(name) = dynsym_names.get(sym_index).filter(|n| !n.is_empty()) else {
            continue;
        };
        let thunk = plt
            .range
            .start()
            .checked_add(header + i * entry_size)
            .filter(|a| plt.range.contains(*a));
        if let Some(imp) = obj.imports.iter_mut().find(|im| im.name == *name) {
            imp.thunk = thunk;
        }
        if let Some(t) = thunk {
            obj.function_hints.push(FunctionHint {
                addr: t,
                size: Some(entry_size),
                name: Some(format!("{name}@plt")),
                provenance: Provenance::new(Evidence::ImportThunk),
            });
        }
    }
}

/// The size of a PLT's resolver stub and of each entry after it.
fn plt_layout(arch: &Arch) -> (u64, u64) {
    match arch {
        Arch::AArch64 => (32, 16),
        Arch::X86_64 | Arch::X86 => (16, 16),
        Arch::Arm => (20, 12),
        _ => (16, 16),
    }
}

/// Build id and any other note worth reporting.
fn read_notes(r: &Reader<'_>, phdrs: &[ProgHdr], shdrs: &[SecHdr], obj: &mut Object) {
    if let Some(p) = phdrs.iter().find(|p| p.kind == PT_INTERP) {
        if let Ok(t) = r.slice_at("interp", p.offset, p.filesz) {
            if let Ok(s) = t.cstr_at("interp", 0, p.filesz) {
                obj.metadata
                    .insert("elf.interp".into(), String::from_utf8_lossy(s).into_owned());
            }
        }
    }
    if phdrs
        .iter()
        .any(|p| p.kind == PT_GNU_STACK && p.flags & 1 != 0)
    {
        obj.metadata.insert("elf.exec_stack".into(), "true".into());
    }
    if phdrs.iter().any(|p| p.kind == PT_GNU_RELRO) {
        obj.metadata.insert("elf.relro".into(), "true".into());
    }

    let notes = phdrs
        .iter()
        .filter(|p| p.kind == PT_NOTE)
        .map(|p| (p.offset, p.filesz))
        .chain(
            shdrs
                .iter()
                .filter(|s| s.kind == 7)
                .map(|s| (s.offset, s.size)),
        );
    for (off, size) in notes {
        let Ok(mut n) = r.slice_at("note", off, size) else {
            continue;
        };
        while n.remaining() >= 12 {
            let (Ok(namesz), Ok(descsz), Ok(kind)) =
                (n.u32("n_namesz"), n.u32("n_descsz"), n.u32("n_type"))
            else {
                break;
            };
            let Ok(name) = n.bytes("note name", (namesz as u64).next_multiple_of(4)) else {
                break;
            };
            let Ok(desc) = n.bytes("note desc", (descsz as u64).next_multiple_of(4)) else {
                break;
            };
            // NT_GNU_BUILD_ID
            if kind == 3 && name.starts_with(b"GNU\0") {
                let hex: String = desc[..descsz.min(64) as usize]
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect();
                obj.metadata.insert("elf.build_id".into(), hex);
            }
        }
    }
}

/// Function starts from `.eh_frame`, the best boundary evidence an ELF carries.
/// Read what the compiler recorded, when it recorded anything.
///
/// A function the debug information names is a fact, not an inference, so the
/// hint it produces outranks everything the analysis would work out for
/// itself.
fn read_debug_info(r: &Reader<'_>, shdrs: &[SecHdr], obj: &mut Object, hints: bool) {
    let section = |name: &str| -> &[u8] {
        match obj.section(name) {
            Some(s) if s.file_size > 0 => r
                .bytes_at("debug section", s.file_offset, s.file_size)
                .unwrap_or(&[]),
            _ => &[],
        }
    };
    // A relocatable object writes zero where an address goes and leaves a
    // relocation to fill it in, so every function would appear to start at the
    // same place until they are applied.
    let info_bytes = relocated(r, shdrs, obj, ".debug_info", section(".debug_info"));
    let line_bytes = relocated(r, shdrs, obj, ".debug_line", section(".debug_line"));
    // DWARF 5 puts the addresses in a table of their own and refers to them by
    // index, so that table needs its relocations as much as the rest: without
    // them every function in the unit resolves to zero.
    let addr_bytes = relocated(r, shdrs, obj, ".debug_addr", section(".debug_addr"));
    // The string offsets are relocated too: an index resolves through this
    // table, and unrelocated it points every name at the first string in the
    // section, which is the producer.
    let str_offset_bytes = relocated(
        r,
        shdrs,
        obj,
        ".debug_str_offsets",
        section(".debug_str_offsets"),
    );
    let rnglist_bytes = relocated(r, shdrs, obj, ".debug_rnglists", section(".debug_rnglists"));
    let sections = crate::dwarf::Sections {
        info: &info_bytes,
        abbrev: section(".debug_abbrev"),
        str: section(".debug_str"),
        line_str: section(".debug_line_str"),
        str_offsets: &str_offset_bytes,

        addr: &addr_bytes,
        rnglists: &rnglist_bytes,
        line: &line_bytes,
    };
    if sections.is_empty() {
        return;
    }
    let info = crate::dwarf::parse(&sections, obj.endian);
    for (addr, f) in info.functions.iter().filter(|_| hints) {
        if f.name.is_empty() {
            continue;
        }
        obj.function_hints.push(FunctionHint {
            addr: *addr,
            size: f.size.filter(|s| *s > 0),
            name: Some(f.name.clone()),
            provenance: Provenance::new(Evidence::DebugInfo),
        });
    }
    obj.debug = Some(info);
}

/// How many relocations a section really holds.
///
/// The declared size is a number from the file and can say anything; what
/// bounds the work is how many entries actually fit in the file.
fn relocation_count(r: &Reader<'_>, sh: &SecHdr, step: u64) -> u64 {
    let step = step.max(1);
    let declared = sh.size / step;
    let available = (r.len() as u64).saturating_sub(sh.offset) / step;
    declared.min(available)
}

/// Apply the relocations that name code and data addresses.
///
/// Only the kinds a compiler emits inside an object file, and only where the
/// symbol resolves to something this file defines: an external symbol has no
/// address here, and writing a guess would produce a call graph that points
/// somewhere wrong rather than nowhere.
fn apply_code_relocations(r: &Reader<'_>, shdrs: &[SecHdr], obj: &mut Object) {
    let wide = obj.bits == Bits::Bits64;
    let step: u64 = if wide { 24 } else { 12 };
    let arch = obj.arch.clone();

    let mut patches: Vec<(Addr, Vec<u8>)> = Vec::new();
    for sh in shdrs.iter().filter(|s| s.kind == SHT_RELA) {
        let Some(target) = obj.sections.get(sh.info as usize).cloned() else {
            continue;
        };
        // Any section that is mapped: a jump table lives in `.rodata` and is
        // as much in need of its relocations as the code that reads it.
        if target.range.is_empty() || target.name.starts_with(".debug") {
            continue;
        }
        for i in 0..relocation_count(r, sh, step) {
            let Ok(mut e) = r.slice_at("relocation", sh.offset + i * step, step) else {
                break;
            };
            let (offset, info, addend) = if wide {
                let (Ok(o), Ok(n), Ok(a)) = (
                    e.u64("r_offset"),
                    e.u64("r_info"),
                    e.i64("r_addend"),
                ) else {
                    continue;
                };
                (o, n, a)
            } else {
                let (Ok(o), Ok(n), Ok(a)) = (
                    e.u32("r_offset"),
                    e.u32("r_info"),
                    e.i32("r_addend"),
                ) else {
                    continue;
                };
                (o as u64, n as u64, a as i64)
            };
            let symbol = if wide { info >> 32 } else { info >> 8 };
            let kind = if wide { info & 0xffff_ffff } else { info & 0xff };
            let Some(value) = symbol_value(r, shdrs, obj, symbol) else {
                continue;
            };
            // Where the fixup goes, which is an offset into the section the
            // relocation names.
            let place = target.range.start().get().wrapping_add(offset);
            // However much is there: the last entry of a table sits at the
            // end of its section, and asking for eight bytes there fails.
            let mut word = [0u8; 8];
            let available = (1..=8)
                .rev()
                .find_map(|n| obj.memory.slice(Addr(place), n));
            let Some(existing) = available else { continue };
            word[..existing.len()].copy_from_slice(existing);
            if let Some(bytes) = fixup(&arch, kind, value, addend, place, &word) {
                patches.push((Addr(place), bytes));
            }
        }
    }
    for (at, bytes) in patches {
        obj.memory.patch(at, &bytes);
    }
}

/// The bytes one relocation writes, or nothing when its kind is not handled.
fn fixup(
    arch: &Arch,
    kind: u64,
    symbol: u64,
    addend: i64,
    place: u64,
    existing: &[u8; 8],
) -> Option<Vec<u8>> {
    let value = symbol.wrapping_add(addend as u64);
    let relative = value.wrapping_sub(place);
    let word = u32::from_le_bytes([existing[0], existing[1], existing[2], existing[3]]);

    match arch {
        Arch::X86_64 => Some(match kind {
            // R_X86_64_64.
            1 => value.to_le_bytes().to_vec(),
            // PC32 and PLT32, which differ only in whether a stub may be used.
            2 | 4 => (relative as u32).to_le_bytes().to_vec(),
            // The 32-bit absolute forms.
            10 | 11 => (value as u32).to_le_bytes().to_vec(),
            _ => return None,
        }),
        Arch::AArch64 => Some(match kind {
            // ABS64.
            257 => value.to_le_bytes().to_vec(),
            // ABS32.
            258 => (value as u32).to_le_bytes().to_vec(),
            // PREL64 and PREL32.
            260 => relative.to_le_bytes().to_vec(),
            261 => (relative as u32).to_le_bytes().to_vec(),
            // ADR_PREL_PG_HI21: the page difference, in the split immediate an
            // `adrp` carries.
            275 | 276 => {
                let pages = (value & !0xfff).wrapping_sub(place & !0xfff) as i64 >> 12;
                let immlo = (pages as u32 & 3) << 29;
                let immhi = ((pages as u32 >> 2) & 0x7ffff) << 5;
                ((word & !0x60ff_ffe0) | immlo | immhi).to_le_bytes().to_vec()
            }
            // The twelve-bit offsets: an add, or a load or store scaled by its
            // access size.
            277 => {
                let imm = (value & 0xfff) as u32;
                ((word & !0x003f_fc00) | (imm << 10)).to_le_bytes().to_vec()
            }
            278 | 284 | 285 | 286 | 299 => {
                let scale = match kind {
                    278 => 0,
                    284 => 1,
                    285 => 2,
                    286 => 3,
                    _ => 4,
                };
                let imm = ((value & 0xfff) >> scale) as u32;
                ((word & !0x003f_fc00) | (imm << 10)).to_le_bytes().to_vec()
            }
            // JUMP26 and CALL26: the branch displacement in instructions.
            282 | 283 => {
                let imm = ((relative as i64 >> 2) as u32) & 0x03ff_ffff;
                ((word & !0x03ff_ffff) | imm).to_le_bytes().to_vec()
            }
            // CONDBR19 and the test-and-branch form.
            280 => {
                let imm = ((relative as i64 >> 2) as u32 & 0x7ffff) << 5;
                ((word & !0x00ff_ffe0) | imm).to_le_bytes().to_vec()
            }
            _ => return None,
        }),
        _ => None,
    }
}

/// A copy of a section with its relocations applied.
///
/// Only the absolute kinds, which is all debug information uses: the value
/// written is the symbol's address plus the addend. Anything else is left
/// alone, because writing a guess into a debug section produces confident
/// nonsense rather than a gap.
fn relocated(
    r: &Reader<'_>,
    shdrs: &[SecHdr],
    obj: &Object,
    name: &str,
    data: &[u8],
) -> Vec<u8> {
    let mut out = data.to_vec();
    if data.is_empty() {
        return out;
    }
    let Some(target) = obj.sections.iter().position(|s| s.name == name) else {
        return out;
    };
    let wide = obj.bits == Bits::Bits64;
    let step: u64 = if wide { 24 } else { 12 };

    for (n, sh) in shdrs.iter().enumerate() {
        if sh.kind != SHT_RELA || sh.info as usize != target {
            continue;
        }
        let _ = n;
        for i in 0..relocation_count(r, sh, step) {
            let at = sh.offset + i * step;
            let Ok(mut e) = r.slice_at("relocation", at, step) else {
                continue;
            };
            let (offset, info, addend) = if wide {
                let Ok(o) = e.u64("r_offset") else { continue };
                let Ok(i) = e.u64("r_info") else { continue };
                let Ok(a) = e.i64("r_addend") else { continue };
                (o, i, a)
            } else {
                let Ok(o) = e.u32("r_offset") else { continue };
                let Ok(i) = e.u32("r_info") else { continue };
                let Ok(a) = e.i32("r_addend") else { continue };
                (o as u64, i as u64, a as i64)
            };
            let symbol = if wide { info >> 32 } else { info >> 8 };
            let kind = if wide { info & 0xffff_ffff } else { info & 0xff };
            // The absolute relocations, which are the only ones a debug
            // section uses: 1 is 64-bit on both architectures this supports,
            // and the 32-bit ones differ by number.
            let size = match (&obj.arch, kind) {
                (Arch::X86_64, 1) | (Arch::AArch64, 257) => 8,
                (Arch::X86_64, 10) | (Arch::X86_64, 11) | (Arch::AArch64, 258) => 4,
                _ => continue,
            };
            let Some(value) = symbol_value(r, shdrs, obj, symbol) else {
                continue;
            };
            let result = value.wrapping_add(addend as u64);
            // The offset comes from the file, so it can be anything.
            let Ok(start) = usize::try_from(offset) else {
                continue;
            };
            let Some(slot) = out.get_mut(start..start.saturating_add(size)) else {
                continue;
            };
            for (k, byte) in slot.iter_mut().enumerate() {
                *byte = (result >> (k * 8)) as u8;
            }
        }
    }
    out
}

/// The address a relocation's symbol resolves to, which for a section symbol
/// is where the loader put that section.
fn symbol_value(r: &Reader<'_>, shdrs: &[SecHdr], obj: &Object, index: u64) -> Option<u64> {
    let wide = obj.bits == Bits::Bits64;
    let entsize: u64 = if wide { 24 } else { 16 };
    let sh = shdrs.iter().find(|s| s.kind == SHT_SYMTAB)?;
    let at = sh.offset + index * entsize;
    let mut e = r.slice_at("symbol", at, entsize).ok()?;
    if wide {
        let _name = e.u32("st_name").ok()?;
        let _info = e.u8("st_info").ok()?;
        let _other = e.u8("st_other").ok()?;
        let shndx = e.u16("st_shndx").ok()?;
        let value = e.u64("st_value").ok()?;
        Some(section_base(obj, shndx)? + value)
    } else {
        let _name = e.u32("st_name").ok()?;
        let value = e.u32("st_value").ok()? as u64;
        let _size = e.u32("st_size").ok()?;
        let _info = e.u8("st_info").ok()?;
        let _other = e.u8("st_other").ok()?;
        let shndx = e.u16("st_shndx").ok()?;
        Some(section_base(obj, shndx)? + value)
    }
}

fn section_base(obj: &Object, index: u16) -> Option<u64> {
    obj.sections
        .get(index as usize)
        .map(|s| s.range.start().get())
}

fn read_eh_frame(r: &Reader<'_>, phdrs: &[ProgHdr], obj: &mut Object) {
    let Some(sec) = obj.section(".eh_frame").cloned() else {
        // A stripped binary can still have PT_GNU_EH_FRAME pointing at the
        // lookup table even when section headers are gone.
        let _ = phdrs.iter().find(|p| p.kind == PT_GNU_EH_FRAME);
        return;
    };
    if sec.file_size == 0 {
        return;
    }
    let Ok(body) = r.bytes_at(".eh_frame", sec.file_offset, sec.file_size) else {
        return;
    };
    match crate::ehframe::function_starts(body, sec.range.start(), obj.bits) {
        Ok(fns) => {
            for (addr, size) in fns {
                obj.function_hints.push(FunctionHint {
                    addr,
                    size: (size != 0).then_some(size),
                    name: None,
                    provenance: Provenance::new(Evidence::EhFrame),
                });
            }
        }
        Err(e) => obj.warnings.push(format!(".eh_frame: {e}")),
    }
}


/// True when a name is one a function could have.
///
/// ARM and AArch64 write mapping symbols — `$x` for code, `$d` for data — at
/// every transition, and they are not functions. Nor are the assembler's local
/// labels.
fn is_code_name(name: &str) -> bool {
    !name.is_empty() && !name.starts_with('$') && !name.starts_with(".L")
}

/// True when an address falls inside a section the loader marked executable.
fn in_executable_section(obj: &Object, addr: Addr) -> bool {
    obj.sections
        .iter()
        .any(|s| s.exec && s.range.contains(addr))
}
