//! Mach-O, thin and fat.
//!
//! A fat file is a big-endian index of thin ones; the requested architecture is
//! selected, or the first slice if none was asked for.
//!
//! `LC_FUNCTION_STARTS` is why this format is worth reading carefully: it lists
//! every function's start as a chain of ULEB128 deltas, it survives stripping,
//! and nothing else in a stripped Mach-O says where the functions are.

use std::collections::BTreeMap;

use r12e_core::{
    Addr, AddrRange, Arch, Bits, Caps, Endian, Error, Evidence, MemoryMap, Perms, Provenance,
    Reader, Result, Segment,
};

use crate::{
    Binding, Export, Format, FunctionHint, Import, LoadOptions, Object, Section, Symbol, SymbolKind,
};

const MH_MAGIC_64: u32 = 0xfeed_facf;
const MH_CIGAM_64: u32 = 0xcffa_edfe;
const MH_MAGIC_32: u32 = 0xfeed_face;
const MH_CIGAM_32: u32 = 0xcefa_edfe;
const FAT_MAGIC: u32 = 0xcafe_babe;
const FAT_MAGIC_64: u32 = 0xcafe_babf;

// Load commands.
const LC_SEGMENT: u32 = 0x01;
const LC_SYMTAB: u32 = 0x02;
const LC_SEGMENT_64: u32 = 0x19;
const LC_LOAD_DYLIB: u32 = 0x0c;
const LC_ID_DYLIB: u32 = 0x0d;
const LC_UUID: u32 = 0x1b;
const LC_FUNCTION_STARTS: u32 = 0x26;
const LC_MAIN: u32 = 0x8000_0028;

// File types.
const MH_OBJECT: u32 = 1;
const MH_EXECUTE: u32 = 2;
const MH_DYLIB: u32 = 6;
const MH_BUNDLE: u32 = 8;
const MH_DSYM: u32 = 10;

// Header flags.
const MH_PIE: u32 = 0x0020_0000;

// nlist n_type.
const N_STAB: u8 = 0xe0;
const N_TYPE: u8 = 0x0e;
const N_EXT: u8 = 0x01;
const N_UNDF: u8 = 0x0;
const N_SECT: u8 = 0xe;

// Section flags: the low byte is the section type.
const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;
const S_ZEROFILL: u32 = 0x1;

/// True when the buffer starts with any Mach-O magic, thin or fat.
pub fn is_macho(data: &[u8]) -> bool {
    if data.len() < 4 {
        return false;
    }
    let le = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
    let be = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
    matches!(le, MH_MAGIC_64 | MH_CIGAM_64 | MH_MAGIC_32 | MH_CIGAM_32)
        || matches!(be, FAT_MAGIC | FAT_MAGIC_64)
}

/// Parse a Mach-O file.
pub fn load(data: &[u8], opts: &LoadOptions) -> Result<Object> {
    if !is_macho(data) {
        return Err(Error::NotRecognized { expected: "Mach-O" });
    }
    let head = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
    if matches!(head, FAT_MAGIC | FAT_MAGIC_64) {
        return load_fat(data, opts, head == FAT_MAGIC_64);
    }
    load_thin(data, opts, 0)
}

/// Pick a slice out of a fat file and load it.
///
/// The index is big-endian whatever the slices are, which is the one place a
/// reader of this format has to change byte order mid-file.
fn load_fat(data: &[u8], opts: &LoadOptions, wide: bool) -> Result<Object> {
    let r = Reader::new(data, Endian::Big);
    let mut h = r;
    h.skip("fat magic", 4)?;
    let count = h.u32("nfat_arch")?;
    opts.caps.check("fat slices", count as u64, 64)?;

    let step = if wide { 32 } else { 20 };
    let mut first: Option<u64> = None;
    for i in 0..count as u64 {
        let mut a = r.slice_at("fat_arch", 8 + i * step, step)?;
        let cputype = a.u32("cputype")? as i32;
        let _sub = a.u32("cpusubtype")?;
        let offset = a.uword("offset", wide)?;
        let _size = a.uword("size", wide)?;
        let arch = cpu_to_arch(cputype);
        if first.is_none() {
            first = Some(offset);
        }
        if opts.arch.as_ref().is_some_and(|want| *want == arch) {
            return load_thin(data, opts, offset);
        }
    }
    let at = first.ok_or(Error::BadField {
        field: "nfat_arch",
        value: 0,
        reason: "means the file contains no slices at all",
    })?;
    let mut obj = load_thin(data, opts, at)?;
    if count > 1 {
        obj.metadata.insert(
            "macho.fat".into(),
            format!("{count} slices; loaded the first, pass --arch to choose"),
        );
    }
    Ok(obj)
}

fn cpu_to_arch(cputype: i32) -> Arch {
    match cputype {
        0x0100_0007 => Arch::X86_64,
        7 => Arch::X86,
        0x0100_000c => Arch::AArch64,
        12 => Arch::Arm,
        other => Arch::Unknown(other as u32),
    }
}

fn file_type_name(t: u32) -> &'static str {
    match t {
        MH_OBJECT => "object",
        MH_EXECUTE => "executable",
        MH_DYLIB => "dylib",
        MH_BUNDLE => "bundle",
        MH_DSYM => "debug symbols",
        _ => "unknown",
    }
}

/// Parse one thin Mach-O, starting at `base` in the file.
fn load_thin(data: &[u8], opts: &LoadOptions, base: u64) -> Result<Object> {
    let caps = &opts.caps;
    let mut warnings = Vec::new();

    let magic = Reader::le(data).slice_at("magic", base, 4)?.u32("magic")?;
    let (wide, endian) = match magic {
        MH_MAGIC_64 => (true, Endian::Little),
        MH_CIGAM_64 => (true, Endian::Big),
        MH_MAGIC_32 => (false, Endian::Little),
        MH_CIGAM_32 => (false, Endian::Big),
        other => {
            return Err(Error::BadField {
                field: "mach_header magic",
                value: other as u64,
                reason: "is not a Mach-O magic number",
            });
        }
    };

    let r = Reader::new(data, endian);
    let mut h = r;
    h.seek("mach_header", base + 4)?;
    let cputype = h.u32("cputype")? as i32;
    let _cpusubtype = h.u32("cpusubtype")?;
    let filetype = h.u32("filetype")?;
    let ncmds = h.u32("ncmds")?;
    let sizeofcmds = h.u32("sizeofcmds")?;
    let flags = h.u32("flags")?;
    if wide {
        h.u32("reserved")?;
    }
    let cmds_at = h.pos();
    caps.check("load commands", ncmds as u64, caps.sections)?;

    let arch = cpu_to_arch(cputype);
    let bits = if wide { Bits::Bits64 } else { Bits::Bits32 };

    let mut memory = MemoryMap::new();
    let mut sections: Vec<Section> = Vec::new();
    let mut metadata: BTreeMap<String, String> = BTreeMap::new();
    let mut symbols: Vec<Symbol> = Vec::new();
    let mut imports: Vec<Import> = Vec::new();
    let mut exports: Vec<Export> = Vec::new();
    let mut hints: Vec<FunctionHint> = Vec::new();
    let mut dylibs: Vec<String> = Vec::new();
    let mut entry: Option<Addr> = None;
    let mut text_start: Option<Addr> = None;
    let mut function_starts: Option<(u64, u64)> = None;
    let mut symtab: Option<(u32, u32, u32, u32)> = None;
    // An object file lays every section at address zero, as ELF and COFF do.
    let relocatable = filetype == MH_OBJECT;
    let mut next_free = opts.base.map(|b| b.get()).unwrap_or(0x1_0000_0000);

    let mut at = cmds_at;
    let end = cmds_at + sizeofcmds as u64;
    for _ in 0..ncmds {
        if at >= end {
            break;
        }
        let Ok(mut c) = r.slice_at("load command", at, 8) else {
            warnings.push("load commands run past the end of the file".into());
            break;
        };
        let cmd = c.u32("cmd")?;
        let size = c.u32("cmdsize")? as u64;
        if size < 8 {
            warnings.push(format!("load command {cmd:#x} claims {size} bytes"));
            break;
        }
        let Ok(body) = r.slice_at("load command body", at, size) else {
            break;
        };
        at += size;

        match cmd {
            LC_SEGMENT | LC_SEGMENT_64 => {
                let seg_wide = cmd == LC_SEGMENT_64;
                let mut s = body;
                s.skip("cmd and cmdsize", 8)?;
                let name = fixed_name(s.bytes("segname", 16)?);
                let vmaddr = s.uword("vmaddr", seg_wide)?;
                let vmsize = s.uword("vmsize", seg_wide)?;
                let fileoff = s.uword("fileoff", seg_wide)?;
                let filesize = s.uword("filesize", seg_wide)?;
                let maxprot = s.u32("maxprot")?;
                let initprot = s.u32("initprot")?;
                let nsects = s.u32("nsects")?;
                let _segflags = s.u32("flags")?;
                let _ = (vmsize, maxprot);

                // A segment with no sections still maps, which is how
                // __PAGEZERO and __LINKEDIT appear.
                if nsects == 0 && filesize > 0 && !relocatable {
                    if let Some(range) = AddrRange::sized(Addr(vmaddr), filesize) {
                        let body = r
                            .bytes_at("segment body", base + fileoff, filesize)
                            .map(|b| b.to_vec())
                            .unwrap_or_default();
                        memory.add(Segment::new(
                            range,
                            prot(initprot),
                            name.clone(),
                            base + fileoff,
                            body,
                        )?);
                    }
                }

                caps.check("sections", nsects as u64, caps.sections)?;
                for _ in 0..nsects {
                    let sect_size = if seg_wide { 80 } else { 68 };
                    let Ok(mut sec) = s.slice_at("section", s.pos(), sect_size) else {
                        break;
                    };
                    s.skip("section", sect_size)?;
                    let sectname = fixed_name(sec.bytes("sectname", 16)?);
                    let segname = fixed_name(sec.bytes("segname", 16)?);
                    let addr = sec.uword("addr", seg_wide)?;
                    let size = sec.uword("size", seg_wide)?;
                    let offset = sec.u32("offset")? as u64;
                    let align = sec.u32("align")?;
                    let _reloff = sec.u32("reloff")?;
                    let _nreloc = sec.u32("nreloc")?;
                    let sflags = sec.u32("flags")?;

                    let exec = sflags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS) != 0;
                    let zerofill = sflags & 0xff == S_ZEROFILL;
                    let full = format!("{segname},{sectname}");

                    let va = if relocatable {
                        let alignment = 1u64 << align.min(16);
                        let a = next_free.next_multiple_of(alignment.max(1));
                        next_free = a + size;
                        a
                    } else {
                        addr
                    };
                    let Some(range) = AddrRange::sized(Addr(va), size) else {
                        warnings.push(format!("section {full} does not fit the address space"));
                        continue;
                    };
                    let file_size = if zerofill { 0 } else { size };
                    let body = if zerofill {
                        Vec::new()
                    } else {
                        r.bytes_at("section body", base + offset, file_size)
                            .map(|b| b.to_vec())
                            .unwrap_or_default()
                    };
                    if !range.is_empty() {
                        let perms = if relocatable {
                            Perms::new(true, !exec, exec)
                        } else {
                            prot(initprot)
                        };
                        memory.add(Segment::new(
                            range,
                            perms,
                            full.clone(),
                            base + offset,
                            body,
                        )?);
                    }
                    if full == "__TEXT,__text" {
                        text_start = Some(Addr(va));
                    }
                    sections.push(Section {
                        name: full,
                        range,
                        file_offset: base + offset,
                        file_size,
                        exec,
                        write: !relocatable && prot(initprot).write,
                        kind: sflags,
                    });
                }
                if name == "__TEXT" && text_start.is_none() {
                    text_start = Some(Addr(vmaddr));
                }
            }
            LC_SYMTAB => {
                let mut s = body;
                s.skip("cmd and cmdsize", 8)?;
                symtab = Some((
                    s.u32("symoff")?,
                    s.u32("nsyms")?,
                    s.u32("stroff")?,
                    s.u32("strsize")?,
                ));
            }
            LC_FUNCTION_STARTS => {
                let mut s = body;
                s.skip("cmd and cmdsize", 8)?;
                function_starts = Some((s.u32("dataoff")? as u64, s.u32("datasize")? as u64));
            }
            LC_MAIN => {
                let mut s = body;
                s.skip("cmd and cmdsize", 8)?;
                let entryoff = s.u64("entryoff")?;
                // LC_MAIN's offset is from the start of the file, which for a
                // loaded image is the start of __TEXT.
                entry = text_start
                    .or(Some(Addr::ZERO))
                    .and_then(|t| t.checked_add(entryoff));
            }
            LC_LOAD_DYLIB | LC_ID_DYLIB => {
                let mut s = body;
                s.skip("cmd and cmdsize", 8)?;
                let name_off = s.u32("name offset")? as u64;
                if let Ok(n) = body.cstr_at("dylib name", name_off, caps.string_len) {
                    let n = String::from_utf8_lossy(n).into_owned();
                    if cmd == LC_ID_DYLIB {
                        metadata.insert("macho.id".into(), n);
                    } else {
                        dylibs.push(n);
                    }
                }
            }
            LC_UUID => {
                if let Ok(u) = body.bytes_at("uuid", 8, 16) {
                    metadata.insert(
                        "macho.uuid".into(),
                        u.iter().map(|b| format!("{b:02x}")).collect(),
                    );
                }
            }
            _ => {}
        }
    }

    metadata.insert("macho.type".into(), file_type_name(filetype).into());
    if flags & MH_PIE != 0 {
        metadata.insert("macho.pie".into(), "true".into());
    }
    if !dylibs.is_empty() {
        metadata.insert("macho.dylibs".into(), dylibs.join(", "));
    }

    let mut obj = Object {
        debug: None,
        format: Format::MachO,
        arch,
        endian,
        bits,
        entry,
        image_base: text_start.unwrap_or(Addr::ZERO),
        pic: flags & MH_PIE != 0 || filetype == MH_DYLIB,
        memory,
        sections,
        symbols: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        function_hints: Vec::new(),
        metadata,
        warnings,
    };

    if let Some((symoff, nsyms, stroff, strsize)) = symtab {
        read_symbols(
            &r,
            base,
            wide,
            symoff,
            nsyms,
            stroff,
            strsize,
            relocatable,
            &mut obj,
            &mut symbols,
            &mut imports,
            &mut exports,
            &mut hints,
            caps,
        );
    }
    if let Some((off, size)) = function_starts {
        read_function_starts(&r, base, off, size, text_start, &mut hints, &mut obj, caps);
    }

    obj.symbols = symbols;
    obj.imports = imports;
    obj.exports = exports;
    obj.function_hints = hints;
    if let Some(e) = obj.entry {
        obj.function_hints.push(FunctionHint {
            addr: e,
            size: None,
            name: Some("main".into()),
            provenance: Provenance::new(Evidence::EntryPoint),
        });
    }
    obj.normalize_symbols();
    obj.normalize_hints();
    Ok(obj)
}

fn prot(initprot: u32) -> Perms {
    Perms::new(initprot & 1 != 0, initprot & 2 != 0, initprot & 4 != 0)
}

/// A fixed-width name field, which is NUL-padded rather than NUL-terminated.
fn fixed_name(b: &[u8]) -> String {
    let end = b.iter().position(|c| *c == 0).unwrap_or(b.len());
    String::from_utf8_lossy(&b[..end]).into_owned()
}

#[allow(clippy::too_many_arguments)]
fn read_symbols(
    r: &Reader<'_>,
    base: u64,
    wide: bool,
    symoff: u32,
    nsyms: u32,
    stroff: u32,
    strsize: u32,
    relocatable: bool,
    obj: &mut Object,
    symbols: &mut Vec<Symbol>,
    imports: &mut Vec<Import>,
    exports: &mut Vec<Export>,
    hints: &mut Vec<FunctionHint>,
    caps: &Caps,
) {
    if caps.check("symbols", nsyms as u64, caps.symbols).is_err() {
        obj.warnings
            .push(format!("{nsyms} symbols exceeds the cap; skipped"));
        return;
    }
    let Ok(strings) = r.slice_at("string table", base + stroff as u64, strsize as u64) else {
        obj.warnings.push("string table is not readable".into());
        return;
    };
    let step = if wide { 16 } else { 12 };

    for i in 0..nsyms as u64 {
        let Ok(mut s) = r.slice_at("nlist", base + symoff as u64 + i * step, step) else {
            break;
        };
        let (Ok(strx), Ok(ntype), Ok(nsect), Ok(_desc)) = (
            s.u32("n_strx"),
            s.u8("n_type"),
            s.u8("n_sect"),
            s.u16("n_desc"),
        ) else {
            break;
        };
        let Ok(value) = s.uword("n_value", wide) else {
            break;
        };
        // Debug symbols describe source, not code.
        if ntype & N_STAB != 0 {
            continue;
        }
        let name = strings
            .cstr_at("symbol name", strx as u64, caps.string_len)
            .map(|b| String::from_utf8_lossy(b).into_owned())
            .unwrap_or_default();
        if name.is_empty() {
            continue;
        }
        // Mach-O prefixes C symbols with an underscore.
        let clean = name.strip_prefix('_').unwrap_or(&name).to_string();

        let kind_bits = ntype & N_TYPE;
        let external = ntype & N_EXT != 0;
        let undefined = kind_bits == N_UNDF;

        let addr = if undefined {
            Addr::ZERO
        } else if relocatable && nsect > 0 {
            // In an object the value is an offset into its section.
            match obj.sections.get(nsect as usize - 1) {
                Some(sec) => Addr(sec.range.start().get().wrapping_add(value)),
                None => Addr(value),
            }
        } else {
            Addr(value)
        };

        let in_code = addr != Addr::ZERO && obj.memory.is_executable(addr);
        let kind = if undefined {
            SymbolKind::Undefined
        } else if in_code {
            SymbolKind::Function
        } else {
            SymbolKind::Object
        };

        if undefined {
            imports.push(Import {
                name: clean.clone(),
                library: None,
                thunk: None,
            });
        } else if external && kind_bits == N_SECT {
            exports.push(Export {
                name: clean.clone(),
                addr,
                ordinal: None,
            });
        }
        if in_code {
            // An assembler temporary marks a place, not a function, and letting
            // one name a function hides the real name at the same address.
            let temporary = name.starts_with("ltmp")
                || name.starts_with("l_")
                || name.starts_with("L")
                || clean.starts_with("ltmp");
            hints.push(FunctionHint {
                addr,
                size: None,
                name: (!temporary).then(|| clean.clone()),
                provenance: Provenance::new(Evidence::SymbolTable),
            });
        }

        symbols.push(Symbol {
            name: clean,
            addr,
            size: 0,
            kind,
            binding: if external {
                Binding::Global
            } else {
                Binding::Local
            },
            dynamic: false,
        });
    }
}

/// `LC_FUNCTION_STARTS`: a chain of ULEB128 deltas from the text segment.
///
/// The best boundary evidence a Mach-O carries, and the only one a stripped
/// binary keeps.
#[allow(clippy::too_many_arguments)]
fn read_function_starts(
    r: &Reader<'_>,
    base: u64,
    off: u64,
    size: u64,
    text_start: Option<Addr>,
    hints: &mut Vec<FunctionHint>,
    obj: &mut Object,
    caps: &Caps,
) {
    let Some(start) = text_start else {
        obj.warnings
            .push("LC_FUNCTION_STARTS with no __TEXT to measure from".into());
        return;
    };
    let Ok(mut d) = r.slice_at("function starts", base + off, size) else {
        return;
    };
    let mut at = start.get();
    let mut count = 0u64;
    while d.remaining() > 0 {
        let Ok(delta) = d.uleb128("function start delta") else {
            break;
        };
        // A zero delta terminates the chain.
        if delta == 0 {
            break;
        }
        let Some(next) = at.checked_add(delta) else {
            break;
        };
        at = next;
        count += 1;
        if caps.check("function starts", count, caps.symbols).is_err() {
            break;
        }
        let addr = Addr(at);
        if obj.memory.is_executable(addr) {
            hints.push(FunctionHint {
                addr,
                size: None,
                name: None,
                provenance: Provenance::new(Evidence::MachFunctionStarts),
            });
        }
    }
}
