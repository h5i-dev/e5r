//! PE and COFF.
//!
//! Two formats in one file. A linked image starts with a DOS stub whose
//! `e_lfanew` points at the PE signature; a COFF object starts with the same
//! file header the PE carries, and nothing else. They share the section table
//! and the symbol table, so they share most of this module.
//!
//! The exception directory is why PE is worth reading carefully: on x86-64 and
//! ARM64 every non-leaf function has a `RUNTIME_FUNCTION` entry giving its
//! exact start and end. It is the best function-boundary evidence any format
//! offers and it survives stripping, which is the same reason `.eh_frame`
//! matters on ELF. That directory, the unwind data behind it and the SEH scope
//! tables live in [`crate::pdata`]; the TLS callback array, the base relocation
//! table and the load config live in [`crate::windirs`].
//!
//! One gap is deliberate and visible in the output. The control-flow-guard
//! function table and the SafeSEH handler table are both linker-built lists of
//! real function entries, but `Evidence` has no variant that describes them,
//! and every other variant would either overstate or understate the claim. They
//! are returned in [`WindowsInfo::load_config`] and counted in the metadata
//! rather than emitted as hints. Adding `Evidence::GuardTable` with
//! `Strength::Proven` to `r12e-core` is what would close it.

use std::collections::BTreeMap;

use r12e_core::{
    Addr, AddrRange, Arch, Bits, Caps, Endian, Error, Evidence, MemoryMap, Perms, Provenance,
    Reader, Result, Segment,
};

use crate::{
    Binding, Export, Format, FunctionHint, Import, LoadOptions, Object, Section, Symbol,
    SymbolKind, pdata, windirs,
};

const DOS_MAGIC: [u8; 2] = *b"MZ";
const PE_MAGIC: [u8; 4] = [b'P', b'E', 0, 0];

// Machine numbers.
const IMAGE_FILE_MACHINE_I386: u16 = 0x014c;
const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;
const IMAGE_FILE_MACHINE_ARM: u16 = 0x01c0;
const IMAGE_FILE_MACHINE_ARMNT: u16 = 0x01c4;
const IMAGE_FILE_MACHINE_ARM64: u16 = 0xaa64;

// Section characteristics.
const SCN_CNT_CODE: u32 = 0x0000_0020;
const SCN_CNT_UNINITIALIZED: u32 = 0x0000_0080;
const SCN_MEM_EXECUTE: u32 = 0x2000_0000;
const SCN_MEM_READ: u32 = 0x4000_0000;
const SCN_MEM_WRITE: u32 = 0x8000_0000;

// Data directory indices.
const DIR_EXPORT: usize = 0;
const DIR_IMPORT: usize = 1;
const DIR_EXCEPTION: usize = 3;
const DIR_BASERELOC: usize = 5;
const DIR_DEBUG: usize = 6;
const DIR_TLS: usize = 9;
const DIR_LOAD_CONFIG: usize = 10;
const DIR_DELAY_IMPORT: usize = 13;

/// One section header, before names are resolved.
struct SecHdr {
    name: String,
    virtual_size: u32,
    virtual_address: u32,
    raw_size: u32,
    raw_offset: u32,
    characteristics: u32,
}

/// A data directory entry: an address and a size, both relative to the image
/// base.
#[derive(Clone, Copy, Default)]
struct Dir {
    rva: u32,
    size: u32,
}

/// The part of a loaded image a directory walk needs.
///
/// Copied out of the section table rather than borrowed from the [`Object`],
/// because every walk both reads the sections and appends warnings to the
/// object they came from.
#[derive(Debug, Clone, Copy)]
struct Span {
    range: AddrRange,
    file_offset: u64,
    file_size: u64,
    exec: bool,
}

/// A mapped PE image, and the three translations every data directory needs:
/// RVA to file offset, RVA to address, and the file's own absolute addresses to
/// addresses under whatever base the image was actually loaded at.
#[derive(Clone)]
pub struct Image<'a> {
    data: Reader<'a>,
    spans: Vec<Span>,
    base: u64,
    image_base: u64,
    wide: bool,
    arch: Arch,
}

impl<'a> Image<'a> {
    /// A view over an already-loaded object.
    ///
    /// `data` is the file the object came from. Exact for an image loaded where
    /// it asked to be, which is every case the loader does not rebase; a
    /// rebased image needs [`load_windows`], which keeps both bases.
    pub fn of(data: &'a [u8], obj: &Object) -> Image<'a> {
        let base = obj.image_base.get();
        Image::new(
            Reader::new(data, Endian::Little),
            &obj.sections,
            base,
            base,
            obj.bits == Bits::Bits64,
            obj.arch.clone(),
        )
    }

    fn new(
        data: Reader<'a>,
        sections: &[Section],
        base: u64,
        image_base: u64,
        wide: bool,
        arch: Arch,
    ) -> Image<'a> {
        Image {
            data,
            spans: sections
                .iter()
                .filter(|s| !s.range.is_empty())
                .map(|s| Span {
                    range: s.range,
                    file_offset: s.file_offset,
                    file_size: s.file_size,
                    exec: s.exec,
                })
                .collect(),
            base,
            image_base,
            wide,
            arch,
        }
    }

    /// The file, as a bounds-checked cursor.
    pub fn reader(&self) -> Reader<'a> {
        self.data
    }

    /// Bytes in the file.
    pub fn len(&self) -> u64 {
        self.data.len() as u64
    }

    /// True when the file is empty.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// True for PE32+, which is what decides every pointer width below.
    pub fn wide(&self) -> bool {
        self.wide
    }

    /// The machine the image targets.
    pub fn arch(&self) -> &Arch {
        &self.arch
    }

    /// Where an RVA lands once the image is loaded.
    pub fn addr_of(&self, rva: u32) -> Addr {
        Addr(self.base.wrapping_add(rva as u64))
    }

    /// An absolute address the file stores, moved to wherever the image was
    /// actually loaded. PE writes these relative to the base it declares, so an
    /// image loaded somewhere else needs the difference applied. `None` for
    /// zero, which every one of these fields uses to mean absent, and for a
    /// value below the declared base, which cannot be inside the image.
    pub fn addr_of_va(&self, va: u64) -> Option<Addr> {
        if va == 0 || va < self.image_base {
            return None;
        }
        Some(Addr(self.base.wrapping_add(va - self.image_base)))
    }

    /// File offset holding the bytes an RVA names, when a section maps it and
    /// those bytes are actually in the file.
    pub fn offset_of(&self, rva: u32) -> Option<u64> {
        self.offset_of_addr(self.addr_of(rva))
    }

    /// The same translation from an address rather than an RVA.
    pub fn offset_of_addr(&self, addr: Addr) -> Option<u64> {
        let s = self.span_at(addr)?;
        let delta = addr.get() - s.range.start().get();
        // A `.bss`-like section is mapped but has no bytes behind it.
        if delta >= s.file_size {
            return None;
        }
        let off = s.file_offset.checked_add(delta)?;
        (off < self.len()).then_some(off)
    }

    /// Bytes between a file offset and the end of the section's raw data, which
    /// is the bound a table with no count has to stop at.
    pub fn section_bytes_after(&self, offset: u64) -> Option<u64> {
        let s = self.spans.iter().find(|s| {
            offset >= s.file_offset && offset < s.file_offset.saturating_add(s.file_size)
        })?;
        Some((s.file_offset + s.file_size).saturating_sub(offset))
    }

    /// True when the address is inside a section the file marks executable.
    pub fn is_code(&self, addr: Addr) -> bool {
        self.span_at(addr).is_some_and(|s| s.exec)
    }

    /// True when any section maps the address at all.
    pub fn is_mapped(&self, addr: Addr) -> bool {
        self.span_at(addr).is_some()
    }

    fn span_at(&self, addr: Addr) -> Option<&Span> {
        self.spans.iter().find(|s| s.range.contains(addr))
    }
}

/// What the Windows-specific data directories said.
///
/// Everything here is also reflected in the [`Object`]: starts became function
/// hints, problems became warnings, counts became metadata. This is the full
/// structure, for a caller that wants the frame layout or the relocation map
/// rather than the summary.
#[derive(Debug, Clone, Default)]
pub struct WindowsInfo {
    /// The TLS directory and its callback array.
    pub tls: Option<windirs::TlsDirectory>,
    /// The exception directory, the unwind records and the scope tables.
    pub exceptions: pdata::Exceptions,
    /// Every base relocation, which is every absolute address in the image.
    pub relocations: Vec<windirs::BaseReloc>,
    /// The load config, including the guard tables.
    pub load_config: Option<windirs::LoadConfig>,
}

/// True when the buffer looks like a PE image or a COFF object.
pub fn is_pe(data: &[u8]) -> bool {
    if data.len() >= 2 && data[..2] == DOS_MAGIC {
        return true;
    }
    // A COFF object begins with a machine number we recognize followed by a
    // plausible section count. Nothing else identifies one.
    if data.len() >= 20 {
        let machine = u16::from_le_bytes([data[0], data[1]]);
        let sections = u16::from_le_bytes([data[2], data[3]]);
        return matches!(
            machine,
            IMAGE_FILE_MACHINE_I386
                | IMAGE_FILE_MACHINE_AMD64
                | IMAGE_FILE_MACHINE_ARM
                | IMAGE_FILE_MACHINE_ARMNT
                | IMAGE_FILE_MACHINE_ARM64
        ) && sections > 0
            && sections < 4096;
    }
    false
}

/// Parse a PE image or a COFF object.
pub fn load(data: &[u8], opts: &LoadOptions) -> Result<Object> {
    load_windows(data, opts).map(|(obj, _)| obj)
}

/// Parse a PE image and keep the Windows-specific directories in full.
///
/// [`load`] is this with the second half dropped. A caller that wants the frame
/// layout of a function, the address of every relocation, or the guard tables
/// calls this instead; nothing else differs, and neither does the [`Object`].
pub fn load_windows(data: &[u8], opts: &LoadOptions) -> Result<(Object, WindowsInfo)> {
    if !is_pe(data) {
        return Err(Error::NotRecognized {
            expected: "PE or COFF",
        });
    }
    let caps = &opts.caps;
    let mut warnings = Vec::new();
    let r = Reader::new(data, Endian::Little);

    // A linked image has a DOS stub; an object file starts at the COFF header.
    let coff_at = if data[..2] == DOS_MAGIC {
        let mut d = r;
        d.seek("e_lfanew", 0x3c)?;
        let at = d.u32("e_lfanew")? as u64;
        let sig = r.bytes_at("PE signature", at, 4)?;
        if sig != PE_MAGIC {
            return Err(Error::BadField {
                field: "PE signature",
                value: u32::from_le_bytes([sig[0], sig[1], sig[2], sig[3]]) as u64,
                reason: "is not \"PE\\0\\0\", so e_lfanew does not point at a PE header",
            });
        }
        at + 4
    } else {
        0
    };
    let is_image = coff_at != 0;

    let mut h = r;
    h.seek("COFF header", coff_at)?;
    let machine = h.u16("Machine")?;
    let n_sections = h.u16("NumberOfSections")?;
    let _timestamp = h.u32("TimeDateStamp")?;
    let sym_table = h.u32("PointerToSymbolTable")?;
    let n_symbols = h.u32("NumberOfSymbols")?;
    let opt_size = h.u16("SizeOfOptionalHeader")?;
    let characteristics = h.u16("Characteristics")?;

    caps.check("sections", n_sections as u64, caps.sections)?;

    // The optional header, which a linked image always has.
    let mut image_base = 0u64;
    let mut entry_rva = 0u32;
    let mut wide = machine == IMAGE_FILE_MACHINE_AMD64 || machine == IMAGE_FILE_MACHINE_ARM64;
    let mut dirs = [Dir::default(); 16];
    let mut subsystem = 0u16;
    let mut dll_characteristics = 0u16;

    if opt_size > 0 {
        let opt_at = coff_at + 20;
        let mut o = r;
        o.seek("optional header", opt_at)?;
        let magic = o.u16("Magic")?;
        wide = match magic {
            0x10b => false,
            0x20b => true,
            other => {
                return Err(Error::BadField {
                    field: "optional header Magic",
                    value: other as u64,
                    reason: "is neither PE32 (0x10b) nor PE32+ (0x20b)",
                });
            }
        };
        // Two linker version bytes and three sizes sit between Magic and the
        // entry point.
        o.skip("linker version and sizes", 14)?;
        entry_rva = o.u32("AddressOfEntryPoint")?;
        o.u32("BaseOfCode")?;
        if !wide {
            o.u32("BaseOfData")?;
        }
        image_base = o.uword("ImageBase", wide)?;
        // Alignments, six version fields, Win32VersionValue, SizeOfImage,
        // SizeOfHeaders and CheckSum sit between ImageBase and Subsystem.
        o.skip("alignments, versions and sizes", 36)?;
        subsystem = o.u16("Subsystem")?;
        dll_characteristics = o.u16("DllCharacteristics")?;
        // Four stack and heap sizes, then LoaderFlags and the directory count.
        o.skip(
            "stack and heap reserve and commit",
            if wide { 32 } else { 16 },
        )?;
        o.u32("LoaderFlags")?;
        let n_dirs = o.u32("NumberOfRvaAndSizes")?.min(16);
        for d in dirs.iter_mut().take(n_dirs as usize) {
            d.rva = o.u32("directory RVA")?;
            d.size = o.u32("directory size")?;
        }
    }

    let bits = if wide { Bits::Bits64 } else { Bits::Bits32 };
    let arch = machine_to_arch(machine);

    // Section headers follow the optional header.
    let sec_at = coff_at + 20 + opt_size as u64;
    let mut shdrs = Vec::with_capacity(n_sections as usize);
    for i in 0..n_sections as u64 {
        let mut s = match r.slice_at("section header", sec_at + i * 40, 40) {
            Ok(s) => s,
            Err(e) => {
                warnings.push(format!("section header {i}: {e}"));
                break;
            }
        };
        let raw_name = s.bytes("section name", 8)?;
        let name = section_name(raw_name, &r, sym_table, n_symbols, caps);
        shdrs.push(SecHdr {
            name,
            virtual_size: s.u32("VirtualSize")?,
            virtual_address: s.u32("VirtualAddress")?,
            raw_size: s.u32("SizeOfRawData")?,
            raw_offset: s.u32("PointerToRawData")?,
            characteristics: {
                s.skip("relocation and line number fields", 12)?;
                s.u32("Characteristics")?
            },
        });
    }

    // An object file has no image base; lay its sections out so it can be
    // analyzed, the way a relocatable ELF is laid out.
    let base = opts
        .base
        .map(|b| b.get())
        .unwrap_or(if is_image { image_base } else { 0x14_0000 });

    let mut memory = MemoryMap::new();
    let mut sections = Vec::with_capacity(shdrs.len());
    let mut next_free = base;
    for sh in &shdrs {
        let va = if is_image {
            base.wrapping_add(sh.virtual_address as u64)
        } else {
            // Objects put every section at RVA zero.
            let at = next_free.next_multiple_of(16);
            next_free = at + sh.virtual_size.max(sh.raw_size) as u64;
            at
        };
        let mem_size = if sh.virtual_size == 0 {
            sh.raw_size as u64
        } else {
            sh.virtual_size as u64
        };
        let Some(range) = AddrRange::sized(Addr(va), mem_size) else {
            warnings.push(format!(
                "section {} does not fit the address space",
                sh.name
            ));
            continue;
        };
        let perms = Perms::new(
            sh.characteristics & SCN_MEM_READ != 0 || !is_image,
            sh.characteristics & SCN_MEM_WRITE != 0,
            sh.characteristics & (SCN_MEM_EXECUTE | SCN_CNT_CODE) != 0,
        );
        let file_size = if sh.characteristics & SCN_CNT_UNINITIALIZED != 0 {
            0
        } else {
            (sh.raw_size as u64).min(mem_size)
        };
        let body = match r.bytes_at("section body", sh.raw_offset as u64, file_size) {
            Ok(b) => b.to_vec(),
            Err(e) => {
                warnings.push(format!("section {}: {e}", sh.name));
                Vec::new()
            }
        };
        if !range.is_empty() {
            memory.add(Segment::new(
                range,
                perms,
                sh.name.clone(),
                sh.raw_offset as u64,
                body,
            )?);
        }
        sections.push(Section {
            name: sh.name.clone(),
            range,
            file_offset: sh.raw_offset as u64,
            file_size,
            exec: perms.exec,
            write: perms.write,
            kind: sh.characteristics,
        });
    }

    let mut obj = Object {
        debug: None,
        format: Format::Pe,
        arch,
        endian: Endian::Little,
        bits,
        entry: (is_image && entry_rva != 0).then(|| Addr(base.wrapping_add(entry_rva as u64))),
        image_base: Addr(base),
        // A DLL and a PIE-equivalent executable both relocate.
        pic: dll_characteristics & 0x0040 != 0 || characteristics & 0x2000 != 0,
        memory,
        sections,
        symbols: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        function_hints: Vec::new(),
        metadata: BTreeMap::new(),
        warnings,
    };

    obj.metadata.insert(
        "pe.kind".into(),
        if is_image {
            if characteristics & 0x2000 != 0 {
                "dll".into()
            } else {
                "executable".into()
            }
        } else {
            "object".into()
        },
    );
    obj.metadata
        .insert("pe.machine".into(), format!("{machine:#x}"));
    if is_image {
        obj.metadata
            .insert("pe.subsystem".into(), subsystem_name(subsystem).into());
        if dll_characteristics & 0x0100 != 0 {
            obj.metadata.insert("pe.nx".into(), "true".into());
        }
        if dll_characteristics & 0x0040 != 0 {
            obj.metadata.insert("pe.aslr".into(), "true".into());
        }
        if dll_characteristics & 0x4000 != 0 {
            obj.metadata.insert("pe.cfg".into(), "true".into());
        }
    }

    read_symbols(&r, sym_table, n_symbols, is_image, base, &mut obj, caps);
    let mut win = WindowsInfo::default();
    if is_image {
        read_imports(&r, &dirs[DIR_IMPORT], base, wide, &mut obj, caps, false);
        read_imports(
            &r,
            &dirs[DIR_DELAY_IMPORT],
            base,
            wide,
            &mut obj,
            caps,
            true,
        );
        read_exports(&r, &dirs[DIR_EXPORT], base, &mut obj, caps);
        read_debug(&r, &dirs[DIR_DEBUG], base, &mut obj, caps);

        let img = Image::new(r, &obj.sections, base, image_base, wide, obj.arch.clone());
        win.exceptions = pdata::read(
            &img,
            dirs[DIR_EXCEPTION].rva,
            dirs[DIR_EXCEPTION].size,
            caps,
            &mut obj,
        );
        win.tls = windirs::read_tls(&img, dirs[DIR_TLS].rva, dirs[DIR_TLS].size, caps, &mut obj);
        win.relocations = windirs::read_relocations(
            &img,
            dirs[DIR_BASERELOC].rva,
            dirs[DIR_BASERELOC].size,
            caps,
            &mut obj,
        );
        win.load_config = windirs::read_load_config(
            &img,
            dirs[DIR_LOAD_CONFIG].rva,
            dirs[DIR_LOAD_CONFIG].size,
            caps,
            &mut obj,
        );
        record_windows_metadata(&win, &mut obj);
    }

    if let Some(entry) = obj.entry {
        obj.function_hints.push(FunctionHint {
            addr: entry,
            size: None,
            name: Some("entry".into()),
            provenance: Provenance::new(Evidence::EntryPoint),
        });
    }

    obj.normalize_symbols();
    obj.normalize_hints();
    Ok((obj, win))
}

/// Summarize the Windows directories into the metadata map, so a report that
/// never looks at [`WindowsInfo`] still says what was there.
fn record_windows_metadata(win: &WindowsInfo, obj: &mut Object) {
    if !win.exceptions.functions.is_empty() {
        obj.metadata.insert(
            "pe.runtime_functions".into(),
            win.exceptions.functions.len().to_string(),
        );
        let scopes: usize = win.exceptions.unwind.iter().map(|u| u.scopes.len()).sum();
        if scopes != 0 {
            obj.metadata
                .insert("pe.seh_scopes".into(), scopes.to_string());
        }
    }
    if let Some(tls) = &win.tls {
        obj.metadata.insert("pe.tls".into(), "present".into());
        obj.metadata
            .insert("pe.tls_callbacks".into(), tls.callbacks.len().to_string());
    }
    if !win.relocations.is_empty() {
        obj.metadata
            .insert("pe.relocations".into(), win.relocations.len().to_string());
    }
    if let Some(cfg) = &win.load_config {
        obj.metadata
            .insert("pe.load_config".into(), cfg.size.to_string());
        if !cfg.guard_functions.is_empty() {
            obj.metadata.insert(
                "pe.guard_functions".into(),
                cfg.guard_functions.len().to_string(),
            );
        }
        if !cfg.se_handlers.is_empty() {
            obj.metadata.insert(
                "pe.safeseh_handlers".into(),
                cfg.se_handlers.len().to_string(),
            );
        }
    }
}

fn machine_to_arch(m: u16) -> Arch {
    match m {
        IMAGE_FILE_MACHINE_I386 => Arch::X86,
        IMAGE_FILE_MACHINE_AMD64 => Arch::X86_64,
        IMAGE_FILE_MACHINE_ARM | IMAGE_FILE_MACHINE_ARMNT => Arch::Arm,
        IMAGE_FILE_MACHINE_ARM64 => Arch::AArch64,
        other => Arch::Unknown(other as u32),
    }
}

fn subsystem_name(s: u16) -> &'static str {
    match s {
        1 => "native",
        2 => "windows gui",
        3 => "windows console",
        9 => "windows ce",
        10 => "efi application",
        _ => "unknown",
    }
}

/// A section name, following the `/N` escape into the string table that long
/// names in object files use.
fn section_name(raw: &[u8], r: &Reader<'_>, sym_table: u32, n_symbols: u32, caps: &Caps) -> String {
    let trimmed: Vec<u8> = raw.iter().copied().take_while(|b| *b != 0).collect();
    if trimmed.first() == Some(&b'/') {
        if let Ok(off) = String::from_utf8_lossy(&trimmed[1..]).trim().parse::<u64>() {
            let strings = sym_table as u64 + n_symbols as u64 * 18;
            if let Ok(name) = r.cstr_at("long section name", strings + off, caps.string_len) {
                return String::from_utf8_lossy(name).into_owned();
            }
        }
    }
    String::from_utf8_lossy(&trimmed).into_owned()
}

/// The COFF symbol table, which object files carry and linked images rarely do.
fn read_symbols(
    r: &Reader<'_>,
    sym_table: u32,
    n_symbols: u32,
    is_image: bool,
    base: u64,
    obj: &mut Object,
    caps: &Caps,
) {
    if sym_table == 0 || n_symbols == 0 {
        return;
    }
    if caps
        .check("symbols", n_symbols as u64, caps.symbols)
        .is_err()
    {
        obj.warnings
            .push(format!("{n_symbols} symbols exceeds the cap; skipped"));
        return;
    }
    let strings = sym_table as u64 + n_symbols as u64 * 18;

    let mut i = 0u32;
    while i < n_symbols {
        let at = sym_table as u64 + i as u64 * 18;
        let Ok(mut s) = r.slice_at("symbol", at, 18) else {
            break;
        };
        let Ok(name_field) = s.bytes("symbol name", 8) else {
            break;
        };
        // A name of eight bytes or fewer is inline; anything longer is a zero
        // word followed by an offset into the string table.
        let name = if name_field[..4] == [0, 0, 0, 0] {
            let off =
                u32::from_le_bytes([name_field[4], name_field[5], name_field[6], name_field[7]]);
            r.cstr_at("symbol name", strings + off as u64, caps.string_len)
                .map(|b| String::from_utf8_lossy(b).into_owned())
                .unwrap_or_default()
        } else {
            String::from_utf8_lossy(
                &name_field
                    .iter()
                    .copied()
                    .take_while(|b| *b != 0)
                    .collect::<Vec<_>>(),
            )
            .into_owned()
        };
        let (Ok(value), Ok(section), Ok(kind), Ok(class), Ok(aux)) = (
            s.u32("Value"),
            s.i16("SectionNumber"),
            s.u16("Type"),
            s.u8("StorageClass"),
            s.u8("NumberOfAuxSymbols"),
        ) else {
            break;
        };
        i += 1 + aux as u32;

        if name.is_empty() {
            continue;
        }
        // Section numbers are one-based; zero means undefined.
        let undefined = section <= 0;
        let addr = if undefined {
            Addr::ZERO
        } else if is_image {
            Addr(base.wrapping_add(value as u64))
        } else {
            match obj.sections.get(section as usize - 1) {
                Some(sec) => Addr(sec.range.start().get().wrapping_add(value as u64)),
                None => Addr::ZERO,
            }
        };
        // Type 0x20 is a function; storage class 2 is external, 3 is static.
        let is_function = kind == 0x20;
        let sym_kind = match (undefined, is_function) {
            (true, _) => SymbolKind::Undefined,
            (_, true) => SymbolKind::Function,
            _ => SymbolKind::Object,
        };
        let binding = match class {
            2 => Binding::Global,
            3 => Binding::Local,
            105 => Binding::Weak,
            _ => Binding::Local,
        };

        if undefined {
            obj.imports.push(Import {
                name: name.clone(),
                library: None,
                thunk: None,
            });
        } else if is_function && addr != Addr::ZERO {
            obj.function_hints.push(FunctionHint {
                addr,
                size: None,
                name: Some(name.clone()),
                provenance: Provenance::new(Evidence::SymbolTable),
            });
        }

        obj.symbols.push(Symbol {
            name,
            addr,
            size: 0,
            kind: sym_kind,
            binding,
            dynamic: false,
        });
    }
}

/// Read an RVA-addressed structure out of the mapped image.
fn at_rva(r: &Reader<'_>, obj: &Object, base: u64, rva: u32) -> Option<u64> {
    // Directories are addressed by RVA but stored at a file offset, so the
    // section containing the RVA gives the translation.
    let va = base.wrapping_add(rva as u64);
    let sec = obj.sections.iter().find(|s| s.range.contains(Addr(va)))?;
    let delta = va - sec.range.start().get();
    let off = sec.file_offset + delta;
    (off < r.len() as u64).then_some(off)
}

/// The import directory, and the delay-import directory, which has the same
/// shape with two extra fields in front.
fn read_imports(
    r: &Reader<'_>,
    dir: &Dir,
    base: u64,
    wide: bool,
    obj: &mut Object,
    caps: &Caps,
    delay: bool,
) {
    if dir.rva == 0 || dir.size == 0 {
        return;
    }
    let Some(mut at) = at_rva(r, obj, base, dir.rva) else {
        obj.warnings
            .push("import directory RVA is not inside any section".into());
        return;
    };
    let step = if delay { 32 } else { 20 };
    let thunk_size = if wide { 8 } else { 4 };

    for _ in 0..(dir.size as u64 / step).max(1).min(caps.sections) {
        let Ok(mut d) = r.slice_at("import descriptor", at, step) else {
            break;
        };
        // Delay descriptors begin with Attributes, then the name RVA.
        if delay {
            let _ = d.u32("Attributes");
        }
        let (name_rva, first_thunk, original_thunk) = if delay {
            let name = d.u32("DllNameRVA").unwrap_or(0);
            let _module = d.u32("ModuleHandleRVA");
            let iat = d.u32("ImportAddressTableRVA").unwrap_or(0);
            let int = d.u32("ImportNameTableRVA").unwrap_or(0);
            (name, iat, int)
        } else {
            let original = d.u32("OriginalFirstThunk").unwrap_or(0);
            let _stamp = d.u32("TimeDateStamp");
            let _forwarder = d.u32("ForwarderChain");
            let name = d.u32("NameRVA").unwrap_or(0);
            let first = d.u32("FirstThunk").unwrap_or(0);
            (name, first, original)
        };
        at += step;
        if name_rva == 0 && first_thunk == 0 {
            break;
        }

        let library = at_rva(r, obj, base, name_rva)
            .and_then(|o| r.cstr_at("dll name", o, caps.string_len).ok())
            .map(|b| String::from_utf8_lossy(b).into_owned());

        // The name table holds the names; the address table holds the slots
        // the program calls through. Either may be absent.
        let names_rva = if original_thunk != 0 {
            original_thunk
        } else {
            first_thunk
        };
        let Some(mut names_at) = at_rva(r, obj, base, names_rva) else {
            continue;
        };

        for n in 0..caps.symbols {
            let Ok(mut t) = r.slice_at("thunk", names_at, thunk_size) else {
                break;
            };
            let Ok(value) = t.uword("thunk", wide) else {
                break;
            };
            names_at += thunk_size;
            if value == 0 {
                break;
            }
            let ordinal_flag = if wide { 1u64 << 63 } else { 1u64 << 31 };
            let name = if value & ordinal_flag != 0 {
                format!("ordinal_{}", value & 0xffff)
            } else {
                // The hint/name table entry is a two-byte hint then the name.
                match at_rva(r, obj, base, value as u32)
                    .and_then(|o| r.cstr_at("import name", o + 2, caps.string_len).ok())
                {
                    Some(b) => String::from_utf8_lossy(b).into_owned(),
                    None => continue,
                }
            };
            // The slot the call goes through, which is what makes an indirect
            // call print a name.
            let thunk = (first_thunk != 0)
                .then(|| Addr(base.wrapping_add(first_thunk as u64 + n * thunk_size)));
            obj.imports.push(Import {
                name,
                library: library.clone(),
                thunk,
            });
        }
    }
}

fn read_exports(r: &Reader<'_>, dir: &Dir, base: u64, obj: &mut Object, caps: &Caps) {
    if dir.rva == 0 {
        return;
    }
    let Some(at) = at_rva(r, obj, base, dir.rva) else {
        return;
    };
    let Ok(mut d) = r.slice_at("export directory", at, 40) else {
        return;
    };
    let _ = d.skip("flags, stamp, versions", 12);
    let name_rva = d.u32("NameRVA").unwrap_or(0);
    let ordinal_base = d.u32("OrdinalBase").unwrap_or(1);
    let n_functions = d.u32("NumberOfFunctions").unwrap_or(0);
    let n_names = d.u32("NumberOfNames").unwrap_or(0);
    let functions_rva = d.u32("AddressTableRVA").unwrap_or(0);
    let names_rva = d.u32("NamePointerRVA").unwrap_or(0);
    let ordinals_rva = d.u32("OrdinalTableRVA").unwrap_or(0);

    if let Some(name) = at_rva(r, obj, base, name_rva)
        .and_then(|o| r.cstr_at("module name", o, caps.string_len).ok())
    {
        obj.metadata.insert(
            "pe.export_name".into(),
            String::from_utf8_lossy(name).into_owned(),
        );
    }

    if caps.check("exports", n_names as u64, caps.symbols).is_err() {
        return;
    }
    let (Some(names_at), Some(ordinals_at), Some(functions_at)) = (
        at_rva(r, obj, base, names_rva),
        at_rva(r, obj, base, ordinals_rva),
        at_rva(r, obj, base, functions_rva),
    ) else {
        return;
    };

    for i in 0..n_names as u64 {
        let Ok(mut np) = r.slice_at("export name pointer", names_at + i * 4, 4) else {
            break;
        };
        let Ok(name_rva) = np.u32("name RVA") else {
            break;
        };
        let Ok(mut op) = r.slice_at("export ordinal", ordinals_at + i * 2, 2) else {
            break;
        };
        let Ok(ordinal) = op.u16("ordinal") else {
            break;
        };
        if ordinal as u32 >= n_functions {
            continue;
        }
        let Ok(mut fp) = r.slice_at("export address", functions_at + ordinal as u64 * 4, 4) else {
            break;
        };
        let Ok(func_rva) = fp.u32("function RVA") else {
            break;
        };
        let Some(name) = at_rva(r, obj, base, name_rva)
            .and_then(|o| r.cstr_at("export name", o, caps.string_len).ok())
            .map(|b| String::from_utf8_lossy(b).into_owned())
        else {
            continue;
        };
        if func_rva == 0 {
            continue;
        }
        let addr = Addr(base.wrapping_add(func_rva as u64));
        obj.exports.push(Export {
            name: name.clone(),
            addr,
            ordinal: Some(ordinal as u32 + ordinal_base),
        });
        if obj.memory.is_executable(addr) {
            obj.function_hints.push(FunctionHint {
                addr,
                size: None,
                name: Some(name),
                provenance: Provenance::new(Evidence::Export),
            });
        }
    }
}

/// The debug directory, for the PDB path, which says where the symbols went.
fn read_debug(r: &Reader<'_>, dir: &Dir, base: u64, obj: &mut Object, caps: &Caps) {
    if dir.rva == 0 || dir.size == 0 {
        return;
    }
    let Some(at) = at_rva(r, obj, base, dir.rva) else {
        return;
    };
    for i in 0..(dir.size as u64 / 28).min(64) {
        let Ok(mut e) = r.slice_at("debug directory", at + i * 28, 28) else {
            break;
        };
        let _ = e.skip("characteristics, stamp, versions", 12);
        let (Ok(kind), Ok(size), Ok(_addr), Ok(offset)) = (
            e.u32("Type"),
            e.u32("SizeOfData"),
            e.u32("AddressOfRawData"),
            e.u32("PointerToRawData"),
        ) else {
            break;
        };
        // IMAGE_DEBUG_TYPE_CODEVIEW
        if kind != 2 || size < 24 {
            continue;
        }
        let Ok(cv) = r.slice_at("codeview record", offset as u64, size as u64) else {
            continue;
        };
        // "RSDS" then a GUID, an age, and the path.
        if cv.data().len() < 24 || &cv.data()[..4] != b"RSDS" {
            continue;
        }
        if let Ok(path) = cv.cstr_at("pdb path", 24, caps.string_len) {
            obj.metadata
                .insert("pe.pdb".into(), String::from_utf8_lossy(path).into_owned());
        }
        // The signature and age as well as the path, because a database from
        // the wrong build is worse than none: it is confidently wrong. A
        // caller that fetches one has to check these before believing it.
        if let Some((id, _)) = crate::pdb::codeview_identity(cv.data()) {
            obj.metadata.insert("pe.pdb.key".into(), id.key());
            obj.metadata.insert("pe.pdb.age".into(), id.age.to_string());
        }
    }
    let _ = base;
}
