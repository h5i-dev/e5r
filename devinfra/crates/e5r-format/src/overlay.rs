//! Overlays, entropy and packer evidence.
//!
//! Three questions about a file that the container itself will not answer.
//! What is in the file that no header describes, because an installer, a
//! self-extracting archive and a dropper all append their payload there and
//! the loader never looks. How random is each region, because compressed and
//! encrypted bytes are near maximum entropy and compiled code is not. And what
//! about the shape of the image is unusual enough to be worth an analyst's
//! attention.
//!
//! The last of those is where tools normally lie. "Packed with UPX 3.96" is a
//! conclusion, and a wrong one whenever a legitimate binary happens to compress
//! a resource. So [`evidence`] reports what it saw and how strong the
//! observation is, and names a packer only when a section name is the packer's
//! own signature. The verdict stays the analyst's.
//!
//! Nothing here trusts a declared size. Every region is clipped to the bytes
//! that exist before it is read, and the window count has its own budget,
//! because a file is free to declare sixty-five thousand sections that each
//! claim to cover the whole image.

use e5r_core::{Addr, Endian, Reader, Strength};

use crate::{Format, Object};

/// Window size for the per-section entropy map. A packed region inside an
/// otherwise ordinary section is the thing this exists to show, and four
/// kilobytes is small enough to isolate one and large enough that a byte
/// histogram of it means something.
pub const WINDOW: u64 = 4096;

/// Windows measured across the whole image. Sections are capped at 65,536 by
/// the loaders and each may claim the whole file, so the product needs its own
/// ceiling or the map becomes the analysis.
const MAX_WINDOWS: usize = 1 << 16;

/// Entropy at or above this is what compressed or encrypted bytes score.
/// English text sits near 4.5 and x86 code near 6.
const HIGH_ENTROPY: f64 = 7.2;

/// Fewer imports than this is worth mentioning, but only alongside enough code
/// to need them.
const FEW_IMPORTS: usize = 8;

/// Executable bytes a program has to carry before a short import table says
/// anything. A hello world genuinely imports three symbols.
const CODE_NEEDING_IMPORTS: u64 = 64 * 1024;

/// Section names a normal toolchain emits. Anything else is worth a mention
/// and nothing more: a name is metadata, and metadata is free to lie.
const USUAL_NAMES: &[&str] = &[
    ".text",
    ".data",
    ".rdata",
    ".rodata",
    ".bss",
    ".idata",
    ".edata",
    ".pdata",
    ".xdata",
    ".reloc",
    ".rsrc",
    ".tls",
    ".debug",
    ".comment",
    ".eh_frame",
    ".eh_frame_hdr",
    ".init",
    ".fini",
    ".init_array",
    ".fini_array",
    ".got",
    ".got.plt",
    ".plt",
    ".plt.got",
    ".plt.sec",
    ".dynamic",
    ".dynsym",
    ".dynstr",
    ".symtab",
    ".strtab",
    ".shstrtab",
    ".gnu.hash",
    ".gnu.version",
    ".gnu.version_r",
    ".gnu.version_d",
    ".rela.dyn",
    ".rela.plt",
    ".rel.dyn",
    ".rel.plt",
    ".note.ABI-tag",
    ".note.gnu.build-id",
    ".note.gnu.property",
    ".interp",
    ".data.rel.ro",
    ".tbss",
    ".tdata",
    ".didat",
    ".CRT",
    ".gfids",
    ".00cfg",
    ".textbss",
];

/// Section names that are a named packer's own signature. Matching one of
/// these is the only case where naming a product is a statement of fact rather
/// than a guess, and even then it says the name was found, not that the file
/// was packed by it.
const PACKER_NAMES: &[(&str, &str)] = &[
    ("UPX0", "UPX"),
    ("UPX1", "UPX"),
    ("UPX2", "UPX"),
    ("UPX!", "UPX"),
    (".UPX0", "UPX"),
    (".UPX1", "UPX"),
    (".aspack", "ASPack"),
    (".adata", "ASPack"),
    (".ASPack", "ASPack"),
    (".petite", "Petite"),
    ("FSG!", "FSG"),
    ("MPRESS1", "MPRESS"),
    ("MPRESS2", "MPRESS"),
    (".MPRESS1", "MPRESS"),
    (".nsp0", "NsPack"),
    (".nsp1", "NsPack"),
    ("PEBundle", "PEBundle"),
    ("PEC2", "PECompact"),
    ("pec1", "PECompact"),
    (".pklstb", "PKLite32"),
    (".Themida", "Themida"),
    (".vmp0", "VMProtect"),
    (".vmp1", "VMProtect"),
    (".enigma1", "Enigma"),
    (".boom", "The Boomerang"),
    (".packed", "RLPack"),
    (".RLPack", "RLPack"),
    (".WWP32", "WWPack32"),
    (".winapi", "AHPack"),
    (".yP", "Y0da Protector"),
    (".taz", "PESpin"),
];

/// What the first bytes of an overlay look like. A guess from magic, so it is
/// a label on the bytes and not a claim about what they are for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Content {
    /// Another ELF.
    Elf,
    /// Another PE.
    Pe,
    /// Another Mach-O.
    MachO,
    /// An `ar` archive.
    Archive,
    /// A zip, which is also a jar, an apk and a self-extracting installer.
    Zip,
    /// Gzip.
    Gzip,
    /// Bzip2.
    Bzip2,
    /// XZ.
    Xz,
    /// Zstandard.
    Zstd,
    /// 7-Zip.
    SevenZip,
    /// A Microsoft cabinet, which is what most self-extractors append.
    Cabinet,
    /// RAR.
    Rar,
    /// An Authenticode signature, which the PE certificate directory
    /// describes but which lives past the last section.
    Certificate,
    /// Mostly printable bytes.
    Text,
    /// No magic matched and the bytes are near maximum entropy: compressed or
    /// encrypted, with nothing to say which.
    HighEntropy,
    /// No magic matched and the entropy is unremarkable.
    Unknown,
}

impl Content {
    /// The name used in output and JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Content::Elf => "elf",
            Content::Pe => "pe",
            Content::MachO => "macho",
            Content::Archive => "archive",
            Content::Zip => "zip",
            Content::Gzip => "gzip",
            Content::Bzip2 => "bzip2",
            Content::Xz => "xz",
            Content::Zstd => "zstd",
            Content::SevenZip => "7z",
            Content::Cabinet => "cab",
            Content::Rar => "rar",
            Content::Certificate => "certificate",
            Content::Text => "text",
            Content::HighEntropy => "high-entropy",
            Content::Unknown => "unknown",
        }
    }
}

impl std::fmt::Display for Content {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Bytes in the file that no header accounts for.
#[derive(Debug, Clone, PartialEq)]
pub struct Overlay {
    /// Where it starts: the end of everything the headers describe.
    pub offset: u64,
    /// How many bytes there are.
    pub size: u64,
    /// Shannon entropy of the whole overlay, zero to eight.
    pub entropy: f64,
    /// What the first bytes look like.
    pub content: Content,
}

/// Entropy of one window inside a section.
#[derive(Debug, Clone, PartialEq)]
pub struct Window {
    /// File offset of the window's first byte.
    pub offset: u64,
    /// Bytes in it, which is [`WINDOW`] except for the last one.
    pub size: u64,
    /// Shannon entropy, zero to eight.
    pub entropy: f64,
}

/// Entropy of one section and of each window inside it.
#[derive(Debug, Clone, PartialEq)]
pub struct SectionEntropy {
    /// Section name as the container spells it.
    pub name: String,
    /// Where its bytes are in the file.
    pub file_offset: u64,
    /// How many of them exist, after clipping to the file.
    pub size: u64,
    /// Entropy over the whole section.
    pub entropy: f64,
    /// Entropy per [`WINDOW`] bytes, in file order. Empty when the window
    /// budget ran out, which the report's warnings record.
    pub windows: Vec<Window>,
}

impl SectionEntropy {
    /// The highest-entropy window, which is what a packed region inside an
    /// ordinary-looking section shows up as.
    pub fn peak(&self) -> Option<&Window> {
        self.windows
            .iter()
            .max_by(|a, b| a.entropy.total_cmp(&b.entropy))
    }
}

/// What kind of observation a finding records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A section is both writable and executable.
    WritableExecutable,
    /// A section's file bytes are far fewer than the memory it claims, which
    /// is what a region unpacked at run time looks like.
    RawSmallerThanVirtual,
    /// High entropy in a section marked executable.
    HighEntropyCode,
    /// The entry point is not inside any section that carries code.
    EntryOutsideCode,
    /// The import table names almost nothing, so the real imports are resolved
    /// at run time.
    FewImports,
    /// A section name no ordinary toolchain emits.
    UnusualSectionName,
    /// A section name that is a named packer's signature.
    PackerSectionName,
    /// Bytes past everything the headers describe.
    OverlayPresent,
    /// A section the container declares but whose file bytes do not exist.
    SectionOutsideFile,
}

impl Kind {
    /// The name used in output and JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Kind::WritableExecutable => "writable-executable-section",
            Kind::RawSmallerThanVirtual => "raw-smaller-than-virtual",
            Kind::HighEntropyCode => "high-entropy-code",
            Kind::EntryOutsideCode => "entry-outside-code",
            Kind::FewImports => "few-imports",
            Kind::UnusualSectionName => "unusual-section-name",
            Kind::PackerSectionName => "packer-section-name",
            Kind::OverlayPresent => "overlay",
            Kind::SectionOutsideFile => "section-outside-file",
        }
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One observation about the image, with what was seen and how much it weighs.
#[derive(Debug, Clone, PartialEq)]
pub struct Finding {
    /// What was observed.
    pub kind: Kind,
    /// The section or region it is about, when it is about one.
    pub section: Option<String>,
    /// What was actually seen, in numbers a reader can check against the file.
    pub detail: String,
    /// How much the observation weighs. Nothing here is ever
    /// [`Strength::Proven`] as a statement about packing: the fact is proven,
    /// the packing is not.
    pub strength: Strength,
}

/// Everything this module found about one image.
#[derive(Debug, Clone, Default)]
pub struct Report {
    /// The overlay, when there is one.
    pub overlay: Option<Overlay>,
    /// The end of everything the headers describe, which is where an overlay
    /// would start.
    pub described_end: u64,
    /// Entropy per section.
    pub sections: Vec<SectionEntropy>,
    /// Observations, strongest first.
    pub findings: Vec<Finding>,
    /// What could not be measured, most often a budget running out.
    pub warnings: Vec<String>,
}

impl Report {
    /// Findings at or above a strength, which is how a caller asks for "only
    /// the ones worth waking someone for".
    pub fn at_least(&self, strength: Strength) -> impl Iterator<Item = &Finding> {
        self.findings.iter().filter(move |f| f.strength >= strength)
    }
}

/// Run every measurement over a loaded image and the bytes it came from.
pub fn analyze(obj: &Object, data: &[u8]) -> Report {
    let described_end = described_end(obj, data);
    let overlay = overlay_at(described_end, data);
    let (sections, warnings) = section_entropy(obj, data);
    let findings = evidence(obj, data, &sections, overlay.as_ref());
    Report {
        overlay,
        described_end,
        sections,
        findings,
        warnings,
    }
}

/// Shannon entropy of a byte string, in bits per byte, so zero to eight.
pub fn entropy(bytes: &[u8]) -> f64 {
    if bytes.is_empty() {
        return 0.0;
    }
    let mut counts = [0u32; 256];
    for &b in bytes {
        counts[b as usize] += 1;
    }
    let total = bytes.len() as f64;
    let mut out = 0.0;
    for &c in counts.iter() {
        if c != 0 {
            let p = c as f64 / total;
            out -= p * p.log2();
        }
    }
    out
}

/// Where everything the headers describe ends.
///
/// The loaded [`Object`] carries sections, which is most of the answer, but
/// not the tables that sit outside them: a section header table, an ELF
/// program header, a Mach-O `__LINKEDIT`, a PE certificate. Those are read
/// back out of the raw bytes here, because the alternative is a false overlay
/// on every signed binary and every unstripped ELF.
pub fn described_end(obj: &Object, data: &[u8]) -> u64 {
    let len = data.len() as u64;
    let mut end = 0u64;
    for s in &obj.sections {
        if s.file_size == 0 {
            continue;
        }
        end = end.max(s.file_offset.saturating_add(s.file_size).min(len));
    }
    let tail = match obj.format {
        Format::Elf => elf_tail(data),
        Format::Pe => pe_tail(data),
        Format::MachO => macho_tail(data),
        Format::Raw => len,
    };
    end.max(tail.min(len))
}

/// An overlay is whatever is left after `end`.
fn overlay_at(end: u64, data: &[u8]) -> Option<Overlay> {
    let len = data.len() as u64;
    if end >= len {
        return None;
    }
    let bytes = &data[end as usize..];
    let e = entropy(bytes);
    Some(Overlay {
        offset: end,
        size: len - end,
        entropy: e,
        content: classify(bytes, e),
    })
}

/// Label a run of bytes by magic, falling back to how random it is.
fn classify(bytes: &[u8], entropy: f64) -> Content {
    let starts = |m: &[u8]| bytes.len() >= m.len() && &bytes[..m.len()] == m;
    if starts(b"\x7fELF") {
        return Content::Elf;
    }
    if starts(b"MZ") {
        return Content::Pe;
    }
    if starts(b"\xcf\xfa\xed\xfe") || starts(b"\xce\xfa\xed\xfe") || starts(b"\xca\xfe\xba\xbe") {
        return Content::MachO;
    }
    if starts(b"!<arch>\n") || starts(b"!<thin>\n") {
        return Content::Archive;
    }
    if starts(b"PK\x03\x04") || starts(b"PK\x05\x06") || starts(b"PK\x07\x08") {
        return Content::Zip;
    }
    if starts(b"\x1f\x8b") {
        return Content::Gzip;
    }
    if starts(b"BZh") {
        return Content::Bzip2;
    }
    if starts(b"\xfd7zXZ\x00") {
        return Content::Xz;
    }
    if starts(b"\x28\xb5\x2f\xfd") {
        return Content::Zstd;
    }
    if starts(b"7z\xbc\xaf\x27\x1c") {
        return Content::SevenZip;
    }
    if starts(b"MSCF") {
        return Content::Cabinet;
    }
    if starts(b"Rar!\x1a\x07") {
        return Content::Rar;
    }
    // A WIN_CERTIFICATE is a length, a revision, a type of 0x0002, then DER.
    if bytes.len() >= 10 && bytes[6] == 0x02 && bytes[7] == 0x00 && bytes[8] == 0x30 {
        return Content::Certificate;
    }
    if entropy >= HIGH_ENTROPY {
        return Content::HighEntropy;
    }
    let printable = bytes
        .iter()
        .take(1024)
        .filter(|&&b| (0x20..0x7f).contains(&b) || b == b'\n' || b == b'\r' || b == b'\t')
        .count();
    if printable * 10 >= bytes.len().min(1024) * 9 {
        return Content::Text;
    }
    Content::Unknown
}

/// End of the ELF tables that are not sections: the program header table and
/// the section header table, plus every segment's file extent.
fn elf_tail(data: &[u8]) -> u64 {
    let r = Reader::le(data);
    let Ok(ident) = r.bytes_at("e_ident", 0, 16) else {
        return 0;
    };
    let wide = ident[4] == 2;
    let endian = if ident[5] == 2 {
        Endian::Big
    } else {
        Endian::Little
    };
    let r = Reader::new(data, endian);
    let mut h = r;
    // e_phoff sits after e_ident, e_type, e_machine, e_version and e_entry.
    let at = 16 + 2 + 2 + 4 + if wide { 8 } else { 4 };
    if h.seek("elf header", at).is_err() {
        return 0;
    }
    let (Ok(phoff), Ok(shoff)) = (h.uword("e_phoff", wide), h.uword("e_shoff", wide)) else {
        return 0;
    };
    // e_flags, e_ehsize, then the two header table geometries.
    if h.skip("e_flags", 4 + 2).is_err() {
        return 0;
    }
    let (Ok(phentsize), Ok(phnum), Ok(shentsize), Ok(shnum)) = (
        h.u16("e_phentsize"),
        h.u16("e_phnum"),
        h.u16("e_shentsize"),
        h.u16("e_shnum"),
    ) else {
        return 0;
    };
    let mut end = phoff.saturating_add(phentsize as u64 * phnum as u64);
    end = end.max(shoff.saturating_add(shentsize as u64 * shnum as u64));
    // Segments, because a file with its section headers stripped still has
    // them and they are what the loader actually reads.
    if phentsize as u64 >= if wide { 56 } else { 32 } {
        for i in 0..phnum as u64 {
            let at = phoff.saturating_add(i * phentsize as u64);
            let off_at = if wide { at + 8 } else { at + 4 };
            let mut p = r;
            if p.seek("program header", off_at).is_err() {
                break;
            }
            let Ok(p_offset) = p.uword("p_offset", wide) else {
                break;
            };
            if wide {
                // 64-bit puts p_vaddr and p_paddr between p_offset and p_filesz.
                if p.skip("p_vaddr", 16).is_err() {
                    break;
                }
            } else if p.skip("p_vaddr", 8).is_err() {
                break;
            }
            let Ok(p_filesz) = p.uword("p_filesz", wide) else {
                break;
            };
            end = end.max(p_offset.saturating_add(p_filesz));
        }
    }
    end
}

/// End of everything a PE or COFF header describes.
///
/// Three things live past the last section and would otherwise read as an
/// overlay: the COFF symbol table and its string table, which every `.o` has;
/// a section's relocation table; and the certificate directory, whose address
/// is a file offset rather than an RVA, which is why every signed Windows
/// binary looks like it has an overlay to a tool that forgets it.
fn pe_tail(data: &[u8]) -> u64 {
    let r = Reader::le(data);
    // An image puts the COFF header behind `PE\0\0`; an object starts with it.
    let coff_at = if data.starts_with(b"MZ") {
        let mut h = r;
        if h.seek("e_lfanew", 0x3c).is_err() {
            return 0;
        }
        let Ok(at) = h.u32("e_lfanew") else {
            return 0;
        };
        let mut c = r;
        if c.seek("pe signature", at as u64).is_err() {
            return 0;
        }
        if c.array::<4>("pe signature").ok() != Some(*b"PE\0\0") {
            return 0;
        }
        at as u64 + 4
    } else {
        0
    };

    let mut c = r;
    if c.seek("coff header", coff_at).is_err() {
        return 0;
    }
    if c.skip("machine", 2).is_err() {
        return 0;
    }
    let (Ok(nsections), Ok(_timestamp), Ok(symtab), Ok(nsyms), Ok(opt_size)) = (
        c.u16("number of sections"),
        c.u32("timestamp"),
        c.u32("pointer to symbol table"),
        c.u32("number of symbols"),
        c.u16("size of optional header"),
    ) else {
        return 0;
    };
    let opt_at = coff_at + 20;
    let sections_at = opt_at + opt_size as u64;
    let mut end = sections_at.saturating_add(40 * nsections as u64);

    // The symbol table is 18-byte records followed by a string table whose
    // first four bytes are its own length.
    if symtab != 0 && nsyms != 0 {
        let strings_at = (symtab as u64).saturating_add(18 * nsyms as u64);
        end = end.max(strings_at);
        let mut t = r;
        if t.seek("string table", strings_at).is_ok() {
            if let Ok(n) = t.u32("string table size") {
                end = end.max(strings_at.saturating_add(n as u64));
            }
        }
    }

    // Relocation and line-number tables, which an object keeps behind the
    // section data they belong to.
    for i in 0..nsections as u64 {
        let mut sh = r;
        if sh
            .seek("section header", sections_at + i * 40 + 24)
            .is_err()
        {
            break;
        }
        let (Ok(relocs), Ok(lines), Ok(nrelocs), Ok(nlines)) = (
            sh.u32("pointer to relocations"),
            sh.u32("pointer to line numbers"),
            sh.u16("number of relocations"),
            sh.u16("number of line numbers"),
        ) else {
            break;
        };
        if relocs != 0 {
            end = end.max((relocs as u64).saturating_add(10 * nrelocs as u64));
        }
        if lines != 0 {
            end = end.max((lines as u64).saturating_add(6 * nlines as u64));
        }
    }

    if opt_size == 0 {
        return end;
    }
    let mut o = r;
    if o.seek("optional header", opt_at).is_err() {
        return end;
    }
    let Ok(magic) = o.u16("optional header magic") else {
        return end;
    };
    let wide = magic == 0x20b;
    // SizeOfHeaders sits at the same place in both optional header layouts.
    let mut s = r;
    if s.seek("size of headers", opt_at + 60).is_ok() {
        if let Ok(size_of_headers) = s.u32("size of headers") {
            end = end.max(size_of_headers as u64);
        }
    }
    // Data directory 4 is the certificate table: a file offset and a size.
    let dirs_at = opt_at + if wide { 112 } else { 96 };
    let mut d = r;
    if d.seek("certificate directory", dirs_at + 4 * 8).is_ok() {
        if let (Ok(off), Ok(size)) = (d.u32("certificate offset"), d.u32("certificate size")) {
            if off != 0 {
                end = end.max((off as u64).saturating_add(size as u64));
            }
        }
    }
    end
}

/// End of every Mach-O segment's file extent, which is what covers
/// `__LINKEDIT` and the code signature the loaded sections do not.
fn macho_tail(data: &[u8]) -> u64 {
    let r = Reader::le(data);
    let mut h = r;
    let Ok(magic) = h.u32("mach magic") else {
        return 0;
    };
    // A fat file describes its slices and nothing past them.
    if magic == 0xbebafeca || magic == 0xcafebabe {
        let mut f = Reader::new(data, Endian::Big);
        if f.seek("fat header", 4).is_err() {
            return 0;
        }
        let Ok(n) = f.u32("nfat_arch") else {
            return 0;
        };
        // The count is not trusted for anything but a loop bound that the
        // reader stops anyway; each entry is 20 bytes of the same file.
        let mut end = 8 + 20 * (n as u64).min(data.len() as u64 / 20);
        for i in 0..(n as u64).min(data.len() as u64 / 20) {
            let mut a = Reader::new(data, Endian::Big);
            if a.seek("fat arch", 8 + i * 20 + 8).is_err() {
                break;
            }
            let (Ok(off), Ok(size)) = (a.u32("fat offset"), a.u32("fat size")) else {
                break;
            };
            end = end.max((off as u64).saturating_add(size as u64));
        }
        return end;
    }
    let (wide, endian) = match magic {
        0xfeedface => (false, Endian::Little),
        0xfeedfacf => (true, Endian::Little),
        0xcefaedfe => (false, Endian::Big),
        0xcffaedfe => (true, Endian::Big),
        _ => return 0,
    };
    let r = Reader::new(data, endian);
    let mut c = r;
    if c.seek("mach header", 16).is_err() {
        return 0;
    }
    let Ok(ncmds) = c.u32("ncmds") else {
        return 0;
    };
    let header_len = if wide { 32u64 } else { 28 };
    let mut end = header_len;
    let mut at = header_len;
    // Bounded by the file: every command declares a length and the walk stops
    // the moment one does not move forward.
    for _ in 0..ncmds.min(1 << 16) {
        let mut l = r;
        if l.seek("load command", at).is_err() {
            break;
        }
        let (Ok(cmd), Ok(cmdsize)) = (l.u32("cmd"), l.u32("cmdsize")) else {
            break;
        };
        if cmdsize < 8 {
            break;
        }
        // LC_SEGMENT and LC_SEGMENT_64 put fileoff and filesize after a
        // sixteen-byte name and the two virtual-memory fields.
        if cmd == 0x01 || cmd == 0x19 {
            let seg_wide = cmd == 0x19;
            let at_off = at + 8 + 16 + if seg_wide { 16 } else { 8 };
            let mut s = r;
            if s.seek("segment", at_off).is_ok() {
                if let (Ok(fileoff), Ok(filesize)) =
                    (s.uword("fileoff", seg_wide), s.uword("filesize", seg_wide))
                {
                    end = end.max(fileoff.saturating_add(filesize));
                }
            }
        }
        // LC_CODE_SIGNATURE and friends are a (dataoff, datasize) pair.
        if matches!(cmd, 0x1d | 0x1a | 0x1b | 0x26 | 0x29 | 0x2b | 0x2e | 0x2f) {
            let mut s = r;
            if s.seek("linkedit command", at + 8).is_ok() {
                if let (Ok(off), Ok(size)) = (s.u32("dataoff"), s.u32("datasize")) {
                    end = end.max((off as u64).saturating_add(size as u64));
                }
            }
        }
        // LC_SYMTAB: symbol table offset and string table extent.
        if cmd == 0x02 {
            let mut s = r;
            if s.seek("symtab", at + 8 + 8).is_ok() {
                if let (Ok(stroff), Ok(strsize)) = (s.u32("stroff"), s.u32("strsize")) {
                    end = end.max((stroff as u64).saturating_add(strsize as u64));
                }
            }
        }
        at = at.saturating_add(cmdsize as u64);
        if at >= data.len() as u64 {
            break;
        }
    }
    end
}

/// Entropy of every section, whole and per window.
pub fn section_entropy(obj: &Object, data: &[u8]) -> (Vec<SectionEntropy>, Vec<String>) {
    let len = data.len() as u64;
    let mut out = Vec::with_capacity(obj.sections.len());
    let mut warnings = Vec::new();
    let mut budget = MAX_WINDOWS;
    for s in &obj.sections {
        // The declared extent is clipped to what exists before anything reads
        // it, so a section claiming four gigabytes measures what is there.
        let start = s.file_offset.min(len);
        let end = s.file_offset.saturating_add(s.file_size).min(len);
        let body = &data[start as usize..end as usize];
        let mut windows = Vec::new();
        if !body.is_empty() {
            let want = body.len().div_ceil(WINDOW as usize);
            if want > budget {
                warnings.push(format!(
                    "section {} has {want} windows, past the {MAX_WINDOWS}-window budget; \
                     its map is omitted",
                    s.name
                ));
            } else {
                budget -= want;
                for (i, chunk) in body.chunks(WINDOW as usize).enumerate() {
                    windows.push(Window {
                        offset: start + i as u64 * WINDOW,
                        size: chunk.len() as u64,
                        entropy: entropy(chunk),
                    });
                }
            }
        }
        out.push(SectionEntropy {
            name: s.name.clone(),
            file_offset: start,
            size: body.len() as u64,
            entropy: entropy(body),
            windows,
        });
    }
    (out, warnings)
}

/// Observations about the image, strongest first.
///
/// Every one names what it saw. None of them says the file is packed, because
/// none of them can: a legitimate installer has an overlay, a legitimate
/// binary has a compressed resource, and a writable executable section is a
/// linker script away from ordinary.
pub fn evidence(
    obj: &Object,
    data: &[u8],
    sections: &[SectionEntropy],
    overlay: Option<&Overlay>,
) -> Vec<Finding> {
    let mut out = Vec::new();
    let len = data.len() as u64;

    for s in &obj.sections {
        if s.exec && s.write && !s.range.is_empty() {
            out.push(Finding {
                kind: Kind::WritableExecutable,
                section: Some(s.name.clone()),
                detail: format!(
                    "section {} is mapped writable and executable at {}",
                    s.name, s.range
                ),
                strength: Strength::Inferred,
            });
        }
        let virt = s.range.len();
        if virt > 0 && s.file_size > 0 && virt >= s.file_size.saturating_mul(4) {
            out.push(Finding {
                kind: Kind::RawSmallerThanVirtual,
                section: Some(s.name.clone()),
                detail: format!(
                    "section {} holds {} bytes in the file and claims {virt} in memory",
                    s.name, s.file_size
                ),
                strength: Strength::Inferred,
            });
        }
        if s.file_size > 0 && s.file_offset.saturating_add(s.file_size) > len {
            out.push(Finding {
                kind: Kind::SectionOutsideFile,
                section: Some(s.name.clone()),
                detail: format!(
                    "section {} runs to {:#x}, past the {len:#x} bytes the file has",
                    s.name,
                    s.file_offset.saturating_add(s.file_size)
                ),
                strength: Strength::Proven,
            });
        }
        if let Some((name, packer)) = PACKER_NAMES.iter().find(|(n, _)| *n == s.name) {
            out.push(Finding {
                kind: Kind::PackerSectionName,
                section: Some(s.name.clone()),
                detail: format!("section is named {name}, which is {packer}'s own signature"),
                strength: Strength::Inferred,
            });
        } else if !s.name.is_empty() && !usual_name(&s.name) {
            out.push(Finding {
                kind: Kind::UnusualSectionName,
                section: Some(s.name.clone()),
                detail: format!(
                    "section {} is not a name an ordinary toolchain emits",
                    s.name
                ),
                strength: Strength::Heuristic,
            });
        }
    }

    for (s, e) in obj.sections.iter().zip(sections) {
        if !s.exec || e.size == 0 {
            continue;
        }
        if e.entropy >= HIGH_ENTROPY {
            out.push(Finding {
                kind: Kind::HighEntropyCode,
                section: Some(s.name.clone()),
                detail: format!(
                    "executable section {} scores {:.2} bits per byte over {} bytes",
                    s.name, e.entropy, e.size
                ),
                strength: Strength::Inferred,
            });
        } else if let Some(w) = e.peak() {
            if w.entropy >= HIGH_ENTROPY && w.size == WINDOW {
                out.push(Finding {
                    kind: Kind::HighEntropyCode,
                    section: Some(s.name.clone()),
                    detail: format!(
                        "executable section {} averages {:.2} but its window at {:#x} scores \
                         {:.2}",
                        s.name, e.entropy, w.offset, w.entropy
                    ),
                    strength: Strength::Heuristic,
                });
            }
        }
    }

    if obj.entry.is_some_and(|e| !entry_in_code(obj, e)) {
        let entry = obj.entry.unwrap_or(Addr::ZERO);
        out.push(Finding {
            kind: Kind::EntryOutsideCode,
            section: None,
            detail: match obj.section_at(entry) {
                Some(s) => format!(
                    "entry point {entry} is in section {}, which is not marked executable",
                    s.name
                ),
                None => format!("entry point {entry} is in no declared section"),
            },
            strength: Strength::Inferred,
        });
    }

    // An import table is only evidence when the container has one at all and
    // when there is enough code for it to be too short for: a relocatable
    // object, a static ELF and a hello world are not hiding anything.
    let dynamic = obj.format == Format::Pe || obj.metadata.contains_key("elf.needed");
    let code_bytes: u64 = obj
        .sections
        .iter()
        .filter(|s| s.exec)
        .map(|s| s.file_size.min(len))
        .sum();
    if dynamic && obj.imports.len() < FEW_IMPORTS && code_bytes >= CODE_NEEDING_IMPORTS {
        out.push(Finding {
            kind: Kind::FewImports,
            section: None,
            detail: format!(
                "{code_bytes} bytes of code import only {} symbols, so the rest are \
                 resolved at run time",
                obj.imports.len()
            ),
            strength: Strength::Inferred,
        });
    }

    if let Some(o) = overlay {
        out.push(Finding {
            kind: Kind::OverlayPresent,
            section: None,
            detail: format!(
                "{} bytes at {:#x} that no header describes, looking like {} at {:.2} bits \
                 per byte",
                o.size, o.offset, o.content, o.entropy
            ),
            strength: if o.content == Content::Certificate {
                Strength::Heuristic
            } else {
                Strength::Inferred
            },
        });
    }

    // Strongest first, then a stable order so two runs agree.
    out.sort_by(|a, b| {
        b.strength
            .cmp(&a.strength)
            .then_with(|| a.kind.as_str().cmp(b.kind.as_str()))
            .then_with(|| a.detail.cmp(&b.detail))
    });
    out
}

/// True when a name is one an ordinary toolchain emits, allowing for the
/// suffixes a section can carry: `.text.unlikely`, `.debug_info`, `.rela.text`.
fn usual_name(name: &str) -> bool {
    USUAL_NAMES
        .iter()
        .any(|u| name == *u || (name.starts_with(u) && name.as_bytes().get(u.len()) == Some(&b'.')))
        || name.starts_with(".debug")
        || name.starts_with(".note")
        || name.starts_with(".gnu")
        || name.starts_with(".rel")
        || name.starts_with("__")
        || name.starts_with(".llvm")
        || name.starts_with(".stab")
}

/// True when the entry point lands in a section that carries code.
fn entry_in_code(obj: &Object, entry: Addr) -> bool {
    match obj.section_at(entry) {
        Some(s) => s.exec,
        // No sections at all is a stripped-to-segments ELF, not a finding; the
        // memory map is then the only authority on what is executable.
        None => obj.sections.is_empty() || obj.memory.is_executable(entry),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entropy_ends_are_right() {
        assert_eq!(entropy(&[]), 0.0);
        assert_eq!(entropy(&[7u8; 4096]), 0.0);
        // Every byte value exactly once is exactly eight bits.
        let all: Vec<u8> = (0..=255u8).collect();
        assert!((entropy(&all) - 8.0).abs() < 1e-12, "{}", entropy(&all));
        // Two values evenly split is one bit.
        let half: Vec<u8> = (0..1024).map(|i| (i % 2) as u8).collect();
        assert!((entropy(&half) - 1.0).abs() < 1e-12);
    }

    #[test]
    fn magic_is_recognized_before_entropy() {
        assert_eq!(classify(b"PK\x03\x04rest", 0.5), Content::Zip);
        assert_eq!(classify(b"MSCFrest", 7.9), Content::Cabinet);
        assert_eq!(classify(b"hello world\n", 1.0), Content::Text);
    }

    #[test]
    fn header_readers_survive_nonsense() {
        // The point is that they return, not what they return.
        for n in 0..300 {
            let v = vec![0xffu8; n];
            let _ = elf_tail(&v);
            let _ = pe_tail(&v);
            let _ = macho_tail(&v);
        }
        let mut pe = vec![0u8; 0x400];
        pe[..2].copy_from_slice(b"MZ");
        pe[0x3c..0x40].copy_from_slice(&0xffff_fff0u32.to_le_bytes());
        assert_eq!(pe_tail(&pe), 0);
    }

    #[test]
    fn unusual_names_allow_the_ordinary_suffixes() {
        assert!(usual_name(".text"));
        assert!(usual_name(".text.unlikely"));
        assert!(usual_name(".debug_info"));
        assert!(usual_name(".rela.text"));
        assert!(!usual_name("UPX1"));
        assert!(!usual_name(".mystery"));
    }
}
