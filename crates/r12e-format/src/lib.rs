//! Container loaders.
//!
//! Every loader produces the same [`Object`]: a memory map, symbols, and
//! function hints tagged with where they came from. Nothing above this crate
//! learns whether the bytes arrived as an ELF segment, a PE section, or a raw
//! blob with a base address.
//!
//! Loaders are written here rather than delegated to a parsing crate because
//! provenance tagging and behaviour on hostile input are the product.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod archive;
pub mod dwarf;
pub mod ehframe;
pub mod elf;
pub mod macho;
pub mod metadata;
pub mod overlay;
pub mod pdata;
pub mod pdb;
pub mod pe;
pub mod raw;
pub mod windirs;

use std::collections::BTreeMap;

use r12e_core::{Addr, AddrRange, Arch, Bits, Caps, Endian, Error, MemoryMap, Provenance, Result};
use serde::{Deserialize, Serialize};

/// Which container a file turned out to be.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Format {
    /// ELF, any class or byte order.
    Elf,
    /// PE or COFF.
    Pe,
    /// Mach-O, thin or one slice of a fat file.
    MachO,
    /// No container: bytes at a base address the caller chose.
    Raw,
}

impl Format {
    /// The name used in output and JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Format::Elf => "elf",
            Format::Pe => "pe",
            Format::MachO => "macho",
            Format::Raw => "raw",
        }
    }
}

impl std::fmt::Display for Format {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// What a symbol names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SymbolKind {
    /// Code.
    Function,
    /// Data.
    Object,
    /// A section.
    Section,
    /// A source file name.
    File,
    /// A thread-local object.
    Tls,
    /// Declared but not defined here.
    Undefined,
    /// Something else the container names.
    Other,
}

/// How visible a symbol is outside its object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Binding {
    /// Visible only within the object.
    Local,
    /// Visible everywhere.
    Global,
    /// Global, but a strong definition overrides it.
    Weak,
}

/// A name the container attaches to an address.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Symbol {
    /// The name as the file spells it, still mangled.
    pub name: String,
    /// Where it lives. Undefined symbols sit at zero.
    pub addr: Addr,
    /// Declared size, zero when the container does not say.
    pub size: u64,
    /// What it names.
    pub kind: SymbolKind,
    /// How widely it is visible.
    pub binding: Binding,
    /// True when the name came from a dynamic table rather than a static one.
    pub dynamic: bool,
}

impl Symbol {
    /// True when the symbol names code at a real address.
    pub fn is_defined_function(&self) -> bool {
        self.kind == SymbolKind::Function && self.addr != Addr::ZERO
    }
}

/// A named region the container declares.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Section {
    /// Name as the container spells it.
    pub name: String,
    /// Where it is mapped, empty when it is not mapped at all.
    pub range: AddrRange,
    /// Where its bytes are in the file.
    pub file_offset: u64,
    /// How many bytes are in the file, which is zero for `.bss`.
    pub file_size: u64,
    /// True when the container marks it executable.
    pub exec: bool,
    /// True when the container marks it writable.
    pub write: bool,
    /// Container-specific type number, for reporting.
    pub kind: u32,
}

/// A symbol this object needs from somewhere else.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Import {
    /// The symbol name.
    pub name: String,
    /// The library it should come from, when the container says.
    pub library: Option<String>,
    /// The address of the thunk or slot that reaches it, when known. This is
    /// what makes an indirect call print a name.
    pub thunk: Option<Addr>,
}

/// A symbol this object offers to others.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Export {
    /// The symbol name.
    pub name: String,
    /// Where it points.
    pub addr: Addr,
    /// Ordinal, for containers that have them.
    pub ordinal: Option<u32>,
}

/// An address analysis should treat as a function entry, and why.
///
/// Loaders emit these instead of a bare address list so the strongest evidence
/// can win and disagreements stay visible.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionHint {
    /// Where the function starts.
    pub addr: Addr,
    /// Its size, when the source of the hint knew one.
    pub size: Option<u64>,
    /// Name from the same source, when there was one.
    pub name: Option<String>,
    /// What said so.
    pub provenance: Provenance,
}

/// A loaded container.
#[derive(Debug, Clone)]
pub struct Object {
    /// Which container it was.
    pub format: Format,
    /// Machine it targets.
    pub arch: Arch,
    /// Byte order.
    pub endian: Endian,
    /// Pointer width.
    pub bits: Bits,
    /// Declared entry point, absent for objects and libraries that have none.
    pub entry: Option<Addr>,
    /// Address the container prefers to be loaded at.
    pub image_base: Addr,
    /// True when the image is position independent, so addresses are offsets.
    pub pic: bool,
    /// The bytes, by address.
    pub memory: MemoryMap,
    /// Declared sections, in container order.
    pub sections: Vec<Section>,
    /// Every symbol, sorted by address then name.
    pub symbols: Vec<Symbol>,
    /// Symbols needed from elsewhere.
    pub imports: Vec<Import>,
    /// Symbols offered to others.
    pub exports: Vec<Export>,
    /// Function entries with their evidence, strongest first.
    pub function_hints: Vec<FunctionHint>,
    /// Things worth reporting that do not fit elsewhere: build id, interpreter,
    /// needed libraries, compiler notes.
    pub metadata: BTreeMap<String, String>,
    /// What DWARF said, when the file carried it.
    pub debug: Option<crate::dwarf::DebugInfo>,
    /// Problems found while loading that did not stop the load. A hostile file
    /// is still worth analyzing, and the complaints belong in the report.
    pub warnings: Vec<String>,
}

impl Object {
    /// Symbol covering `addr`, preferring the closest start at or below it.
    pub fn symbol_at(&self, addr: Addr) -> Option<&Symbol> {
        let i = self.symbols.partition_point(|s| s.addr <= addr);
        self.symbols[..i]
            .iter()
            .rev()
            .find(|s| s.addr <= addr && (s.size == 0 || addr.get() < s.addr.get() + s.size))
    }

    /// Section containing `addr`.
    pub fn section_at(&self, addr: Addr) -> Option<&Section> {
        self.sections
            .iter()
            .find(|s| !s.range.is_empty() && s.range.contains(addr))
    }

    /// Section by name.
    pub fn section(&self, name: &str) -> Option<&Section> {
        self.sections.iter().find(|s| s.name == name)
    }

    /// Merge hints for the same address and sort strongest first, then by
    /// address. Deterministic regardless of the order loaders emitted them.
    pub fn normalize_hints(&mut self) {
        self.function_hints.sort_by_key(|h| h.addr);
        let mut out: Vec<FunctionHint> = Vec::with_capacity(self.function_hints.len());
        for h in self.function_hints.drain(..) {
            match out.last_mut() {
                Some(prev) if prev.addr == h.addr => {
                    prev.provenance.merge(&h.provenance);
                    if prev.size.is_none() {
                        prev.size = h.size;
                    }
                    if prev.name.is_none() {
                        prev.name = h.name;
                    }
                }
                _ => out.push(h),
            }
        }
        out.sort_by(|a, b| a.provenance.rank(&b.provenance).then(a.addr.cmp(&b.addr)));
        self.function_hints = out;
    }

    /// Sort symbols by address, then name, so output does not depend on the
    /// order the tables were walked.
    pub fn normalize_symbols(&mut self) {
        self.symbols
            .sort_by(|a, b| a.addr.cmp(&b.addr).then_with(|| a.name.cmp(&b.name)));
        self.symbols.dedup_by(|a, b| {
            a.addr == b.addr && a.name == b.name && a.kind == b.kind && a.dynamic == b.dynamic
        });
    }
}

/// Options a caller can set before loading.
#[derive(Debug, Clone)]
pub struct LoadOptions {
    /// Resource caps.
    pub caps: Caps,
    /// Base address for a raw image, or a rebase for a relocatable one.
    pub base: Option<Addr>,
    /// Architecture for a raw image, which has no header to say.
    pub arch: Option<Arch>,
    /// Read `.eh_frame` for function starts. On by default; it is the best
    /// boundary evidence an ELF offers and costs one pass.
    pub eh_frame: bool,
    /// Read DWARF debug information when it is present. On by default: what
    /// the compiler knew about names and types cannot be recovered any other
    /// way, so it is worth the pass over the sections.
    pub debug_info: bool,
}

impl Default for LoadOptions {
    fn default() -> Self {
        LoadOptions {
            caps: Caps::default(),
            base: None,
            arch: None,
            eh_frame: true,
            debug_info: true,
        }
    }
}

/// Identify and load a file.
///
/// Probing order is by magic, not by extension. A loader that says "not my
/// format" lets the next one try; any other error stops, because a file that
/// announces itself as ELF and then fails is a broken ELF, not a PE.
pub fn load(data: &[u8], opts: &LoadOptions) -> Result<Object> {
    archive::refuse_in_load(data)?;
    match elf::load(data, opts) {
        Err(e) if e.is_not_recognized() => {}
        other => return other,
    }
    match macho::load(data, opts) {
        Err(e) if e.is_not_recognized() => {}
        other => return other,
    }
    match pe::load(data, opts) {
        Err(e) if e.is_not_recognized() => {}
        other => return other,
    }
    if opts.arch.is_some() {
        return raw::load(data, opts);
    }
    Err(Error::NotRecognized {
        expected: "recognized container (ELF, Mach-O or PE); pass an architecture to load it raw",
    })
}
