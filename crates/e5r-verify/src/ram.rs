//! Export a RAM-resident bare-metal ELF as the initial RAM a loader writes.
//!
//! QEMU `-M virt -bios none -kernel IMAGE.elf` has no flash: its ELF loader
//! copies every `PT_LOAD`'s file bytes into RAM and zero-fills up to `p_memsz`,
//! then starts the hart at `e_entry`. So the export is, per `PT_LOAD`, the exact
//! file bytes at `p_vaddr` and a zero-fill range, never expanded into bytes.
//! The only supported mapping policy is `p_paddr == p_vaddr`; an image that
//! distinguishes the two is refused rather than guessed at.
//!
//! The image says nothing about safety. RAM is writable and executable on that
//! machine, so a model that fetches from these bytes is exact only while no
//! store reaches an executable range; the manifest states that as an
//! assumption for the checker to discharge, it does not establish it.

use crate::sha256;
use e5r_core::{Addr, Arch, Bits, Endian};
use e5r_format::LoadOptions;
use serde_json::{Value, json};
use std::fmt::Write;

pub const SCHEMA: &str = "e5r.ram-image.v1";
/// The one mapping policy implemented: load and run addresses are equal.
pub const MAPPING: &str = "paddr=vaddr";

/// Default and hard ceilings of the explicit size budgets.
pub const DEFAULT_MAX_FILE: u64 = 1 << 20;
pub const CEILING_MAX_FILE: u64 = 16 << 20;
pub const DEFAULT_MAX_FILE_BYTES: u64 = 512 << 10;
pub const CEILING_MAX_FILE_BYTES: u64 = 4 << 20;

const PT_NULL: u32 = 0;
const PT_LOAD: u32 = 1;
const PT_GNU_STACK: u32 = 0x6474_e551;
const PT_RISCV_ATTRIBUTES: u32 = 0x7000_0003;
const EF_RISCV_RVC: u32 = 1;
const PF_X: u32 = 1;
const PF_W: u32 = 2;
const PF_R: u32 = 4;

/// What the image is checked and exported against.
#[derive(Clone, Copy, Debug)]
pub struct Policy {
    pub ram_base: u64,
    pub ram_size: u64,
    /// Largest ELF file accepted.
    pub max_file: u64,
    /// Largest sum of `p_filesz` over all `PT_LOAD`s.
    pub max_file_bytes: u64,
}

impl Policy {
    pub fn new(ram_base: u64, ram_size: u64) -> Policy {
        Policy {
            ram_base,
            ram_size,
            max_file: DEFAULT_MAX_FILE,
            max_file_bytes: DEFAULT_MAX_FILE_BYTES,
        }
    }

    fn check(&self) -> Result<(), String> {
        if self.ram_size == 0
            || self
                .ram_base
                .checked_add(self.ram_size)
                .is_none_or(|e| e > 1 << 32)
        {
            return Err("RAM window must be non-empty and inside the 32-bit address space".into());
        }
        if self.max_file > CEILING_MAX_FILE || self.max_file_bytes > CEILING_MAX_FILE_BYTES {
            return Err(format!(
                "budgets above the ceilings ({CEILING_MAX_FILE} file, \
                 {CEILING_MAX_FILE_BYTES} file-backed bytes)"
            ));
        }
        Ok(())
    }
}

/// One `PT_LOAD`, as found in the program headers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Load {
    /// Index among all program headers.
    pub index: usize,
    pub offset: u64,
    pub vaddr: u64,
    pub paddr: u64,
    pub filesz: u64,
    pub memsz: u64,
    pub align: u64,
    pub flags: u32,
    /// `ELF[offset, offset + filesz)`.
    pub bytes: Vec<u8>,
}

impl Load {
    pub fn read(&self) -> bool {
        self.flags & PF_R != 0
    }
    pub fn write(&self) -> bool {
        self.flags & PF_W != 0
    }
    pub fn exec(&self) -> bool {
        self.flags & PF_X != 0
    }
    /// `[vaddr + filesz, vaddr + memsz)`, if non-empty.
    pub fn zero(&self) -> Option<(u64, u64)> {
        (self.memsz > self.filesz).then(|| (self.vaddr + self.filesz, self.vaddr + self.memsz))
    }
}

/// The initial RAM image of a RAM-resident ELF.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RamImage {
    pub entry: u64,
    pub e_flags: u32,
    /// `Tag_RISCV_arch` from the `PT_RISCV_ATTRIBUTES` segment, if present.
    pub arch: Option<String>,
    pub loads: Vec<Load>,
}

fn u16_at(b: &[u8], off: u64) -> Result<u64, String> {
    let o = usize::try_from(off).map_err(|_| format!("offset {off:#x} too large"))?;
    b.get(o..o.checked_add(2).ok_or("offset overflows")?)
        .map(|s| u16::from_le_bytes([s[0], s[1]]) as u64)
        .ok_or_else(|| format!("truncated at {off:#x}"))
}

fn u32_at(b: &[u8], off: u64) -> Result<u64, String> {
    let o = usize::try_from(off).map_err(|_| format!("offset {off:#x} too large"))?;
    b.get(o..o.checked_add(4).ok_or("offset overflows")?)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]) as u64)
        .ok_or_else(|| format!("truncated at {off:#x}"))
}

fn within(addr: u64, len: u64, base: u64, size: u64) -> bool {
    addr >= base && addr.checked_add(len).is_some_and(|end| end <= base + size)
}

/// Parse and validate. Every refusal names the rule it broke.
pub fn ram_image(bytes: &[u8], p: Policy) -> Result<RamImage, String> {
    p.check()?;
    let len = bytes.len() as u64;
    if len > p.max_file || len < 52 {
        return Err(format!("ELF size must be 52..={} bytes", p.max_file));
    }
    if &bytes[..7] != b"\x7fELF\x01\x01\x01" {
        return Err("not a little-endian ELF32 file (EV_CURRENT)".into());
    }
    if u16_at(bytes, 16)? != 2 || u16_at(bytes, 18)? != 243 || u32_at(bytes, 20)? != 1 {
        return Err("requires an EM_RISCV ET_EXEC (static executable)".into());
    }
    let e_flags = u32_at(bytes, 36)? as u32;
    if e_flags & !EF_RISCV_RVC != 0 {
        return Err(format!(
            "e_flags {e_flags:#x}: only RVC with the soft-float ABI is supported"
        ));
    }
    if u16_at(bytes, 40)? != 52 || u16_at(bytes, 42)? != 32 {
        return Err("unexpected ELF32 header or program header size".into());
    }
    let entry = u32_at(bytes, 24)?;
    let phoff = u32_at(bytes, 28)?;
    let phnum = u16_at(bytes, 44)?;
    if !(1..=16).contains(&phnum) {
        return Err("requires 1..=16 program headers".into());
    }
    if phoff + phnum * 32 > len {
        return Err("program headers outside the file".into());
    }
    let mut loads: Vec<Load> = Vec::new();
    let mut arch = None;
    let mut file_bytes = 0u64;
    for i in 0..phnum {
        let field = |n: u64| u32_at(bytes, phoff + i * 32 + n);
        let kind = field(0)? as u32;
        let (offset, vaddr, paddr) = (field(4)?, field(8)?, field(12)?);
        let (filesz, memsz, flags, align) = (field(16)?, field(20)?, field(24)? as u32, field(28)?);
        let i = i as usize;
        let file_end = offset
            .checked_add(filesz)
            .filter(|&e| e <= len)
            .ok_or_else(|| format!("program header {i}: file bytes outside the file"))?;
        match kind {
            PT_NULL => continue,
            PT_GNU_STACK => {
                if flags & PF_X != 0 {
                    return Err(format!("program header {i}: executable stack"));
                }
                continue;
            }
            PT_RISCV_ATTRIBUTES => {
                if arch.is_some() {
                    return Err("more than one PT_RISCV_ATTRIBUTES".into());
                }
                arch = Some(arch_attribute(&bytes[offset as usize..file_end as usize])?);
                continue;
            }
            PT_LOAD => {}
            other => return Err(format!("program header {i}: unsupported type {other:#x}")),
        }
        if flags & !(PF_R | PF_W | PF_X) != 0 || flags & PF_R == 0 {
            return Err(format!(
                "PT_LOAD {i}: flags {flags:#x} must be readable R/W/X only"
            ));
        }
        if flags & PF_W != 0 && flags & PF_X != 0 {
            return Err(format!("PT_LOAD {i}: writable and executable"));
        }
        if memsz == 0 || filesz > memsz {
            return Err(format!(
                "PT_LOAD {i}: needs 0 < p_memsz and p_filesz <= p_memsz"
            ));
        }
        if paddr != vaddr {
            return Err(format!(
                "PT_LOAD {i}: p_paddr {paddr:#x} != p_vaddr {vaddr:#x}; \
                 only the {MAPPING} mapping policy is supported"
            ));
        }
        if !within(vaddr, memsz, p.ram_base, p.ram_size) {
            return Err(format!(
                "PT_LOAD {i}: [{vaddr:#x}, +{memsz:#x}) is not inside RAM [{:#x}, +{:#x})",
                p.ram_base, p.ram_size
            ));
        }
        if align > 1 && (!align.is_power_of_two() || vaddr % align != offset % align) {
            return Err(format!("PT_LOAD {i}: p_align {align:#x} inconsistent"));
        }
        file_bytes += filesz;
        if file_bytes > p.max_file_bytes {
            return Err(format!(
                "more than {} file-backed bytes (budget)",
                p.max_file_bytes
            ));
        }
        loads.push(Load {
            index: i,
            offset,
            vaddr,
            paddr,
            filesz,
            memsz,
            align,
            flags,
            bytes: bytes[offset as usize..file_end as usize].to_vec(),
        });
    }
    if loads.is_empty() {
        return Err("no PT_LOAD".into());
    }
    // Ascending and disjoint over the whole memory image, zero-fill included:
    // two segments that overlap would make the initial RAM depend on load order.
    for pair in loads.windows(2) {
        if pair[0].vaddr + pair[0].memsz > pair[1].vaddr {
            return Err(format!(
                "PT_LOAD {} and {} overlap or are out of address order",
                pair[0].index, pair[1].index
            ));
        }
    }
    let in_exec = loads
        .iter()
        .any(|l| l.exec() && within(entry, 2, l.vaddr, l.filesz));
    if entry % 2 != 0 || !in_exec {
        return Err(format!(
            "entry {entry:#x} is not 2-aligned inside the file bytes of an executable PT_LOAD"
        ));
    }
    if let Some(a) = &arch {
        if !a.starts_with("rv32") {
            return Err(format!("Tag_RISCV_arch {a:?} is not rv32"));
        }
    }
    cross_check(bytes, &loads)?;
    Ok(RamImage {
        entry,
        e_flags,
        arch,
        loads,
    })
}

/// `Tag_RISCV_arch` (5, NTBS) from a `.riscv.attributes` blob: format version
/// 'A', one "riscv" subsection, one file-scope (tag 1) attribute list. Only
/// enough is parsed to find the arch string; anything else is refused.
fn arch_attribute(b: &[u8]) -> Result<String, String> {
    let bad = || "malformed .riscv.attributes".to_string();
    let uleb = |b: &[u8], at: &mut usize| -> Result<u64, String> {
        let mut v = 0u64;
        for shift in (0..64).step_by(7) {
            let byte = *b.get(*at).ok_or_else(bad)?;
            *at += 1;
            v |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(v);
            }
        }
        Err(bad())
    };
    if b.first() != Some(&b'A') || b.len() < 5 {
        return Err(bad());
    }
    let sub_len = u32::from_le_bytes(b[1..5].try_into().unwrap()) as usize;
    let sub = b
        .get(1..1usize.checked_add(sub_len).ok_or_else(bad)?)
        .ok_or_else(bad)?;
    let rest = sub.get(4..).ok_or_else(bad)?;
    let nul = rest.iter().position(|&c| c == 0).ok_or_else(bad)?;
    if &rest[..nul] != b"riscv" {
        return Err(bad());
    }
    let mut at = nul + 1;
    if rest.get(at) != Some(&1) {
        return Err(bad());
    }
    at += 1;
    let tag_len = rest.get(at..at + 4).ok_or_else(bad)?;
    let end = (at - 1)
        .checked_add(u32::from_le_bytes(tag_len.try_into().unwrap()) as usize)
        .filter(|&e| e <= rest.len())
        .ok_or_else(bad)?;
    at += 4;
    while at < end {
        let tag = uleb(rest, &mut at)?;
        // Even tags carry ULEB128 values, odd ones NUL-terminated strings
        // (the RISC-V psABI convention), so unknown tags can be skipped.
        if tag % 2 == 0 {
            uleb(rest, &mut at)?;
        } else {
            let n = rest[at..end].iter().position(|&c| c == 0).ok_or_else(bad)?;
            if tag == 5 {
                return String::from_utf8(rest[at..at + n].to_vec()).map_err(|_| bad());
            }
            at += n + 1;
        }
    }
    Err("no Tag_RISCV_arch in .riscv.attributes".into())
}

/// e5r's analysis loader is an independent reader of the same file: it must
/// place the same bytes at the same addresses with the same execute bit, and
/// agree there is nothing to relocate or link.
fn cross_check(bytes: &[u8], loads: &[Load]) -> Result<(), String> {
    let obj = e5r_format::load(bytes, &LoadOptions::default()).map_err(|e| e.to_string())?;
    if obj.bits != Bits::Bits32
        || obj.endian != Endian::Little
        || obj.arch != Arch::Sleigh("RISCV:LE:32:default".into())
        || obj.pic
        || !obj.imports.is_empty()
    {
        return Err("e5r loader disagrees about architecture or linkage".into());
    }
    if obj.sections.iter().any(|s| matches!(s.kind, 4 | 6 | 9)) {
        return Err("relocation or dynamic sections are unsupported".into());
    }
    for l in loads.iter().filter(|l| l.filesz > 0) {
        let loaded = obj
            .memory
            .read(Addr(l.vaddr), l.filesz)
            .map_err(|_| format!("e5r loader did not map {:#x}", l.vaddr))?;
        if loaded != l.bytes || obj.memory.is_executable(Addr(l.vaddr)) != l.exec() {
            return Err(format!("e5r loader disagrees at {:#x}", l.vaddr));
        }
    }
    Ok(())
}

fn hex(v: u64) -> String {
    format!("{v:#010x}")
}

/// The assumptions a proof over this image must state or discharge. The
/// exporter establishes none of them beyond A1's byte equations.
pub const ASSUMPTIONS: [&str; 5] = [
    "A1 initial-ram: for every segment, RAM[file.start, file.end) equals the blob bytes and \
     RAM[zero.start, zero.end) is zero; RAM outside all segments is unconstrained (QEMU puts \
     its device tree there)",
    "A2 fetch-coherence: segment permissions are ELF metadata only (QEMU virt RAM is \
     writable and executable, no PMP under -bios none); a model fetching from this image is \
     exact only if no store or AMO ever writes an executable segment's range",
    "A3 entry: QEMU starts the hart in M-mode at its reset ROM (0x1000), which jumps to \
     `entry` with a0 = mhartid, a1 = device-tree address, a2 = 0x1028, t0 = entry; other \
     registers and CSRs are not described here",
    "A4 loader: QEMU's ELF loader places p_filesz bytes at p_paddr (= p_vaddr here) and \
     zero-fills to p_memsz; not checked by the exporter",
    "A5 machine RAM: the window given to the exporter must lie inside the machine's RAM and \
     no other loaded blob (device tree, firmware) may overlap a segment; QEMU's own RAM size \
     (-m) is not checked by the exporter",
];

/// The `e5r.ram-image.v1` manifest. `blob(i)` names segment `i`'s file.
pub fn manifest(elf: &[u8], img: &RamImage, p: Policy) -> Value {
    let segments: Vec<Value> = img
        .loads
        .iter()
        .map(|l| {
            json!({
                "index": l.index,
                "p_offset": l.offset, "p_vaddr": l.vaddr, "p_paddr": l.paddr,
                "p_filesz": l.filesz, "p_memsz": l.memsz, "p_align": l.align,
                "r": l.read(), "w": l.write(), "x": l.exec(),
                "file": {"start": l.vaddr, "end": l.vaddr + l.filesz},
                "zero": l.zero().map(|(s, e)| json!({"start": s, "end": e})),
                "file_sha256": sha256::hex(&l.bytes),
                "blob": blob_name(l.index),
            })
        })
        .collect();
    json!({
        "schema": SCHEMA,
        "tool": {"name": "e5r-verify ram-image", "version": env!("CARGO_PKG_VERSION")},
        "elf": {"sha256": sha256::hex(elf), "size": elf.len()},
        "entry": img.entry,
        "e_flags": img.e_flags,
        "arch_attribute": img.arch,
        "mapping": MAPPING,
        "ram": {"base": p.ram_base, "size": p.ram_size},
        "budgets": {"max_file": p.max_file, "max_file_bytes": p.max_file_bytes},
        "segments": segments,
        "totals": {
            "file_bytes": img.loads.iter().map(|l| l.filesz).sum::<u64>(),
            "zero_bytes": img.loads.iter().map(|l| l.memsz - l.filesz).sum::<u64>(),
        },
        "assumptions": ASSUMPTIONS,
    })
}

pub fn blob_name(index: usize) -> String {
    format!("seg-{index}.bin")
}

/// Lean metadata for the image in namespace `ns`: plain definitions, no
/// theory import. The bytes stay in the blobs (hashed in the manifest) until
/// the Lean-side contract for embedding ~170 KB is agreed with the checker.
pub fn lean(img: &RamImage, elf_sha256: &str, ns: &str) -> String {
    let mut out = format!(
        "-- Generated by e5r-verify ram-image; regenerate, do not edit.\n\
         -- ELF sha256 {elf_sha256}, mapping {MAPPING}.\n\
         set_option maxRecDepth 100000\nnamespace {ns}\n"
    );
    writeln!(out, "def entry : Nat := {}", hex(img.entry)).unwrap();
    out.push_str(
        "/-- (index, vaddr, filesz, memsz, r, w, x): RAM[vaddr, vaddr+filesz) = bytes i,\n    \
         RAM[vaddr+filesz, vaddr+memsz) = 0. -/\n\
         def loads : List (Nat × Nat × Nat × Nat × Bool × Bool × Bool) := [\n",
    );
    for (n, l) in img.loads.iter().enumerate() {
        let sep = if n + 1 < img.loads.len() { "," } else { "" };
        writeln!(
            out,
            "  ({}, {}, {:#x}, {:#x}, {}, {}, {}){sep}",
            l.index,
            hex(l.vaddr),
            l.filesz,
            l.memsz,
            l.read(),
            l.write(),
            l.exec()
        )
        .unwrap();
    }
    out.push_str("]\n");
    writeln!(out, "end {ns}").unwrap();
    out
}

/// Export to a new directory `out`: `manifest.json`, one blob per `PT_LOAD`,
/// `image.lean`. Everything is validated and rendered before the directory
/// is created, so a refusal writes nothing.
pub fn export(elf: &[u8], p: Policy, ns: &str, out: &std::path::Path) -> Result<Value, String> {
    if ns.is_empty()
        || !ns.split('.').all(|c| {
            c.chars().next().is_some_and(|f| f.is_ascii_alphabetic())
                && c.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
        })
    {
        return Err(format!("namespace {ns:?} is not a plain Lean identifier"));
    }
    let img = ram_image(elf, p)?;
    let m = manifest(elf, &img, p);
    let lean = lean(&img, m["elf"]["sha256"].as_str().unwrap(), ns);
    let io = |e: std::io::Error| format!("{}: {e}", out.display());
    std::fs::create_dir(out).map_err(io)?;
    for l in &img.loads {
        std::fs::write(out.join(blob_name(l.index)), &l.bytes).map_err(io)?;
    }
    std::fs::write(out.join("image.lean"), lean).map_err(io)?;
    let text = serde_json::to_string_pretty(&m).unwrap() + "\n";
    std::fs::write(out.join("manifest.json"), text).map_err(io)?;
    Ok(m)
}

#[cfg(test)]
mod tests {
    use super::*;

    const RAM: Policy = Policy {
        ram_base: 0x8000_0000,
        ram_size: 0x1000,
        max_file: DEFAULT_MAX_FILE,
        max_file_bytes: DEFAULT_MAX_FILE_BYTES,
    };
    /// Program header `i`'s field at byte `n`.
    fn ph(i: usize, n: usize) -> usize {
        52 + i * 32 + n
    }

    fn put32(b: &mut [u8], off: usize, v: u32) {
        b[off..off + 4].copy_from_slice(&v.to_le_bytes());
    }

    /// Code (RX, 8 bytes), rodata (R, 4), data with a zero tail (RW, 4 of 16),
    /// bss (RW, 0 of 0x100) and an attributes segment, linked like riscv-rt
    /// links RMK: everything in RAM. The 16 bytes after the data's file bytes
    /// are 0xaa, so a reader that loads p_memsz from the file shows up.
    fn image() -> Vec<u8> {
        let mut b = vec![0u8; 0x13a];
        b[..7].copy_from_slice(b"\x7fELF\x01\x01\x01");
        b[16..20].copy_from_slice(&[2, 0, 243, 0]);
        put32(&mut b, 20, 1);
        put32(&mut b, 24, 0x8000_0000);
        put32(&mut b, 28, 52);
        put32(&mut b, 36, 1);
        b[40..46].copy_from_slice(&[52, 0, 32, 0, 5, 0]);
        let headers: [[u32; 8]; 5] = [
            [1, 0x100, 0x8000_0000, 0x8000_0000, 8, 8, 5, 4],
            [1, 0x108, 0x8000_0008, 0x8000_0008, 4, 4, 4, 4],
            [1, 0x10c, 0x8000_0010, 0x8000_0010, 4, 0x10, 6, 4],
            [1, 0x110, 0x8000_0020, 0x8000_0020, 0, 0x100, 6, 4],
            [PT_RISCV_ATTRIBUTES, 0x120, 0, 0, 26, 26, 4, 1],
        ];
        for (i, h) in headers.iter().enumerate() {
            for (k, v) in h.iter().enumerate() {
                put32(&mut b, ph(i, 4 * k), *v);
            }
        }
        // c.li a0, 1; c.j . ; c.nop; c.nop | rodata | data
        b[0x100..0x110].copy_from_slice(&[
            0x05, 0x45, 0x01, 0xa0, 0x01, 0, 0x01, 0, 1, 2, 3, 4, 0x11, 0x22, 0x33, 0x44,
        ]);
        b[0x110..0x120].fill(0xaa);
        let mut attr = vec![b'A'];
        attr.extend_from_slice(&25u32.to_le_bytes());
        attr.extend_from_slice(b"riscv\0\x01");
        attr.extend_from_slice(&15u32.to_le_bytes());
        attr.extend_from_slice(b"\x05rv32imac\0");
        b[0x120..0x120 + attr.len()].copy_from_slice(&attr);
        b
    }

    fn mutate(edits: &[(usize, u32)]) -> Result<RamImage, String> {
        let mut b = image();
        for &(off, v) in edits {
            put32(&mut b, off, v);
        }
        ram_image(&b, RAM)
    }

    #[test]
    fn file_bytes_and_zero_fill_are_kept_apart() {
        let img = ram_image(&image(), RAM).unwrap();
        assert_eq!(img.entry, 0x8000_0000);
        assert_eq!(img.arch.as_deref(), Some("rv32imac"));
        let got: Vec<_> = img
            .loads
            .iter()
            .map(|l| {
                (
                    l.vaddr,
                    l.bytes.clone(),
                    l.zero(),
                    l.read(),
                    l.write(),
                    l.exec(),
                )
            })
            .collect();
        assert_eq!(
            got,
            [
                (
                    0x8000_0000,
                    vec![0x05, 0x45, 0x01, 0xa0, 1, 0, 1, 0],
                    None,
                    true,
                    false,
                    true
                ),
                (0x8000_0008, vec![1, 2, 3, 4], None, true, false, false),
                (
                    0x8000_0010,
                    vec![0x11, 0x22, 0x33, 0x44],
                    Some((0x8000_0014, 0x8000_0020)),
                    true,
                    true,
                    false
                ),
                (
                    0x8000_0020,
                    vec![],
                    Some((0x8000_0020, 0x8000_0120)),
                    true,
                    true,
                    false
                ),
            ]
        );
    }

    #[test]
    fn manifest_hashes_are_of_the_bytes_and_stable() {
        let elf = image();
        let img = ram_image(&elf, RAM).unwrap();
        let m = manifest(&elf, &img, RAM);
        assert_eq!(m["elf"]["sha256"], sha256::hex(&elf));
        // sha256("\x11\x22\x33\x44"), computed outside this crate.
        assert_eq!(
            m["segments"][2]["file_sha256"],
            "1a835ed8734f86355ca5b835d824d486993aabf1913cd3a011b7446c0514b7c9"
        );
        assert_eq!(m["totals"]["file_bytes"], 16);
        assert_eq!(m["totals"]["zero_bytes"], 12 + 0x100);
        assert_eq!(m["segments"][3]["zero"]["end"], 0x8000_0120u32);
        assert_eq!(m, manifest(&elf, &img, RAM));
    }

    #[test]
    fn refuses_images_whose_initial_ram_is_not_exactly_determined() {
        let cases: &[(&[(usize, u32)], &str)] = &[
            (
                &[(ph(1, 12), 0x2000_0008)],
                "load address differs from run address",
            ),
            (
                &[(ph(3, 8), 0x8000_0f80), (ph(3, 12), 0x8000_0f80)],
                "zero-fill past RAM end",
            ),
            (
                &[(ph(0, 8), 0x7fff_fff8), (ph(0, 12), 0x7fff_fff8)],
                "below RAM",
            ),
            (&[(ph(2, 20), 0x11)], "data zero-fill overlaps bss"),
            (&[(ph(1, 20), 0x9)], "rodata memsz overlaps data"),
            (
                &[
                    (ph(1, 8), 0x8000_0004),
                    (ph(1, 12), 0x8000_0004),
                    (ph(1, 4), 0x104),
                ],
                "overlapping code",
            ),
            (
                &[(ph(2, 8), 0x8000_0200), (ph(2, 12), 0x8000_0200)],
                "out of address order",
            ),
            (&[(ph(2, 16), 0x11)], "p_filesz > p_memsz"),
            (&[(ph(1, 16), 0), (ph(1, 20), 0)], "empty segment"),
            (
                &[(ph(1, 4), 0xffff_ffff)],
                "offset + filesz overflows the file",
            ),
            (&[(ph(1, 4), 0x137)], "file bytes past EOF"),
            (&[(ph(0, 24), 7)], "writable code"),
            (&[(ph(1, 24), 0)], "no permissions"),
            (&[(ph(3, 24), 2)], "write-only"),
            (&[(ph(1, 24), 0x14)], "unknown flag bits"),
            (&[(ph(1, 28), 3)], "non power-of-two align"),
            (
                &[(ph(1, 4), 0x10a)],
                "vaddr and offset disagree modulo align",
            ),
            (&[(24, 0x8000_0001)], "odd entry"),
            (&[(24, 0x8000_0008)], "entry in rodata"),
            (
                &[(24, 0x8000_0006), (ph(0, 16), 6)],
                "entry in the code's zero-fill",
            ),
            (
                &[(24, 0x8000_0006), (ph(0, 16), 7), (ph(0, 20), 7)],
                "entry halfword past file bytes",
            ),
            (&[(36, 3)], "single-float ABI"),
            (&[(36, 8)], "RVE"),
            (&[(16, 3)], "ET_DYN"),
            (&[(28, 0x130)], "program headers past EOF"),
            (&[(28, 0xffff_fff0)], "program header offset overflow"),
            (&[(ph(4, 0), 2)], "PT_DYNAMIC"),
            (&[(ph(4, 0), 3)], "PT_INTERP"),
            (&[(ph(4, 0), 6)], "PT_PHDR"),
            (&[(ph(4, 0), 7)], "PT_TLS"),
            (
                &[(ph(4, 0), PT_GNU_STACK), (ph(4, 24), 7)],
                "executable stack",
            ),
            (
                &[(ph(4, 0), PT_RISCV_ATTRIBUTES), (ph(4, 16), 25)],
                "truncated attributes",
            ),
            (
                &[(0x120 + 17, u32::from_le_bytes(*b"rv64"))],
                "rv64 attribute",
            ),
            (
                &[(ph(0, 0), 0), (ph(1, 0), 0), (ph(2, 0), 0), (ph(3, 0), 0)],
                "no PT_LOAD",
            ),
        ];
        for (edits, what) in cases {
            assert!(mutate(edits).is_err(), "accepted {what}");
        }
        // The reason, not just the refusal, for the rules a looser reader
        // would most plausibly get wrong.
        let reason = |edits: &[(usize, u32)]| mutate(edits).unwrap_err();
        assert!(reason(&[(ph(1, 12), 0x2000_0008)]).contains("paddr=vaddr"));
        assert!(reason(&[(ph(2, 20), 0x11)]).contains("overlap"));
        assert!(reason(&[(ph(1, 4), 0x10a)]).contains("p_align"));
        assert!(reason(&[(ph(1, 4), 0xffff_ffff)]).contains("outside the file"));
        assert!(reason(&[(24, 0x8000_0006), (ph(0, 16), 6)]).contains("entry"));
        assert!(reason(&[(0x120 + 17, u32::from_le_bytes(*b"rv64"))]).contains("not rv32"));
        let mut b = image();
        b[44] = 0;
        assert!(ram_image(&b, RAM).is_err(), "accepted zero program headers");
        b[44] = 17;
        assert!(ram_image(&b, RAM).is_err(), "accepted 17 program headers");
        let mut b = image();
        b[4] = 2;
        assert!(ram_image(&b, RAM).is_err(), "accepted ELFCLASS64");
        let mut b = image();
        b[5] = 2;
        assert!(ram_image(&b, RAM).is_err(), "accepted big-endian");
        for end in 0..image().len() {
            assert!(
                ram_image(&image()[..end], RAM).is_err(),
                "accepted truncation at {end}"
            );
        }
    }

    /// Relocations are invisible in the program headers; only the second
    /// reader, which looks at sections, refuses them.
    #[test]
    fn the_loader_cross_check_refuses_relocatable_content() {
        let mut b = image();
        let shoff = b.len();
        b.resize(shoff + 3 * 40, 0);
        put32(&mut b, 32, shoff as u32);
        b[46..52].copy_from_slice(&[40, 0, 3, 0, 2, 0]);
        // [1] SHT_RELA over nothing, [2] .shstrtab with the names.
        let names = b"\0.rela\0.shstrtab\0";
        let strtab = b.len() as u32;
        b.extend_from_slice(names);
        for (k, v) in [(0, 1), (4, 4), (16, 0x100), (20, 0), (36, 12)] {
            put32(&mut b, shoff + 40 + k, v);
        }
        for (k, v) in [(0, 7), (4, 3), (16, strtab), (20, names.len() as u32)] {
            put32(&mut b, shoff + 80 + k, v);
        }
        let err = ram_image(&b, RAM).unwrap_err();
        assert!(err.contains("relocation"), "{err}");
        // The same file with the section typed PROGBITS is fine.
        put32(&mut b, shoff + 44, 1);
        assert!(ram_image(&b, RAM).is_ok());
    }

    #[test]
    fn rules_hold_at_their_exact_edges() {
        // The last byte of RAM may be loaded; one more may not.
        let edge = [(ph(3, 20), 0x1000 - 0x20)];
        assert!(mutate(&edge).is_ok());
        assert!(mutate(&[(ph(3, 20), 0x1000 - 0x1f)]).is_err());
        // Segments may touch.
        assert!(mutate(&[(ph(2, 20), 0x10)]).is_ok());
        // The entry's halfword may end exactly at the code's last file byte.
        assert!(mutate(&[(24, 0x8000_0006)]).is_ok());
        // A RAM window at the top of the address space: no wraparound.
        let top = Policy::new(0xffff_f000, 0x1000);
        assert!(ram_image(&image(), top).is_err());
        assert!(Policy::new(0xffff_f000, 0x1001).check().is_err());
        assert!(Policy::new(0x8000_0000, 0).check().is_err());
    }

    #[test]
    fn budgets_are_explicit_and_bounded() {
        let mut p = RAM;
        p.max_file_bytes = 15;
        assert!(ram_image(&image(), p).unwrap_err().contains("budget"));
        p.max_file_bytes = 16;
        assert!(ram_image(&image(), p).is_ok());
        p.max_file = image().len() as u64 - 1;
        assert!(ram_image(&image(), p).is_err());
        p.max_file = CEILING_MAX_FILE + 1;
        assert!(ram_image(&image(), p).unwrap_err().contains("ceiling"));
        p.max_file = DEFAULT_MAX_FILE;
        p.max_file_bytes = CEILING_MAX_FILE_BYTES + 1;
        assert!(ram_image(&image(), p).unwrap_err().contains("ceiling"));
    }

    #[test]
    fn export_writes_blobs_and_nothing_on_refusal() {
        let dir = std::env::temp_dir().join(format!("e5r-ram-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let mut bad = image();
        put32(&mut bad, ph(1, 12), 0x2000_0008);
        assert!(export(&bad, RAM, "T", &dir).is_err());
        assert!(
            !dir.exists(),
            "a refused image created its output directory"
        );
        assert!(export(&image(), RAM, "not a name", &dir).is_err());
        assert!(export(&image(), RAM, "T.Ok_1", &dir).is_ok());
        assert_eq!(
            std::fs::read(dir.join("seg-2.bin")).unwrap(),
            [0x11, 0x22, 0x33, 0x44]
        );
        assert!(std::fs::read(dir.join("seg-3.bin")).unwrap().is_empty());
        let lean = std::fs::read_to_string(dir.join("image.lean")).unwrap();
        assert!(lean.contains("(2, 0x80000010, 0x4, 0x10, true, true, false),"));
        assert!(
            export(&image(), RAM, "T", &dir).is_err(),
            "overwrote an export"
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// The pinned RMK example, when its ELF is at hand (`E5R_RMK_ELF`): the
    /// layout and hashes recorded in `docs/ram-image-export.md`.
    #[test]
    fn pinned_rmk_qemu_riscv_rynk() {
        let Ok(path) = std::env::var("E5R_RMK_ELF") else {
            return;
        };
        let elf = std::fs::read(path).unwrap();
        assert_eq!(
            sha256::hex(&elf),
            "f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30"
        );
        let p = Policy::new(0x8000_0000, 0x100_0000);
        let img = ram_image(&elf, p).unwrap();
        let got: Vec<_> = img
            .loads
            .iter()
            .map(|l| (l.vaddr, l.filesz, l.memsz, l.flags, sha256::hex(&l.bytes)))
            .collect();
        let want = [
            (
                0x8000_0000,
                0x210da,
                0x210da,
                5,
                "6327ee65f6d15f1d968ca2dab4da23a132f84faf7e9cb4b8551417547e4b1b3b",
            ),
            (
                0x8002_10dc,
                0x8aec,
                0x8aec,
                4,
                "8bcc02e1e8b9254ed68d9f61f3711bc108c2262ceb2523693666d095ebaf449a",
            ),
            (
                0x8002_9bc8,
                5,
                5,
                6,
                "0bd288cecce2dfc6c9b9245ab747a10870f84c16e986e61b259603b59cf1f3b9",
            ),
            (
                0x8002_9bd0,
                0,
                0xfd_6430,
                6,
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
        ];
        let want: Vec<_> = want
            .iter()
            .map(|&(v, f, m, fl, h)| (v, f, m, fl, h.to_string()))
            .collect();
        assert_eq!(got, want);
        assert_eq!(img.entry, 0x8000_0000);
        // The last zero byte is the last byte of the 16 MiB RAM.
        assert_eq!(img.loads[3].zero().unwrap().1, 0x8100_0000);
        // One byte less RAM, or the old 64 KiB-style budget, is refused.
        assert!(ram_image(&elf, Policy::new(0x8000_0000, 0xff_ffff)).is_err());
        let mut small = p;
        small.max_file_bytes = 1 << 16;
        assert!(ram_image(&elf, small).is_err());
    }
}
