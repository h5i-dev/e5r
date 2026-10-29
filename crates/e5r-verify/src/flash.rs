//! Export a bare-metal firmware ELF as the flash contents a board boots from.
//!
//! On a board there is no loader: what exists at reset is what the flash
//! programmer wrote, which is every `PT_LOAD`'s file bytes at its physical
//! address. RAM holds whatever it held; startup code copies `.data` and zeroes
//! `.bss`. So the export is the file-backed parts of the image placed at
//! `p_paddr`, and nothing else. A `PT_LOAD` with no file bytes (`.bss`, the
//! stack) contributes nothing and must lie in RAM.
//!
//! The program headers are parsed here, strictly, and the result is then
//! cross-checked against e5r's own loader. The Lean side has a third,
//! independent reader whose equality with this export is a kernel-checked
//! theorem.

use e5r_core::{Arch, Bits, Endian};
use e5r_format::LoadOptions;
use std::fmt::Write;

/// The address windows of the board the image is exported for.
#[derive(Clone, Copy, Debug)]
pub struct Windows {
    pub flash_base: u64,
    pub flash_size: u64,
    pub ram_base: u64,
    pub ram_size: u64,
}

/// One flash segment: physical base, file bytes, executable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlashSegment {
    pub base: u64,
    pub bytes: Vec<u8>,
    pub exec: bool,
    pub file_offset: u64,
    /// Runs where it is stored (code, read-only data), rather than being
    /// copied to RAM by startup code (`.data`).
    pub in_place: bool,
}

/// What the board boots: entry and flash contents.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlashImage {
    pub entry: u64,
    pub segments: Vec<FlashSegment>,
}

/// Largest ELF file accepted. Firmware for a 16 KiB-RAM part is far smaller.
pub const MAX_FILE: usize = 1 << 20;
/// Largest total of file-backed bytes exported to Lean.
pub const MAX_FLASH: u64 = 1 << 18;

const PT_NULL: u32 = 0;
const PT_LOAD: u32 = 1;
const PT_GNU_STACK: u32 = 0x6474_e551;
const PT_RISCV_ATTRIBUTES: u32 = 0x7000_0003;
/// `e_flags`: RVC may be set; the ABI must be soft-float, no RVE, no TSO.
const EF_RISCV_RVC: u32 = 1;

fn u16_at(b: &[u8], off: usize) -> Result<u64, String> {
    b.get(off..off + 2)
        .map(|s| u16::from_le_bytes([s[0], s[1]]) as u64)
        .ok_or_else(|| format!("truncated at {off:#x}"))
}

fn u32_at(b: &[u8], off: usize) -> Result<u64, String> {
    b.get(off..off + 4)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]) as u64)
        .ok_or_else(|| format!("truncated at {off:#x}"))
}

fn within(addr: u64, len: u64, base: u64, size: u64) -> bool {
    addr >= base && addr.checked_add(len).is_some_and(|end| end <= base + size)
}

/// Parse and validate the image for `w`. Every refusal names the rule.
pub fn flash_image(bytes: &[u8], w: Windows) -> Result<FlashImage, String> {
    if bytes.len() > MAX_FILE || bytes.len() < 52 {
        return Err(format!("ELF size must be 52..={MAX_FILE} bytes"));
    }
    if &bytes[..7] != b"\x7fELF\x01\x01\x01" {
        return Err("not a little-endian ELF32 file".into());
    }
    if u16_at(bytes, 16)? != 2 || u16_at(bytes, 18)? != 243 || u32_at(bytes, 20)? != 1 {
        return Err("requires an EM_RISCV ET_EXEC (static executable)".into());
    }
    let flags = u32_at(bytes, 36)? as u32;
    if flags & !EF_RISCV_RVC != 0 {
        return Err(format!(
            "e_flags {flags:#x}: only RVC with the soft-float ABI is supported"
        ));
    }
    if u16_at(bytes, 40)? != 52 || u16_at(bytes, 42)? != 32 {
        return Err("unexpected ELF32 header or program header size".into());
    }
    let phoff = u32_at(bytes, 28)? as usize;
    let phnum = u16_at(bytes, 44)? as usize;
    if !(1..=16).contains(&phnum) {
        return Err("requires 1..=16 program headers".into());
    }
    let entry = u32_at(bytes, 24)?;
    let mut segments: Vec<FlashSegment> = Vec::new();
    let mut total = 0;
    for i in 0..phnum {
        let off = phoff
            .checked_add(i * 32)
            .ok_or("program header offset overflows")?;
        let field = |n: usize| u32_at(bytes, off + n);
        let kind = field(0)? as u32;
        let (file, vaddr, paddr) = (field(4)?, field(8)?, field(12)?);
        let (filesz, memsz, pflags) = (field(16)?, field(20)?, field(24)?);
        match kind {
            PT_NULL | PT_GNU_STACK | PT_RISCV_ATTRIBUTES => continue,
            PT_LOAD => {}
            other => return Err(format!("program header {i}: unsupported type {other:#x}")),
        }
        if pflags > 7 || filesz > memsz || memsz == 0 {
            return Err(format!("PT_LOAD {i}: bad sizes or flags"));
        }
        let (exec, write) = (pflags & 1 != 0, pflags & 2 != 0);
        if exec && write {
            return Err(format!("PT_LOAD {i}: writable and executable"));
        }
        if filesz == 0 {
            // .bss, .uninit, heap and stack: RAM that startup code owns.
            if !write || !within(vaddr, memsz, w.ram_base, w.ram_size) {
                return Err(format!(
                    "PT_LOAD {i}: a segment without file bytes must be writable RAM"
                ));
            }
            continue;
        }
        if file
            .checked_add(filesz)
            .is_none_or(|e| e > bytes.len() as u64)
        {
            return Err(format!("PT_LOAD {i}: file bytes outside the file"));
        }
        if !within(paddr, filesz, w.flash_base, w.flash_size) {
            return Err(format!(
                "PT_LOAD {i}: physical address {paddr:#x} is not in flash"
            ));
        }
        if write {
            // .data: its load image sits in flash, its run address in RAM.
            if !within(vaddr, memsz, w.ram_base, w.ram_size) {
                return Err(format!("PT_LOAD {i}: writable run address not in RAM"));
            }
        } else if vaddr != paddr || filesz != memsz {
            // Code and read-only data execute and are read in place (XIP).
            return Err(format!(
                "PT_LOAD {i}: a read-only segment must run where it is stored"
            ));
        }
        total += filesz;
        if total > MAX_FLASH {
            return Err(format!("more than {MAX_FLASH} bytes of flash"));
        }
        segments.push(FlashSegment {
            base: paddr,
            bytes: bytes[file as usize..(file + filesz) as usize].to_vec(),
            exec,
            file_offset: file,
            in_place: vaddr == paddr,
        });
    }
    // Linkers emit PT_LOADs in address order. Requiring it, rather than
    // sorting, keeps the independent Lean reader equally simple.
    for pair in segments.windows(2) {
        if pair[0].base + pair[0].bytes.len() as u64 > pair[1].base {
            return Err("flash segments overlap or are out of address order".into());
        }
    }
    let in_exec = segments
        .iter()
        .any(|s| s.exec && within(entry, 2, s.base, s.bytes.len() as u64));
    if entry % 2 != 0 || !in_exec {
        return Err(format!("entry {entry:#x} is not aligned executable flash"));
    }
    cross_check(bytes, &segments)?;
    Ok(FlashImage { entry, segments })
}

/// e5r's loader maps by virtual address. For every in-place segment its bytes
/// must be exactly ours: two independent parsers of the same headers.
fn cross_check(bytes: &[u8], segments: &[FlashSegment]) -> Result<(), String> {
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
    for s in segments.iter().filter(|s| s.in_place) {
        let loaded = obj
            .memory
            .read(e5r_core::Addr(s.base), s.bytes.len() as u64)
            .map_err(|_| format!("e5r loader did not map {:#x}", s.base))?;
        if loaded != s.bytes || obj.memory.is_executable(e5r_core::Addr(s.base)) != s.exec {
            return Err(format!("e5r loader disagrees at {:#x}", s.base));
        }
    }
    Ok(())
}

/// Lean source for the image: the original file bytes, the entry and the
/// flash segments, in the namespace `ns`.
pub fn export_flash(bytes: &[u8], w: Windows, ns: &str) -> Result<String, String> {
    let img = flash_image(bytes, w)?;
    let mut out = format!(
        "-- Generated by e5r-verify flash; regenerate, do not edit.\nimport Theories.Platform\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\n"
    );
    writeln!(out, "def elfBytes : List Nat := {:?}", bytes).unwrap();
    writeln!(out, "def entry : Nat := {:#x}", img.entry).unwrap();
    out.push_str("def segments : List E5R.Segment := [\n");
    for (i, s) in img.segments.iter().enumerate() {
        if i != 0 {
            out.push_str(",\n");
        }
        writeln!(
            out,
            "  -- PT_LOAD file offset {:#x}, {} bytes",
            s.file_offset,
            s.bytes.len()
        )
        .unwrap();
        write!(out, "  ⟨{:#x}, {:?}, {}⟩", s.base, s.bytes, s.exec).unwrap();
    }
    writeln!(out, "\n]\nend {ns}").unwrap();
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    const W: Windows = Windows {
        flash_base: 0x2000_0000,
        flash_size: 0x2000_0000,
        ram_base: 0x8000_0000,
        ram_size: 0x4000,
    };

    /// A two-segment image: 8 bytes of code at 0x20010000 (file offset 0x100)
    /// and an empty 0x100-byte RAM segment.
    fn image() -> Vec<u8> {
        let mut b = vec![0u8; 0x108];
        b[..7].copy_from_slice(b"\x7fELF\x01\x01\x01");
        let put16 =
            |b: &mut Vec<u8>, off: usize, v: u16| b[off..off + 2].copy_from_slice(&v.to_le_bytes());
        let put32 =
            |b: &mut Vec<u8>, off: usize, v: u32| b[off..off + 4].copy_from_slice(&v.to_le_bytes());
        put16(&mut b, 16, 2);
        put16(&mut b, 18, 243);
        put32(&mut b, 20, 1);
        put32(&mut b, 24, 0x2001_0000);
        put32(&mut b, 28, 52);
        put32(&mut b, 36, 1);
        put16(&mut b, 40, 52);
        put16(&mut b, 42, 32);
        put16(&mut b, 44, 2);
        for (off, v) in [
            (0, 1),
            (4, 0x100),
            (8, 0x2001_0000),
            (12, 0x2001_0000),
            (16, 8),
            (20, 8),
            (24, 5),
        ] {
            put32(&mut b, 52 + off, v);
        }
        for (off, v) in [
            (0, 1),
            (8, 0x8000_0000),
            (12, 0x8000_0000),
            (20, 0x100),
            (24, 6),
        ] {
            put32(&mut b, 84 + off, v);
        }
        // c.li a0, 1; c.j . ; two halfwords of padding
        b[0x100..0x108].copy_from_slice(&[0x05, 0x45, 0x01, 0xa0, 0, 0, 0, 0]);
        b
    }

    #[test]
    fn exports_file_bytes_at_physical_addresses_only() {
        let img = flash_image(&image(), W).unwrap();
        assert_eq!(img.entry, 0x2001_0000);
        assert_eq!(img.segments.len(), 1, "the RAM segment has no file bytes");
        assert_eq!(img.segments[0].bytes, [0x05, 0x45, 0x01, 0xa0, 0, 0, 0, 0]);
        assert!(img.segments[0].exec);
        let src = export_flash(&image(), W, "T").unwrap();
        assert!(src.contains("⟨0x20010000, [5, 69, 1, 160, 0, 0, 0, 0], true⟩"));
        assert_eq!(src, export_flash(&image(), W, "T").unwrap());
    }

    #[test]
    fn refuses_what_a_board_cannot_boot() {
        let mutate = |off: usize, v: u32| {
            let mut b = image();
            b[off..off + 4].copy_from_slice(&v.to_le_bytes());
            flash_image(&b, W)
        };
        let cases = [
            (36, 3, "float ABI e_flags"),
            (52 + 24, 7, "writable executable code"),
            (52 + 12, 0x1000_0000, "code stored outside flash"),
            (52 + 8, 0x2002_0000, "code not run in place"),
            (84 + 8, 0x9000_0000, "bss outside RAM"),
            (84 + 24, 4, "read-only segment without bytes"),
            (24, 0x2001_0001, "odd entry"),
            (24, 0x2002_0000, "entry outside code"),
            (84, 2, "dynamic segment"),
            (52 + 16, 0x200, "file bytes past the end"),
        ];
        for (off, v, what) in cases {
            assert!(mutate(off, v).is_err(), "accepted {what}");
        }
        for end in 0..image().len() {
            assert!(
                flash_image(&image()[..end], W).is_err(),
                "accepted truncation at {end}"
            );
        }
    }
}
