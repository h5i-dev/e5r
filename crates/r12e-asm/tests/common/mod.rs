//! Shared corpus plumbing for the assembler's gates.

use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_arch::insn::Insn;
use r12e_core::{Addr, Arch};

/// One instruction as an external disassembler reported it.
pub struct Line {
    pub addr: u64,
    pub bytes: Vec<u8>,
}

pub fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// The disassembler used only to find instruction boundaries. Decoding is
/// still r12e's own; this says where one instruction ends and the next starts.
pub fn objdump(arch: &Arch) -> Option<&'static str> {
    let candidates: &[&str] = match arch {
        Arch::X86_64 => &["llvm-objdump-18", "llvm-objdump-15", "llvm-objdump"],
        _ => &["objdump", "llvm-objdump-18", "llvm-objdump"],
    };
    candidates
        .iter()
        .copied()
        .find(|c| Command::new(c).arg("--version").output().is_ok())
}

pub fn disassemble(tool: &str, path: &Path, arch: &Arch) -> Vec<Line> {
    let mut cmd = Command::new(tool);
    cmd.arg("-d");
    if *arch == Arch::X86_64 && tool.starts_with("llvm") {
        cmd.arg("--x86-asm-syntax=intel");
    }
    let Ok(out) = cmd.arg(path).output() else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lines = Vec::new();
    for l in text.lines() {
        // Both spellings of the listing: llvm's "   0: 85 ff  \ttest..." and
        // binutils' "   0:\t85 ff \ttest...".
        let Some((left, rest)) = l.split_once(':') else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let raw = match rest.find('\t') {
            Some(i) if rest[..i].trim().is_empty() => match rest[i + 1..].find('\t') {
                Some(j) => &rest[i + 1..i + 1 + j],
                None => continue,
            },
            Some(i) => &rest[..i],
            None => continue,
        };
        // binutils prints an A64 instruction as one eight-digit word and an
        // x86 one as separated bytes, so both spellings are read here.
        let fields: Vec<&str> = raw.split_whitespace().collect();
        let bytes = if fields.len() == 1 && fields[0].len() == 8 {
            match u32::from_str_radix(fields[0], 16) {
                Ok(w) => w.to_le_bytes().to_vec(),
                Err(_) => continue,
            }
        } else {
            let parsed: Option<Vec<u8>> = fields
                .iter()
                .map(|h| u8::from_str_radix(h, 16).ok())
                .collect();
            match parsed {
                Some(b) => b,
                None => continue,
            }
        };
        if bytes.is_empty() || bytes.len() > 15 {
            continue;
        }
        lines.push(Line { addr, bytes });
    }
    lines
}

pub fn decode_for(arch: &Arch, bytes: &[u8], addr: Addr) -> Option<Insn> {
    r12e_arch::decode(arch, bytes, addr)
}

/// The text the assembler has to accept, which is what `r12e disas` prints.
pub fn render(arch: &Arch, i: &Insn) -> String {
    r12e_arch::format(arch, i, false)
}

/// Two instructions compare by what they are, not by where they were found or
/// how long the encoding that produced them happened to be.
pub fn normalize(i: &Insn) -> Insn {
    let mut c = *i;
    c.len = 0;
    c.flow = r12e_arch::insn::Flow::Next;
    c
}
