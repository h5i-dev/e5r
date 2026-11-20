//! e5r: a formal-verification-friendly profile of RISC-V (RV64IM + Zba +
//! Zbb, structured control flow, a fixed stack discipline), and the tools to
//! check a binary against it, record its structure, and export it to Lean 4.
//!
//! None of this crate is trusted by a proof. A binary that passes `check` is
//! one the proof tactics handle well; what a proof establishes is checked by
//! the Lean kernel against the bytes of the binary (see docs/isa/trust.md).

pub mod elf;
pub mod isa;
pub mod lean;
pub mod meta;
pub mod profile;
pub mod sha256;

use profile::{Func, FuncMeta, Violation};
use std::collections::BTreeSet;

/// ELF `e_flags` bit for the C extension.
const EF_RISCV_RVC: u32 = 1;

/// A RISC-V executable as the profile sees it.
pub struct Binary<'a> {
    pub bytes: &'a [u8],
    pub text_addr: u64,
    pub text: Vec<u32>,
    pub funcs: Vec<Func>,
    /// `.e5r.struct`, if the file has one.
    pub recorded: Option<Vec<FuncMeta>>,
}

pub fn load(bytes: &[u8]) -> Result<Binary<'_>, String> {
    let e = elf::Elf::parse(bytes).map_err(|e| e.to_string())?;
    if e.machine != elf::EM_RISCV {
        return Err(format!("e_machine {} is not RISC-V", e.machine));
    }
    if e.flags & EF_RISCV_RVC != 0 {
        return Err(
            "built with the C extension (e_flags RVC); the profile has fixed 32-bit instructions"
                .into(),
        );
    }
    let text = e.section(".text").ok_or("no .text section")?;
    for s in &e.sections {
        if s.flags & elf::SHF_EXECINSTR != 0 && s.name != ".text" && s.size > 0 {
            return Err(format!(
                "executable section {} besides .text; the profile has one",
                s.name
            ));
        }
    }
    if text.addr % 4 != 0 || text.size % 4 != 0 {
        return Err(".text is not a whole number of aligned words".into());
    }
    let words: Vec<u32> = e
        .bytes(text)
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect();
    let mut funcs = Vec::new();
    for s in e.functions() {
        if s.value < text.addr || s.value + s.size > text.addr + text.size {
            continue;
        }
        if (s.value - text.addr) % 4 != 0 || s.size % 4 != 0 {
            return Err(format!(
                "function {} is not a whole number of aligned words",
                s.name
            ));
        }
        let i = ((s.value - text.addr) / 4) as usize;
        funcs.push(Func {
            name: s.name.clone(),
            entry: s.value,
            words: words[i..i + (s.size / 4) as usize].to_vec(),
        });
    }
    let recorded = match e.section(meta::SECTION) {
        Some(s) => Some(meta::decode(e.bytes(s))?),
        None => None,
    };
    Ok(Binary {
        bytes,
        text_addr: text.addr,
        text: words,
        funcs,
        recorded,
    })
}

/// The outcome for one function.
pub struct Report {
    pub name: String,
    pub entry: u64,
    pub result: Result<FuncMeta, Vec<Violation>>,
}

impl Binary<'_> {
    pub fn entries(&self) -> BTreeSet<u64> {
        self.funcs.iter().map(|f| f.entry).collect()
    }

    /// Check every function: against `.e5r.struct` where the file has one,
    /// otherwise against the recovered tree. A recorded entry whose frame,
    /// callees or size disagree with the code is a violation.
    pub fn check(&self) -> Vec<Report> {
        let entries = self.entries();
        self.funcs
            .iter()
            .map(|f| {
                let recorded = self.recorded.as_ref().map(|r| r.iter().find(|m| m.entry == f.entry));
                let result = match recorded {
                    Some(None) => Err(vec![Violation {
                        addr: f.entry,
                        rule: "M1 metadata",
                        detail: format!("{} has no entry in {}", f.name, meta::SECTION),
                    }]),
                    Some(Some(m)) => profile::check(f, &m.nodes, &entries).and_then(|got| {
                        if got.frame == m.frame && got.callees == m.callees && got.size == m.size {
                            Ok(got)
                        } else {
                            Err(vec![Violation {
                                addr: f.entry,
                                rule: "M1 metadata",
                                detail: format!(
                                    "recorded frame {} callees {:x?} size {}, the code has {} {:x?} {}",
                                    m.frame, m.callees, m.size, got.frame, got.callees, got.size
                                ),
                            }])
                        }
                    }),
                    None => profile::recover(f, &entries)
                        .map_err(|e| vec![e])
                        .and_then(|nodes| profile::check(f, &nodes, &entries)),
                };
                Report { name: f.name.clone(), entry: f.entry, result }
            })
            .collect()
    }
}
