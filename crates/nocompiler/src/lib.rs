//! nocompiler: a formal-verification-friendly profile of RISC-V (RV64IM + Zba +
//! Zbb, structured control flow, a fixed stack discipline), and the tools to
//! check a binary against it, record its structure, and export it to Lean 4.
//!
//! None of this crate is trusted by a proof. A binary that passes `check` is
//! one the proof tactics handle well; what a proof establishes is checked by
//! the Lean kernel against the bytes of the binary (see docs/isa/trust.md).

pub mod cc;
pub mod cmd;
pub mod dwarf;
pub mod elf;
pub mod frame;
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
    /// `.nocompiler.struct`, if the file has one.
    pub recorded: Option<Vec<FuncMeta>>,
    /// Functions whose record declares a frame partition (version 2 tables).
    pub declared: BTreeSet<String>,
    /// Stack variables the DWARF debug information places in each frame.
    pub dwarf: dwarf::FrameVars,
    /// Every allocated section that is not code, in header order.
    pub segments: Vec<DataSegment>,
}

/// An allocated, non-executable section: `.rodata`, `.data`, `.bss`, ...
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataSegment {
    pub name: String,
    pub addr: u64,
    /// The bytes; zeros for NOBITS.
    pub bytes: Vec<u8>,
    /// NOBITS (`.bss`): exported as zeros of `bytes.len()`.
    pub zero: bool,
    pub writable: bool,
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
    let segments = e
        .sections
        .iter()
        .filter(|s| {
            s.flags & elf::SHF_ALLOC != 0
                && s.flags & elf::SHF_EXECINSTR == 0
                && s.size > 0
                && (s.kind == elf::SHT_PROGBITS || s.kind == elf::SHT_NOBITS)
        })
        .map(|s| DataSegment {
            name: s.name.clone(),
            addr: s.addr,
            bytes: if s.kind == elf::SHT_NOBITS {
                vec![0; s.size as usize]
            } else {
                e.bytes(s).to_vec()
            },
            zero: s.kind == elf::SHT_NOBITS,
            writable: s.flags & elf::SHF_WRITE != 0,
        })
        .collect();
    let mut declared = BTreeSet::new();
    let recorded = match e.section(meta::SECTION) {
        Some(s) => {
            let by_name: std::collections::BTreeMap<String, u64> =
                funcs.iter().map(|f| (f.name.clone(), f.entry)).collect();
            let mut out = Vec::new();
            for r in meta::decode(e.bytes(s))? {
                let entry = *by_name.get(&r.meta.name).ok_or_else(|| {
                    format!(
                        "{}: {} is not a function of this file",
                        meta::SECTION,
                        r.meta.name
                    )
                })?;
                if r.version >= 2 {
                    declared.insert(r.meta.name.clone());
                }
                out.push(r.place(entry, &by_name)?);
            }
            Some(out)
        }
        None => None,
    };
    Ok(Binary {
        bytes,
        text_addr: text.addr,
        text: words,
        funcs,
        recorded,
        declared,
        dwarf: dwarf::frame_vars(&e),
        segments,
    })
}

/// The outcome for one function.
pub struct Report {
    pub name: String,
    pub entry: u64,
    /// The level reached: `None` when it does not even decode (R1).
    pub level: Option<profile::Level>,
    /// `Ok` at L1 and above, with the metadata to record; otherwise why not.
    pub result: Result<FuncMeta, Vec<Violation>>,
    /// At L1: why the function is not at L2 (empty at L2).
    pub missed: Vec<Violation>,
    /// At L2: the certificate for the Lean checker.
    pub cert: Vec<frame::CertFact>,
}

impl Binary<'_> {
    pub fn entries(&self) -> BTreeSet<u64> {
        self.funcs.iter().map(|f| f.entry).collect()
    }

    /// Check every function: against `.nocompiler.struct` where the file has one,
    /// otherwise against the recovered tree and an inferred frame partition.
    /// A recorded entry whose level, frame, callees or size disagree with the
    /// code is a violation (M1).
    pub fn check(&self) -> Vec<Report> {
        let entries = self.entries();
        self.funcs
            .iter()
            .map(|f| {
                let recorded = self.recorded.as_ref().map(|r| r.iter().find(|m| m.entry == f.entry));
                let fail = |level, violations| Report {
                    name: f.name.clone(),
                    entry: f.entry,
                    level,
                    result: Err(violations),
                    missed: vec![],
                    cert: vec![],
                };
                let (nodes, part) = match recorded {
                    Some(None) => {
                        return fail(
                            None,
                            vec![Violation {
                                addr: f.entry,
                                rule: "M1 metadata",
                                detail: format!("{} has no entry in {}", f.name, meta::SECTION),
                            }],
                        )
                    }
                    Some(Some(m)) => {
                        let part = self.declared.contains(&f.name).then(|| frame::Partition {
                            slots: m.slots.clone(),
                            ranges: m.ranges.clone(),
                        });
                        (m.nodes.clone(), part)
                    }
                    None => match profile::recover(f, &entries) {
                        Ok(nodes) => (nodes, None),
                        Err(e) => {
                            let level = (e.rule != "R1 decode").then_some(profile::Level::L0);
                            return fail(level, vec![e]);
                        }
                    },
                };
                match profile::check_with(f, &nodes, part.as_ref(), self.dwarf.get(&f.entry), &entries) {
                    Err(e) => fail(e.level, e.violations),
                    Ok(c) => {
                        let got = c.meta;
                        if let Some(Some(m)) = recorded {
                            if got.frame != m.frame
                                || got.callees != m.callees
                                || got.size != m.size
                                || (self.declared.contains(&f.name) && got.level != m.level)
                            {
                                return fail(
                                    Some(profile::Level::L0),
                                    vec![Violation {
                                        addr: f.entry,
                                        rule: "M1 metadata",
                                        detail: format!(
                                            "recorded frame {} callees {:x?} size {} level {:?}, the code has {} {:x?} {} {:?}",
                                            m.frame, m.callees, m.size, m.level, got.frame, got.callees, got.size, got.level
                                        ),
                                    }],
                                );
                            }
                        }
                        Report {
                            name: f.name.clone(),
                            entry: f.entry,
                            level: Some(got.level),
                            result: Ok(got),
                            missed: c.missed,
                            cert: c.cert,
                        }
                    }
                }
            })
            .collect()
    }
}

/// Check `file` and write it to `out` with an `.nocompiler.struct` section (through
/// llvm-objcopy, or `NOCOMPILER_OBJCOPY`). The inner error lists the violations,
/// when a function does not conform and nothing is written.
pub fn annotate(
    file: &std::path::Path,
    out: &std::path::Path,
) -> Result<Result<(usize, usize), Vec<String>>, String> {
    let bytes = std::fs::read(file).map_err(|e| format!("{}: {e}", file.display()))?;
    let mut bin = load(&bytes)?;
    // What is recorded is replaced, so it is not what the code is checked
    // against: the tree is recovered and the partition inferred afresh.
    let had_section = bin.recorded.take().is_some();
    bin.declared.clear();
    let mut metas = Vec::new();
    let mut bad = Vec::new();
    for r in bin.check() {
        match r.result {
            Ok(m) => metas.push(m),
            Err(vs) => bad.extend(vs.into_iter().map(|v| format!("{} {v}", r.name))),
        }
    }
    if !bad.is_empty() {
        return Ok(Err(bad));
    }
    let names: std::collections::BTreeMap<u64, String> = bin
        .funcs
        .iter()
        .map(|f| (f.entry, f.name.clone()))
        .collect();
    let data = meta::encode(&metas, &names)?;
    let tmp = out.with_extension("nocompiler-struct.tmp");
    std::fs::write(&tmp, &data).map_err(|e| format!("{}: {e}", tmp.display()))?;
    let objcopy = std::env::var("NOCOMPILER_OBJCOPY").unwrap_or_else(|_| "llvm-objcopy".into());
    let verb = if had_section {
        "--update-section"
    } else {
        "--add-section"
    };
    let st = std::process::Command::new(&objcopy)
        .arg(format!("{verb}={}={}", meta::SECTION, tmp.display()))
        .arg(file)
        .arg(out)
        .status()
        .map_err(|e| format!("{objcopy}: {e} (set NOCOMPILER_OBJCOPY)"));
    let _ = std::fs::remove_file(&tmp);
    if !st?.success() {
        return Err(format!("{objcopy} failed"));
    }
    Ok(Ok((metas.len(), data.len())))
}
