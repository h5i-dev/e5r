//! `nocompiler cc`: compile and link into the profile with clang and ld.lld, then
//! record `.nocompiler.struct` and check (docs/isa/toolchain.md).
//!
//! The flags are what keeps ordinary C inside the profile without changing
//! LLVM. Each one is there because without it clang emits something a rule
//! rejects:
//!
//! | flag | without it |
//! | --- | --- |
//! | `-march=rv64im_zba_zbb` | C, A, F, D instructions (R1) |
//! | `-mcmodel=medany` | data addresses as absolute `lui`/`addi` pairs (`R_RISCV_HI20`/`LO12`): the code is then tied to where the data is, and a proof cannot be relocated (docs/isa/v1.md, relocation) |
//! | `-mno-relax` | the linker rewrites calls after the code is checked |
//! | `-fno-pic`, static link | PLT and GOT: indirect calls (R2) |
//! | `-fno-jump-tables` | a dense `switch` becomes an indirect jump (R2) |
//! | `-mllvm -disable-block-placement` | loops rotated so their header is in the middle: entered by a forward jump into the loop (R3) |
//! | `-ffreestanding -nostdlib` | libc, which would have to conform too |
//!
//! What remains outside the profile is what the source asks for: calls
//! through function pointers (R2), and inline assembly that breaks a rule.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The flags every compilation gets, before the user's.
pub const CFLAGS: &[&str] = &[
    "--target=riscv64-unknown-elf",
    "-march=rv64im_zba_zbb",
    "-mabi=lp64",
    "-mcmodel=medany",
    "-mno-relax",
    "-fno-pic",
    "-ffreestanding",
    "-nostdlib",
    "-fno-jump-tables",
    "-fno-asynchronous-unwind-tables",
    "-fno-unwind-tables",
    "-fno-ident",
    "-mllvm",
    "-disable-block-placement",
];

pub struct Report {
    pub conforms: bool,
    pub text: String,
}

fn found(cands: &[String]) -> Option<String> {
    cands
        .iter()
        .find(|c| {
            Command::new(c)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success())
        })
        .cloned()
}

/// clang (`CLANG`) and ld.lld (`LLD`, or the first versioned one on PATH).
pub fn tools() -> Result<(String, String), String> {
    let env = |v: &str, d: &[&str]| match std::env::var(v) {
        Ok(x) => vec![x],
        Err(_) => d.iter().map(|s| s.to_string()).collect(),
    };
    let clang = found(&env("CLANG", &["clang"])).ok_or("cc: no clang (set CLANG)")?;
    let lld = found(&env(
        "LLD",
        &[
            "ld.lld",
            "ld.lld-22",
            "ld.lld-21",
            "ld.lld-20",
            "ld.lld-19",
            "ld.lld-18",
        ],
    ))
    .ok_or("cc: no ld.lld (set LLD)")?;
    Ok((clang, lld))
}

fn is_source(a: &str) -> bool {
    [".c", ".S", ".s"].iter().any(|e| a.ends_with(e)) && !a.starts_with('-')
}

/// Compile every source in `args` (the rest are clang flags; `-O2` unless an
/// `-O` is given), link with entry `_start`, write `out` with `.nocompiler.struct`
/// when every function conforms, and report.
pub fn build(args: &[String], out: &Path) -> Result<Report, String> {
    let (clang, lld) = tools()?;
    let sources: Vec<&String> = args.iter().filter(|a| is_source(a)).collect();
    if sources.is_empty() {
        return Err("cc: no source files".into());
    }
    let mut flags: Vec<&str> = CFLAGS.to_vec();
    if !args.iter().any(|a| a.starts_with("-O")) {
        flags.push("-O2");
    }
    let user: Vec<&str> = args
        .iter()
        .filter(|a| !is_source(a))
        .map(|s| s.as_str())
        .collect();
    let tmp = out.with_extension("nocompiler-cc");
    std::fs::create_dir_all(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
    let mut objs: Vec<PathBuf> = Vec::new();
    for (i, src) in sources.iter().enumerate() {
        let obj = tmp.join(format!("{i}.o"));
        let st = Command::new(&clang)
            .args(&flags)
            .args(&user)
            .arg("-c")
            .arg(src)
            .arg("-o")
            .arg(&obj)
            .status()
            .map_err(|e| format!("{clang}: {e}"))?;
        if !st.success() {
            return Err(format!("cc: clang failed on {src}"));
        }
        objs.push(obj);
    }
    let raw = tmp.join("linked.elf");
    let st = Command::new(&lld)
        .args([
            "-static",
            "-e",
            "_start",
            "--build-id=none",
            "-z",
            "noseparate-code",
        ])
        .args(&objs)
        .arg("-o")
        .arg(&raw)
        .status()
        .map_err(|e| format!("{lld}: {e}"))?;
    if !st.success() {
        return Err("cc: ld.lld failed".into());
    }
    let mut text = String::new();
    let conforms = match crate::annotate(&raw, out)? {
        Ok((n, _)) => {
            text.push_str(&format!("{}: {n} functions, all conform\n", out.display()));
            true
        }
        Err(vs) => {
            std::fs::copy(&raw, out).map_err(|e| format!("{}: {e}", out.display()))?;
            text.push_str(&format!(
                "{}: written without .nocompiler.struct; violations:\n",
                out.display()
            ));
            for v in vs {
                text.push_str(&format!("  {v}\n"));
            }
            false
        }
    };
    let _ = std::fs::remove_dir_all(&tmp);
    Ok(Report { conforms, text })
}
