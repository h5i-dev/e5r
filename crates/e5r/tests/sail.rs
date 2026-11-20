//! The Lean semantics against the official Sail RISC-V model.
//!
//! The same kind of random straight-line programs as `tests/semantics.rs`
//! (every instruction of the profile, interesting operands), linked at the
//! Sail emulator's RAM base, are run by `sail_riscv_sim`, the C emulator
//! generated from the Sail model, and by the executable Lean semantics
//! (`E5R.runToEcall`). Each program stores every register into a buffer and
//! then writes `tohost`, which stops Sail; the Lean run stops at the `ecall`
//! after it. Sail writes the buffer out as a test signature
//! (`begin_signature` to `end_signature`), and the two must be identical.
//!
//! Needs clang, ld.lld, lake and the Sail emulator: SAIL_RISCV_SIM names it
//! (release binaries: https://github.com/riscv/sail-riscv/releases). Skips,
//! loudly, when one is missing. E5R_SAIL_PROGRAMS sets the number of
//! programs (default 48).

mod common;
use common::*;
use std::fmt::Write as _;
use std::process::Command;

const LINK: &str = "SECTIONS {\n  . = 0x80000000;\n  .text : { *(.text*) }\n  . = ALIGN(4096);\n  .data : { *(.data*) *(.sdata*) *(.bss*) *(.sbss*) }\n}\n";

const END: &str = "  la t0, tohost\n  li t1, 1\n  sd t1, 0(t0)\n  ecall\n";
const DATA: &str = ".globl tohost\ntohost: .dword 0\n.globl fromhost\nfromhost: .dword 0\n.globl begin_signature\nbegin_signature:\n";

fn sail() -> Option<String> {
    let sim = std::env::var("SAIL_RISCV_SIM").unwrap_or_else(|_| "sail_riscv_sim".into());
    Command::new(&sim)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|_| sim)
}

#[test]
fn lean_semantics_agree_with_sail() {
    let clang = tool("CLANG", &["clang"]);
    let lld = tool("LLD", &["ld.lld", "ld.lld-20", "ld.lld-19", "ld.lld-18"]);
    let lake = tool("LAKE", &["lake"]);
    let (Some(clang), Some(lld), Some(lake), Some(sim)) = (clang, lld, lake, sail()) else {
        eprintln!(
            "SKIPPED lean_semantics_agree_with_sail: needs clang, ld.lld, lake and SAIL_RISCV_SIM"
        );
        return;
    };
    let version =
        String::from_utf8_lossy(&Command::new(&sim).arg("--version").output().unwrap().stdout)
            .trim()
            .to_string();
    let n: u64 = std::env::var("E5R_SAIL_PROGRAMS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(48);
    let dir = std::env::temp_dir().join(format!("e5r-sail-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let ld = dir.join("link.ld");
    std::fs::write(&ld, LINK).unwrap();
    let mut lean = String::from("import E5R\nopen E5R\n\n");
    let mut want = Vec::new();
    for p in 0..n {
        let asm = dir.join(format!("p{p}.S"));
        let obj = dir.join(format!("p{p}.o"));
        let elf = dir.join(format!("p{p}.elf"));
        let sig = dir.join(format!("p{p}.sig"));
        // A different seed from the qemu test, so the two cover different programs.
        let mut src = program(1_000_000 + p, END, DATA);
        src.push_str(".globl end_signature\nend_signature:\n");
        std::fs::write(&asm, src).unwrap();
        let ok = Command::new(&clang)
            .args([
                "--target=riscv64-unknown-elf",
                "-march=rv64im_zba_zbb",
                "-mabi=lp64",
                "-mno-relax",
                "-c",
            ])
            .arg(&asm)
            .arg("-o")
            .arg(&obj)
            .status()
            .unwrap()
            .success();
        assert!(ok, "clang failed on {}", asm.display());
        let ok = Command::new(&lld)
            .args(["-static", "-e", "_start", "-T"])
            .arg(&ld)
            .arg(&obj)
            .arg("-o")
            .arg(&elf)
            .status()
            .unwrap()
            .success();
        assert!(ok, "ld.lld failed on {}", obj.display());
        let out = Command::new(&sim)
            .arg("--test-signature")
            .arg(&sig)
            .args(["--signature-granularity", "8", "--inst-limit", "100000"])
            .arg(&elf)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "sail failed on {}: {}",
            elf.display(),
            String::from_utf8_lossy(&out.stderr)
        );
        // One 64-bit word per line, most significant digit first; the
        // buffer's bytes are those words little-endian.
        let words = std::fs::read_to_string(&sig).unwrap();
        let mut hex = String::new();
        for w in words.lines() {
            let v = u64::from_str_radix(w.trim(), 16).unwrap();
            for b in v.to_le_bytes() {
                write!(hex, "{b:02x}").unwrap();
            }
        }
        assert_eq!(
            hex.len(),
            1024,
            "program {p}: the signature is not 512 bytes"
        );
        want.push(hex);

        let bytes = std::fs::read(&elf).unwrap();
        let bin = e5r::load(&bytes).expect("generated programs are RV64 without C");
        let e = e5r::elf::Elf::parse(&bytes).unwrap();
        let data = e.section(".data").expect(".data");
        let words: Vec<String> = bin.text.iter().map(|w| format!("0x{w:08x}#32")).collect();
        writeln!(
            lean,
            "def code{p} : Code := ⟨0x{:x}#64, #[{}]⟩",
            bin.text_addr,
            words.join(", ")
        )
        .unwrap();
        writeln!(
            lean,
            "def mem{p} : Word → Byte := memOf 0x{:x}#64 ({})",
            data.addr,
            lean_bytes(e.bytes(data))
        )
        .unwrap();
        writeln!(
            lean,
            "#eval IO.println (match runToEcall code{p} 100000 {{ regs := fun _ => 0, pc := 0x{:x}#64, mem := mem{p}, trace := [], exit := none }} with\n  | some s => s!\"P{p} \" ++ hexBytes (readBytes s.mem (s.reg 27) 512)\n  | none => \"P{p} FAULT\")\n",
            e.entry
        )
        .unwrap();
    }
    let file = dir.join("Sail.lean");
    std::fs::write(&file, &lean).unwrap();
    let out = Command::new(&lake)
        .args(["env", "lean"])
        .arg(&file)
        .current_dir(root().join("lean"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "lean failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let mut bad = Vec::new();
    for (p, w) in want.iter().enumerate() {
        let got = stdout
            .lines()
            .find_map(|l| l.strip_prefix(&format!("P{p} ")))
            .unwrap_or("missing");
        if got != w {
            bad.push(format!(
                "program {p} ({}): lean {}, sail {}",
                dir.join(format!("p{p}.S")).display(),
                &got[..got.len().min(80)],
                &w[..80]
            ));
        }
    }
    eprintln!("{n} programs compared with {version}");
    assert!(
        bad.is_empty(),
        "{} programs differ:\n{}",
        bad.len(),
        bad.join("\n")
    );
    let _ = std::fs::remove_dir_all(&dir);
}
