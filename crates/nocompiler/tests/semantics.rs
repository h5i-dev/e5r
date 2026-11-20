//! The Lean semantics against the processor (CONTRIBUTING.md: an external
//! oracle wherever one exists).
//!
//! Random straight-line programs over every instruction of the profile, with
//! interesting operands (0, -1, 1, the extremes, random), are assembled with
//! clang, linked with ld.lld and run under qemu-riscv64. The same ELF is run
//! by the executable Lean semantics (`NoCompiler.runToEcall`, the `exec` every proof
//! is about). Both dump 512 bytes: a scratch area the program loaded from and
//! stored to, and every register. They must be identical.
//!
//! The same Lean run checks `NoCompiler.decode` against this crate's decoder on a
//! sample of the corpus `tests/decode.rs` checks against llvm-mc.
//!
//! Needs clang, ld.lld, qemu-riscv64 and lake (CLANG, LLD, QEMU_RISCV64,
//! LAKE override them); skips, loudly, when one is missing. NOCOMPILER_SEM_PROGRAMS
//! sets the number of programs (default 48).

mod common;
use common::*;
use std::fmt::Write as _;
use std::process::Command;

#[test]
fn lean_semantics_agree_with_qemu() {
    let clang = tool("CLANG", &["clang"]);
    let lld = tool("LLD", &["ld.lld", "ld.lld-20", "ld.lld-19", "ld.lld-18"]);
    let qemu = tool("QEMU_RISCV64", &["qemu-riscv64", "qemu-riscv64-static"]);
    let lake = tool("LAKE", &["lake"]);
    let (Some(clang), Some(lld), Some(qemu), Some(lake)) = (clang, lld, qemu, lake) else {
        eprintln!(
            "SKIPPED lean_semantics_agree_with_qemu: needs clang, ld.lld, qemu-riscv64 and lake"
        );
        return;
    };
    let n: u64 = std::env::var("NOCOMPILER_SEM_PROGRAMS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(48);
    let dir = std::env::temp_dir().join(format!("nocompiler-semantics-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut lean = String::from("import NoCompiler\nopen NoCompiler\n\n");
    let mut want = Vec::new();
    for p in 0..n {
        let asm = dir.join(format!("p{p}.S"));
        let obj = dir.join(format!("p{p}.o"));
        let elf = dir.join(format!("p{p}.elf"));
        std::fs::write(
            &asm,
            program(
                p,
                "  li a7, 64\n  li a0, 1\n  mv a1, s11\n  li a2, 512\n  ecall\n  li a7, 93\n  li a0, 0\n  ecall\n",
                "",
            ),
        )
        .unwrap();
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
            .args(["-static", "-e", "_start"])
            .arg(&obj)
            .arg("-o")
            .arg(&elf)
            .status()
            .unwrap()
            .success();
        assert!(ok, "ld.lld failed on {}", obj.display());
        let out = Command::new(&qemu).arg(&elf).output().unwrap();
        assert!(out.status.success(), "qemu failed on {}", elf.display());
        assert_eq!(
            out.stdout.len(),
            512,
            "program {p} wrote {} bytes",
            out.stdout.len()
        );
        want.push(
            out.stdout
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>(),
        );

        let bytes = std::fs::read(&elf).unwrap();
        let bin = nocompiler::load(&bytes).expect("generated programs are RV64 without C");
        let e = nocompiler::elf::Elf::parse(&bytes).unwrap();
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
    // Decoder cross-check: about 300 words per major opcode, spread over the
    // other 25 bits, in chunks small enough to elaborate quickly.
    let mut cases = Vec::new();
    for opc in [
        0x13u32, 0x1b, 0x03, 0x23, 0x33, 0x3b, 0x63, 0x67, 0x73, 0x37, 0x17, 0x6f,
    ] {
        for x in (0..(1u32 << 25)).step_by(111_863) {
            let w = opc | x << 7;
            cases.push(match nocompiler::isa::decode(w) {
                Some(i) => format!("(0x{w:08x}#32, some ({}))", i.lean()),
                None => format!("(0x{w:08x}#32, none)"),
            });
        }
    }
    let chunks: Vec<&[String]> = cases.chunks(64).collect();
    for (k, c) in chunks.iter().enumerate() {
        writeln!(
            lean,
            "def dcases{k} : List (BitVec 32 × Option Instr) := [\n  {}]",
            c.join(",\n  ")
        )
        .unwrap();
    }
    let all: Vec<String> = (0..chunks.len()).map(|k| format!("dcases{k}")).collect();
    writeln!(
        lean,
        "def dcases : List (BitVec 32 × Option Instr) := {}",
        all.join(" ++ ")
    )
    .unwrap();
    writeln!(lean, "#eval IO.println s!\"DECODE {{(dcases.filter fun (w, e) => decode w != e).length}} of {{dcases.length}}\"").unwrap();
    let file = dir.join("Semantics.lean");
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
                "program {p} ({}): lean {}, qemu {}",
                dir.join(format!("p{p}.S")).display(),
                &got[..got.len().min(80)],
                &w[..80]
            ));
        }
    }
    let decode_line = stdout
        .lines()
        .find(|l| l.starts_with("DECODE"))
        .unwrap_or("DECODE missing");
    eprintln!("{n} programs compared; {decode_line}");
    assert!(
        decode_line.starts_with("DECODE 0 of"),
        "the Lean and Rust decoders disagree: {decode_line}"
    );
    assert!(
        bad.is_empty(),
        "{} programs differ:\n{}",
        bad.len(),
        bad.join("\n")
    );
    let _ = std::fs::remove_dir_all(&dir);
}
