//! The simulated performance oracle (`nocompiler::sim`, docs/isa/sim.md)
//! against qemu-riscv64:
//!
//! * semantics: random programs over every instruction of the profile (the
//!   generator of tests/semantics.rs) dump their registers and a scratch area;
//!   the simulator's dump must be qemu's, byte for byte;
//! * instruction counts: on the same programs and on the demo's COBS test
//!   driver, the simulator's count must be the number of instructions qemu
//!   executes (`-one-insn-per-tb -d exec,nochain`: one log line per
//!   instruction);
//! * whole programs: the COBS driver on random inputs gives qemu's output and
//!   exit status.
//!
//! Needs clang, ld.lld and qemu-riscv64 8.0 or later; skips, loudly, without
//! them. (qemu 7.2 computes `ctzw` of a value whose low 32 bits are zero as
//! the 64-bit count, 63 for 1<<63; the RISC-V specification, the Lean
//! semantics and qemu 8.2 give 32.)

/// qemu 8.0 or later (see above).
fn qemu_ok(qemu: &str) -> bool {
    let v = Command::new(qemu).arg("--version").output().unwrap();
    let s = String::from_utf8_lossy(&v.stdout).to_string();
    let major = s
        .split("version ")
        .nth(1)
        .and_then(|v| v.split('.').next())
        .and_then(|m| m.parse::<u32>().ok());
    if major.is_some_and(|m| m >= 8) {
        return true;
    }
    eprintln!(
        "SKIPPED: {qemu} is {}; needs 8.0 or later (ctzw)",
        s.lines().next().unwrap_or("?")
    );
    false
}

mod common;
use common::*;
use std::process::Command;

fn qemu_count(qemu: &str, elf: &std::path::Path, input: &[u8], dir: &std::path::Path) -> u64 {
    let log = dir.join("exec.log");
    // `-one-insn-per-tb` since qemu 8.1; `-singlestep` before.
    let help = Command::new(qemu).arg("-h").output().unwrap();
    let flag = if String::from_utf8_lossy(&help.stdout).contains("one-insn-per-tb") {
        "-one-insn-per-tb"
    } else {
        "-singlestep"
    };
    let mut c = Command::new(qemu)
        .args([flag, "-d", "exec,nochain", "-D"])
        .arg(&log)
        .arg(elf)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .spawn()
        .unwrap();
    use std::io::Write as _;
    c.stdin.take().unwrap().write_all(input).unwrap();
    c.wait().unwrap();
    let n = std::fs::read_to_string(&log)
        .unwrap()
        .lines()
        .filter(|l| l.starts_with("Trace"))
        .count() as u64;
    let _ = std::fs::remove_file(&log);
    n
}

#[test]
fn simulator_agrees_with_qemu() {
    let clang = tool("CLANG", &["clang"]);
    let lld = tool("LLD", &["ld.lld", "ld.lld-20", "ld.lld-19", "ld.lld-18"]);
    let qemu = tool("QEMU_RISCV64", &["qemu-riscv64", "qemu-riscv64-static"]);
    let (Some(clang), Some(lld), Some(qemu)) = (clang, lld, qemu) else {
        eprintln!("SKIPPED simulator_agrees_with_qemu: needs clang, ld.lld and qemu-riscv64");
        return;
    };
    if !qemu_ok(&qemu) {
        return;
    }
    let m = nocompiler::sim::Model::inorder5();
    let dir = std::env::temp_dir().join(format!("nocompiler-sim-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let n: u64 = std::env::var("NOCOMPILER_SIM_PROGRAMS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(200);
    for p in 0..n {
        let asm = dir.join(format!("p{p}.S"));
        let obj = dir.join(format!("p{p}.o"));
        let elf = dir.join(format!("p{p}.elf"));
        std::fs::write(
            &asm,
            program(p, "  li a7, 64\n  li a0, 1\n  mv a1, s11\n  li a2, 512\n  ecall\n  li a7, 93\n  li a0, 0\n  ecall\n", ""),
        )
        .unwrap();
        assert!(
            Command::new(&clang)
                .args([
                    "--target=riscv64-unknown-elf",
                    "-march=rv64im_zba_zbb",
                    "-mabi=lp64",
                    "-mno-relax",
                    "-c"
                ])
                .arg(&asm)
                .arg("-o")
                .arg(&obj)
                .status()
                .unwrap()
                .success()
        );
        assert!(
            Command::new(&lld)
                .args(["-static", "-e", "_start"])
                .arg(&obj)
                .arg("-o")
                .arg(&elf)
                .status()
                .unwrap()
                .success()
        );
        let want = Command::new(&qemu).arg(&elf).output().unwrap();
        let bytes = std::fs::read(&elf).unwrap();
        let mut got = Vec::new();
        let r = nocompiler::sim::run(&bytes, &[], &mut got, &m, 100_000).unwrap();
        assert_eq!(r.exit, Some(0), "program {p}: {:?}", r.fault);
        assert_eq!(
            got, want.stdout,
            "program {p}: the dump differs from qemu's"
        );
        if p < 20 {
            assert_eq!(
                r.instructions,
                qemu_count(&qemu, &elf, &[], &dir),
                "program {p}: instruction count"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn cobs_driver_agrees_with_qemu() {
    let qemu = tool("QEMU_RISCV64", &["qemu-riscv64", "qemu-riscv64-static"]);
    let Some(qemu) = qemu else {
        eprintln!("SKIPPED cobs_driver_agrees_with_qemu: needs qemu-riscv64");
        return;
    };
    if !qemu_ok(&qemu) {
        return;
    }
    let dir = std::env::temp_dir().join(format!("nocompiler-sim-cobs-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // The test driver of the demo (examples/demo/src/cobs_test_main.c), built
    // as examples/demo/build.sh builds it.
    let elf = dir.join("cobs_test.elf");
    let srcs = [
        "examples/demo/src/cobs.c",
        "examples/demo/src/cobs_test_main.c",
    ];
    let args: Vec<String> = srcs
        .iter()
        .map(|s| root().join(s).display().to_string())
        .collect();
    if nocompiler::cc::build(&args, &elf).is_err() || !elf.exists() {
        eprintln!("SKIPPED cobs_driver_agrees_with_qemu: nocompiler cc could not build the driver");
        return;
    }
    let bytes = std::fs::read(&elf).unwrap();
    let m = nocompiler::sim::Model::inorder5();
    let mut seed = 0x2545f4914f6cdd1du64;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for k in 0..40 {
        // Records as the driver reads them: u64 length, then the bytes.
        let mut input = Vec::new();
        for _ in 0..(1 + k % 4) {
            let n = (next() % 300) as usize;
            input.extend_from_slice(&(n as u64).to_le_bytes());
            for _ in 0..n {
                let b = next() as u8;
                input.push(if b % 5 == 0 { 0 } else { b });
            }
        }
        let mut q = Command::new(&qemu)
            .arg(&elf)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        use std::io::Write as _;
        q.stdin.take().unwrap().write_all(&input).unwrap();
        let want = q.wait_with_output().unwrap();
        let mut got = Vec::new();
        let r = nocompiler::sim::run(&bytes, &input, &mut got, &m, 100_000_000).unwrap();
        assert_eq!(got, want.stdout, "input {k}: output");
        assert_eq!(
            r.exit.map(|c| c as i32),
            want.status.code(),
            "input {k}: exit status ({:?})",
            r.fault
        );
        if k < 5 {
            assert_eq!(
                r.instructions,
                qemu_count(&qemu, &elf, &input, &dir),
                "input {k}: instruction count"
            );
        }
        assert!(r.cycles >= r.instructions);
    }
    let _ = std::fs::remove_dir_all(&dir);
}
