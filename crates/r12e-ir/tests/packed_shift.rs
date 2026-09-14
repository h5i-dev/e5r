//! The packed shifts with a register count, checked against a processor.
//!
//! Shifting a vector lane by a count held in another vector has a rule the
//! arithmetic does not: a count at or above the lane's width gives zero rather
//! than wrapping. The lifter writes that out as a mask, and a mask derived
//! from a manual is an assertion until something runs it.
//!
//! This host is aarch64, so the x86-64 side runs under qemu, which is how the
//! rest of the lifter's hardware oracle already works.

use std::process::Command;

use r12e_core::{Addr, Arch};
use r12e_ir::interp::{Step, step};
use r12e_ir::{Machine, lift};

/// Counts either side of every lane width that matters, so the rule is
/// exercised in range, at the boundary and past it.
const COUNTS: [u64; 8] = [0, 1, 15, 16, 31, 32, 63, 64];

fn tool(name: &str) -> Option<String> {
    Command::new(name)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|_| name.to_string())
}

/// Build a program that runs one instruction per count and prints both lanes.
///
/// Written as inline assembly rather than an intrinsic so the instruction
/// under test is the one that runs, not whatever a header expands to.
fn on_hardware(insn: &str, value: u64) -> Option<Vec<(u64, u64)>> {
    // Inside inline assembly a register's percent has to be doubled, while
    // the assembler wants it single, so one form is written and doubled here.
    let insn = insn.replace('%', "%%");
    let insn = insn.as_str();
    let cc = tool("clang")?;
    let qemu = tool("qemu-x86_64").or_else(|| tool("qemu-x86_64-static"))?;
    // A test runs with its crate as the working directory, not the workspace.
    let lld = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build/ld");
    if !lld.join("ld.lld").exists() {
        return None; // the corpus has not been built
    }
    let dir = std::env::temp_dir().join(format!("r12e-psh-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("m.c");
    let bin = dir.join("m");
    // Freestanding, because this host has no x86-64 libc headers: the results
    // go out through a raw write and the program exits with a raw syscall.
    let mut body = String::from(
        "typedef unsigned long long u64;\n\
         /* -O0 turns an array initializer into a call to this, and there is\n\
            no library here to provide it. */\n\
         void *memset(void *d, int c, unsigned long n) {\n\
           unsigned char *p = d;\n\
           while (n--) *p++ = (unsigned char)c;\n\
           return d;\n\
         }\n\
         static void put(const void *p, u64 n) {\n\
           __asm__ volatile(\"syscall\" :: \"a\"(1ULL), \"D\"(1ULL), \"S\"(p), \"d\"(n)\n\
             : \"rcx\", \"r11\", \"memory\");\n\
         }\n\
         void _start(void) {\n\
           u64 out[2];\n",
    );
    for c in COUNTS {
        body.push_str(&format!(
            "  {{ u64 v[2] = {{ {value}ULL, {value}ULL }}, k[2] = {{ {c}ULL, 0 }};\n\
             \x20   __asm__ volatile(\"movdqu %2, %%xmm0\\n\\tmovdqu %3, %%xmm1\\n\\t{insn}\\n\\tmovdqu %%xmm0, %0\\n\\tmovdqu %%xmm0, %1\"\n\
             \x20     : \"=m\"(out[0]), \"=m\"(out[1]) : \"m\"(v[0]), \"m\"(k[0]) : \"xmm0\", \"xmm1\", \"memory\");\n\
             \x20   put(out, 16); }}\n"
        ));
    }
    body.push_str(
        "  __asm__ volatile(\"syscall\" :: \"a\"(60ULL), \"D\"(0ULL));\n\
         }\n",
    );
    std::fs::write(&src, body).ok()?;
    let built = Command::new(&cc)
        .args([
            "--target=x86_64-unknown-linux-gnu",
            "-O0",
            "-static",
            "-nostdlib",
            "-ffreestanding",
        ])
        .arg(format!("-B{}", lld.display()))
        .arg("-fuse-ld=lld")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .output()
        .ok()?;
    if !built.status.success() {
        return None;
    }
    let ran = Command::new(&qemu).arg(&bin).output().ok()?;
    let _ = std::fs::remove_dir_all(&dir);
    // Two little endian words per case, written straight out.
    let raw = ran.stdout;
    if raw.len() != COUNTS.len() * 16 {
        return None;
    }
    Some(
        raw.chunks_exact(16)
            .map(|c| {
                (
                    u64::from_le_bytes(c[..8].try_into().unwrap()),
                    u64::from_le_bytes(c[8..].try_into().unwrap()),
                )
            })
            .collect(),
    )
}

/// Assemble one x86-64 instruction and hand back its bytes.
fn assemble(text: &str) -> Option<Vec<u8>> {
    let cc = tool("clang")?;
    let dir = std::env::temp_dir().join(format!("r12e-pshasm-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("a.s");
    let obj = dir.join("a.o");
    std::fs::write(&src, format!(".text\n{text}\n")).ok()?;
    let ok = Command::new(&cc)
        .args(["--target=x86_64-unknown-linux-gnu", "-c", "-o"])
        .arg(&obj)
        .arg(&src)
        .status()
        .ok()?;
    if !ok.success() {
        return None;
    }
    let out = Command::new("llvm-objdump-18")
        .args(["-d", "--x86-asm-syntax=intel"])
        .arg(&obj)
        .output()
        .or_else(|_| {
            Command::new("llvm-objdump")
                .args(["-d", "--x86-asm-syntax=intel"])
                .arg(&obj)
                .output()
        })
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    // "       0: 66 0f d3 c1   \tpsrlq\txmm0, xmm1": the bytes sit between the
    // colon and the first tab.
    let hex = text.lines().find_map(|l| {
        let after = l.split_once(':')?.1.split('\t').next()?.trim();
        // The header line also has a colon and nothing useful after it.
        (!after.is_empty()).then_some(after)
    })?;
    let _ = std::fs::remove_dir_all(&dir);
    hex.split_whitespace()
        .map(|b| u8::from_str_radix(b, 16).ok())
        .collect()
}

/// Lift one instruction, set xmm0 to `value` in both lanes and xmm1 to the
/// count, run it, and read both lanes of xmm0 back.
fn interpreted(bytes: &[u8], value: u64, count: u64) -> Option<(u64, u64)> {
    let insn = r12e_arch::x86::decode(bytes, Addr(0x1000))?;
    let lifted = lift::x86::lift(&insn);
    assert!(
        lifted.complete,
        "{} is not modelled",
        r12e_arch::format(&Arch::X86_64, &insn, false)
    );
    let mut m = Machine::new();
    let v = lift::x86::vec_offset(0);
    let k = lift::x86::vec_offset(1);
    m.set_reg(v, 8, value);
    m.set_reg(v + 8, 8, value);
    m.set_reg(k, 8, count);
    m.set_reg(k + 8, 8, 0);
    for op in &lifted.ops {
        if !matches!(step(&mut m, op), Step::Next) {
            return None;
        }
    }
    Some((m.reg(v, 8), m.reg(v + 8, 8)))
}

#[test]
fn a_packed_shift_by_a_register_does_what_the_processor_does() {
    const VALUE: u64 = 0x0123_4567_89ab_cdef;
    let cases = [
        ("psrlq %xmm1, %xmm0", "psrlq xmm0, xmm1"),
        ("psllq %xmm1, %xmm0", "psllq xmm0, xmm1"),
        ("psrld %xmm1, %xmm0", "psrld xmm0, xmm1"),
        ("pslld %xmm1, %xmm0", "pslld xmm0, xmm1"),
        ("psrlw %xmm1, %xmm0", "psrlw xmm0, xmm1"),
        ("psllw %xmm1, %xmm0", "psllw xmm0, xmm1"),
    ];
    let mut checked = 0;
    for (at_and_t, intel) in cases {
        let Some(bytes) = assemble(at_and_t) else {
            return; // no assembler or no objdump here
        };
        let Some(real) = on_hardware(at_and_t, VALUE) else {
            return; // no cross compiler, linker or qemu here
        };
        assert_eq!(real.len(), COUNTS.len(), "{intel}: the harness lost a case");
        for (count, want) in COUNTS.iter().zip(&real) {
            let got = interpreted(&bytes, VALUE, *count).expect("the interpreter stopped");
            assert_eq!(
                got.0, want.0,
                "{intel} by {count}: the processor says {:#x}, the lifter says {:#x}",
                want.0, got.0
            );
            checked += 1;
        }
    }
    assert!(checked >= 40, "only {checked} comparisons ran");
    eprintln!("{checked} packed shift results match the processor");
}
