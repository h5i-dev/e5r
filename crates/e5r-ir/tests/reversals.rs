//! The byte and bit reversals, checked against this processor.
//!
//! The IR has no operation that reverses bytes or bits, so the lifter writes
//! each out as shifts and masks. That expansion is exact rather than
//! approximate, which is the only reason it is allowed to exist, and the only
//! way to be sure of it is to run the instruction.
//!
//! No portable C expression compiles to `rbit`, and the loop that computes the
//! same thing vectorizes instead, so the portable driver cannot reach it. This
//! assembles the instructions directly and runs them, which is a stronger
//! oracle anyway: nothing here is an expectation written by hand.

use std::process::Command;

use e5r_core::{Addr, Arch};
use e5r_ir::interp::{Step, step};
use e5r_ir::{Machine, lift};

/// The values to try. The edges first, because a mask written one bit wide
/// shows there and nowhere else.
const INPUTS: [u64; 10] = [
    0,
    1,
    0xffff_ffff_ffff_ffff,
    0x0123_4567_89ab_cdef,
    0x8000_0000_0000_0000,
    0x0000_0000_0000_00ff,
    0xff00_0000_0000_0000,
    0xdead_beef_cafe_babe,
    0x5555_5555_5555_5555,
    0x8000_0001,
];

/// Assemble one instruction and hand back its four bytes.
fn assemble(text: &str) -> Option<[u8; 4]> {
    let dir = std::env::temp_dir().join(format!("e5r-rev-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("a.s");
    let obj = dir.join("a.o");
    std::fs::write(&src, format!("{text}\n")).ok()?;
    let ok = Command::new("as")
        .arg("-o")
        .arg(&obj)
        .arg(&src)
        .status()
        .ok()?;
    if !ok.success() {
        return None;
    }
    let out = Command::new("objdump")
        .args(["-d", "--show-raw-insn"])
        .arg(&obj)
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let hex = text
        .lines()
        .find_map(|l| l.split_once(":\t")?.1.split_whitespace().next())
        .filter(|h| h.len() == 8)?;
    let word = u32::from_str_radix(hex, 16).ok()?;
    let _ = std::fs::remove_dir_all(&dir);
    Some(word.to_le_bytes())
}

/// Run one instruction on this processor, with `x0` set, and read `x0` back.
fn on_hardware(text: &str, inputs: &[u64]) -> Option<Vec<u64>> {
    let dir = std::env::temp_dir().join(format!("e5r-revrun-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("m.c");
    let bin = dir.join("m");
    let mut body = String::from("#include <stdio.h>\n#include <stdint.h>\nint main(void){\n");
    body.push_str("  uint64_t v;\n");
    for v in inputs {
        body.push_str(&format!(
            "  __asm__ volatile(\"{text}\" : \"=r\"(v) : \"r\"((uint64_t){v}ULL));\n  printf(\"%llu\\n\", (unsigned long long)v);\n"
        ));
    }
    body.push_str("  return 0;\n}\n");
    std::fs::write(&src, body).ok()?;
    let built = Command::new("cc")
        .arg("-O0")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .output()
        .ok()?;
    if !built.status.success() {
        return None;
    }
    let ran = Command::new(&bin).output().ok()?;
    let _ = std::fs::remove_dir_all(&dir);
    Some(
        String::from_utf8_lossy(&ran.stdout)
            .lines()
            .filter_map(|l| l.trim().parse().ok())
            .collect(),
    )
}

/// Lift one instruction, run it in the interpreter with `x0` set, read `x0`.
fn interpreted(bytes: &[u8; 4], input: u64) -> Option<u64> {
    let at = Addr(0x1000);
    let insn = e5r_arch::aarch64::decode(bytes, at)?;
    let lifted = lift::aarch64::lift(&insn);
    assert!(
        lifted.complete,
        "{} is not modelled, so there is nothing to check",
        e5r_arch::format(&Arch::AArch64, &insn, false)
    );
    let mut m = Machine::new();
    let x0 = e5r_ir::lift::aarch64::gpr_offset(0);
    let x1 = e5r_ir::lift::aarch64::gpr_offset(1);
    m.set_reg(x1, 8, input);
    for op in &lifted.ops {
        if !matches!(step(&mut m, op), Step::Next) {
            return None;
        }
    }
    Some(m.reg(x0, 8))
}

#[test]
fn the_reversals_do_what_this_processor_does() {
    if !cfg!(target_arch = "aarch64") {
        return; // the hardware oracle is this host
    }
    // `%0` is the output and `%1` the input, in the order the harness writes
    // them, so each of these is "reverse x1 into x0".
    let cases = [
        ("rbit %0, %1", "rbit x0, x1"),
        ("rev %0, %1", "rev x0, x1"),
        ("rev16 %0, %1", "rev16 x0, x1"),
        ("rev32 %0, %1", "rev32 x0, x1"),
        ("rev %w0, %w1", "rev w0, w1"),
        ("rbit %w0, %w1", "rbit w0, w1"),
        ("rev16 %w0, %w1", "rev16 w0, w1"),
    ];
    let mut checked = 0;
    for (asm, plain) in cases {
        let Some(bytes) = assemble(plain) else {
            return; // no assembler here
        };
        let Some(real) = on_hardware(asm, &INPUTS) else {
            return; // no compiler here
        };
        assert_eq!(real.len(), INPUTS.len(), "{plain}: the harness lost a case");
        for (input, want) in INPUTS.iter().zip(&real) {
            let got = interpreted(&bytes, *input).expect("the interpreter stopped");
            // A 32-bit form leaves the top half zero, which the hardware
            // answer already reflects, so nothing is masked here.
            assert_eq!(
                got, *want,
                "{plain} on {input:#x}: the processor says {want:#x}, the lifter says {got:#x}"
            );
            checked += 1;
        }
    }
    assert!(checked >= 70, "only {checked} comparisons ran");
    eprintln!("{checked} reversal results match this processor");
}
