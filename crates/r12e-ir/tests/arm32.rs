//! The ARM32 lifter measured against a processor.
//!
//! This host is aarch64, which does not run A32 code, so the ARM side runs
//! under qemu -- the way the rest of the lifter's hardware oracle already
//! works. Nothing below is an assertion about what the lifter ought to do:
//! every expected value came out of a processor.
//!
//! The cases are the ones where this architecture differs from every other the
//! lifter covers: the barrel shifter on the second operand and the carry it
//! leaves behind, predication as part of the mnemonic, and the load and store
//! multiple forms that move a frame in one instruction.

use std::process::Command;

use r12e_core::{Addr, Arch};
use r12e_ir::interp::{Step, step};
use r12e_ir::{Machine, lift};

/// Where the interpreted machine's stack goes.
const STACK: u64 = 0x4000_0000;

/// One case: a name, and assembly that leaves its answer in `r0`.
///
/// `sp` is the harness's, so a case that moves it has to put it back. The
/// push and pop cases do exactly that, which is the point of testing them.
const CASES: &[(&str, &str)] = &[
    // The barrel shifter on the second operand, which no other architecture
    // the lifter covers has.
    (
        "shifted_add",
        "mov r1, #5\n mov r2, #3\n add r0, r1, r2, lsl #4\n",
    ),
    (
        "shifted_sub",
        "mov r1, #100\n mov r2, #8\n sub r0, r1, r2, lsr #2\n",
    ),
    (
        "shifted_asr",
        "mvn r1, #0\n mov r2, #0\n add r0, r2, r1, asr #4\n",
    ),
    (
        "shifted_ror",
        "mov r1, #0xff\n mov r2, #0\n add r0, r2, r1, ror #4\n",
    ),
    // The carry the shifter leaves, which is not the carry out of the
    // arithmetic and which `adc` then reads.
    (
        "shifter_carry",
        "mov r1, #0x80000000\n movs r2, r1, lsl #1\n mov r0, #0\n adc r0, r0, #0\n",
    ),
    (
        "shifter_carry_lsr",
        "mov r1, #3\n movs r2, r1, lsr #1\n mov r0, #0\n adc r0, r0, #0\n",
    ),
    (
        "rrx_through_carry",
        "mov r1, #1\n movs r2, r1, lsr #1\n mov r0, #0\n rrx r0, r0\n",
    ),
    // Predication, which is part of the mnemonic and applies to almost
    // everything.
    (
        "predicated_taken",
        "mov r0, #1\n cmp r0, #1\n moveq r0, #0x55\n",
    ),
    (
        "predicated_skipped",
        "mov r0, #1\n cmp r0, #2\n moveq r0, #0x55\n",
    ),
    (
        "predicated_add",
        "mov r0, #10\n mov r1, #3\n cmp r1, #3\n addeq r0, r0, #7\n addne r0, r0, #100\n",
    ),
    (
        "predicated_signed",
        "mov r0, #0\n mov r1, #1\n cmn r1, #2\n movlt r0, #1\n movge r0, #2\n",
    ),
    // The flags themselves, at a 32-bit width.
    (
        "carry_out",
        "mvn r1, #0\n adds r1, r1, #1\n mov r0, #0\n adc r0, r0, #0\n",
    ),
    (
        "borrow_out",
        "mov r1, #1\n subs r1, r1, #2\n mov r0, #0\n adc r0, r0, #0\n",
    ),
    (
        "overflow_set",
        "mov r1, #0x80000000\n subs r1, r1, #1\n mov r0, #0\n movvs r0, #1\n",
    ),
    // push and pop, which move several registers and the stack in one go.
    (
        "push_pop",
        "mov r4, #0x11\n mov r5, #0x22\n push {r4, r5}\n mov r4, #0\n mov r5, #0\n pop {r4, r5}\n add r0, r4, r5\n",
    ),
    (
        "push_order",
        "mov r4, #0x10\n mov r5, #0x20\n push {r4, r5}\n ldr r0, [sp]\n add sp, sp, #8\n",
    ),
    // Multiplies, including the long forms that write two registers.
    ("mul_wraps", "mov r1, #0x10000\n mul r0, r1, r1\n"),
    ("umull_high", "mov r1, #0x10000\n umull r2, r0, r1, r1\n"),
    (
        "smull_negative",
        "mvn r1, #0\n mov r2, #2\n smull r3, r0, r1, r2\n",
    ),
    (
        "mla_accumulates",
        "mov r1, #3\n mov r2, #4\n mov r3, #5\n mla r0, r1, r2, r3\n",
    ),
    // Extensions and the bit operations.
    ("uxtb_keeps_low", "mvn r1, #0\n uxtb r0, r1\n"),
    ("sxtb_extends", "mov r1, #0xff\n sxtb r0, r1\n"),
    ("clz_counts", "mov r1, #0x8000\n clz r0, r1\n"),
    ("rev_swaps", "ldr r1, =0x11223344\n rev r0, r1\n"),
    ("rbit_reverses", "mov r1, #1\n rbit r0, r1\n"),
    (
        "ubfx_extracts",
        "ldr r1, =0x12345678\n ubfx r0, r1, #4, #8\n",
    ),
    (
        "bfi_inserts",
        "ldr r0, =0x12345678\n mov r1, #0xf\n bfi r0, r1, #8, #4\n",
    ),
    // Loads and stores, including the writeback the addressing modes have.
    (
        "store_load",
        "sub sp, sp, #16\n ldr r1, =0xdeadbeef\n str r1, [sp, #4]\n ldr r0, [sp, #4]\n add sp, sp, #16\n",
    ),
    (
        "post_index",
        "sub sp, sp, #16\n mov r1, #7\n mov r2, sp\n str r1, [r2], #4\n sub r0, r2, sp\n add sp, sp, #16\n",
    ),
    (
        "byte_load_zero",
        "sub sp, sp, #16\n mvn r1, #0\n str r1, [sp]\n ldrb r0, [sp]\n add sp, sp, #16\n",
    ),
    (
        "byte_load_signed",
        "sub sp, sp, #16\n mvn r1, #0\n str r1, [sp]\n ldrsb r0, [sp]\n add sp, sp, #16\n",
    ),
    (
        "scaled_index",
        "sub sp, sp, #32\n mov r1, #0x99\n mov r2, #2\n str r1, [sp, r2, lsl #2]\n ldr r0, [sp, #8]\n add sp, sp, #32\n",
    ),
];

/// Thumb-specific cases, which A32 cannot express.
///
/// The narrow encodings write back into the first source and name it once, the
/// wide ones carry a `.w`, and an IT block makes the instructions after it
/// conditional with nothing in their own halfwords saying so -- the decoder
/// has to carry that state from one to the next, and this is what says it does.
const THUMB_CASES: &[(&str, &str)] = &[
    (
        "two_operand_add",
        "movs r0, #10\n movs r1, #7\n adds r0, r1\n",
    ),
    (
        "two_operand_sub",
        "movs r0, #10\n movs r1, #7\n subs r0, r1\n",
    ),
    (
        "two_operand_shift",
        "movs r0, #1\n movs r1, #4\n lsls r0, r1\n",
    ),
    (
        "two_operand_ror",
        "ldr r0, =0x12345678\n movs r1, #4\n rors r0, r1\n",
    ),
    ("wide_add", "movs r1, #5\n add.w r0, r1, #0x1000\n"),
    (
        "wide_load",
        "sub sp, #16\n ldr r1, =0xcafe\n str.w r1, [sp, #4]\n ldr.w r0, [sp, #4]\n add sp, #16\n",
    ),
    // An IT block: the instructions after it are conditional and their own
    // halfwords do not say so.
    (
        "it_taken",
        "movs r0, #1\n cmp r0, #1\n itt eq\n moveq r0, #0x33\n addeq r0, #1\n",
    ),
    (
        "it_skipped",
        "movs r0, #1\n cmp r0, #2\n itt eq\n moveq r0, #0x33\n addeq r0, #1\n",
    ),
    (
        "it_else",
        "movs r0, #1\n cmp r0, #2\n ite eq\n moveq r0, #0x44\n movne r0, #0x55\n",
    ),
    (
        "it_four",
        "movs r0, #0\n cmp r0, #0\n itttt eq\n addeq r0, #1\n addeq r0, #2\n addeq r0, #4\n addeq r0, #8\n",
    ),
    // cbz and cbnz, which exist only in Thumb.
    (
        "cbz_taken",
        "movs r0, #0\n cbz r0, 1f\n movs r0, #0x99\n1:\n",
    ),
    (
        "cbnz_taken",
        "movs r0, #7\n cbnz r0, 1f\n movs r0, #0x99\n1:\n",
    ),
];

fn tool(name: &str) -> Option<String> {
    Command::new(name)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|_| name.to_string())
}

/// Run every case on a processor and hand back the `r0` each one leaves.
fn on_hardware(cases: &[(&str, &str)], thumb: bool) -> Option<Vec<u32>> {
    let cc = tool("clang")?;
    let qemu = tool("qemu-arm").or_else(|| tool("qemu-arm-static"))?;
    // A test runs with its crate as the working directory, not the workspace.
    let lld = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build/ld");
    if !lld.join("ld.lld").exists() {
        return None; // the corpus has not been built
    }
    // The two instruction sets are two tests and run at once, so the
    // directory is named for the set as well as the process.
    let set = if thumb { "t32" } else { "a32" };
    let dir = std::env::temp_dir().join(format!("r12e-arm32-{set}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("m.s");
    let bin = dir.join("m");

    // Written as assembly rather than C with inline assembly: this host has no
    // ARM libc headers, and the cases are assembly anyway. The results go out
    // through a raw `write` and the program exits with a raw `_exit`, both
    // through `svc #0` with the number in r7, which is how a 32-bit ARM
    // process reaches the kernel.
    let mut body = String::from(if thumb {
        ".text\n.thumb\n.syntax unified\n.globl _start\n.thumb_func\n_start:\n"
    } else {
        ".text\n.arm\n.globl _start\n_start:\n"
    });
    for (_, asm) in cases {
        body.push_str(asm);
        body.push_str("  ldr r4, =out\n  str r0, [r4]\n");
        body.push_str("  mov r7, #4\n  mov r0, #1\n  mov r1, r4\n  mov r2, #4\n  svc #0\n");
    }
    body.push_str("  mov r7, #1\n  mov r0, #0\n  svc #0\n");
    // One literal pool, after the last instruction and before the data. Not
    // one per case: `.ltorg` emits the constants where it stands, and a pool
    // in the middle of the text is executed as instructions on the way past.
    // The whole program is well inside the 4 KB a pc-relative load reaches.
    body.push_str("  .ltorg\n");
    body.push_str(".data\nout: .word 0\n");
    std::fs::write(&src, body).ok()?;

    let built = Command::new(&cc)
        .args([
            "--target=arm-unknown-linux-gnueabi",
            "-march=armv7-a",
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
    let raw = ran.stdout;
    if raw.len() != cases.len() * 4 {
        return None;
    }
    Some(
        raw.chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
            .collect(),
    )
}

/// Assemble one case, with its literal pool, and hand back the bytes and where
/// in them the instructions stop.
fn assemble(text: &str, thumb: bool) -> Option<(Vec<u8>, usize)> {
    let cc = tool("clang")?;
    let set = if thumb { "t32" } else { "a32" };
    let dir = std::env::temp_dir().join(format!("r12e-arm32asm-{set}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("a.s");
    let obj = dir.join("a.o");
    let bin = dir.join("a.bin");
    // A marker instruction after the case, so the interpreter knows where to
    // stop without having to tell an instruction from a literal.
    let head = if thumb {
        ".text\n.thumb\n.syntax unified\n"
    } else {
        ".text\n.arm\n"
    };
    std::fs::write(&src, format!("{head}{text}\n  udf.w #0xdead\n  .ltorg\n")).ok()?;
    let ok = Command::new(&cc)
        .args([
            "--target=arm-unknown-linux-gnueabi",
            "-march=armv7-a",
            "-c",
            "-o",
        ])
        .arg(&obj)
        .arg(&src)
        .status()
        .ok()?;
    if !ok.success() {
        return None;
    }
    let cut = Command::new("llvm-objcopy-18")
        .args(["-O", "binary", "--only-section=.text"])
        .arg(&obj)
        .arg(&bin)
        .status()
        .or_else(|_| {
            Command::new("llvm-objcopy")
                .args(["-O", "binary", "--only-section=.text"])
                .arg(&obj)
                .arg(&bin)
                .status()
        })
        .ok()?;
    if !cut.success() {
        return None;
    }
    let out = std::fs::read(&bin).ok()?;
    let _ = std::fs::remove_dir_all(&dir);
    // The marker: the wide `udf` is e7fdeafd on A32 and f7ff addead on Thumb,
    // both four bytes and neither a shape a case ends with.
    let want: [u8; 4] = if thumb {
        [0xfd, 0xf7, 0xad, 0xae]
    } else {
        [0xfd, 0xea, 0xfd, 0xe7]
    };
    let end = out.windows(4).position(|w| w == want)?;
    Some((out, end))
}

/// Decode, lift and run a case's bytes, and read `r0` back.
///
/// The image is placed where the assembler put it so a pc-relative literal
/// load reads the pool that follows the instructions.
fn interpreted(bytes: &[u8], end: usize, thumb: bool) -> Option<u32> {
    const BASE: u64 = 0x1000;
    let mut m = Machine::new();
    m.set_reg(lift::arm::sp_offset(), 4, STACK);
    m.write_mem(BASE, bytes);
    let mut at = 0usize;
    // Thumb's IT block predicates the instructions after it, and the state has
    // to be carried from one decode to the next exactly as the analysis does.
    let mut it = r12e_arch::arm::ItState::default();
    while at < end {
        let arch = if thumb { Arch::Thumb } else { Arch::Arm };
        let insn = if thumb {
            let (i, next) = r12e_arch::arm::decode_thumb(&bytes[at..], Addr(BASE + at as u64), it)?;
            it = next;
            i
        } else {
            r12e_arch::arm::decode(&bytes[at..], Addr(BASE + at as u64))?
        };
        let lifted = lift::arm::lift_mode(&insn, thumb);
        assert!(
            lifted.complete,
            "{} is not modelled",
            r12e_arch::format(&arch, &insn, false)
        );
        // A case may branch over an instruction, which `cbz` exists to do, so
        // a jump inside the run is followed rather than treated as the end.
        // An IT block does not branch: the decoder folds its condition into
        // the instructions after it, which is the state carried above.
        let mut jumped = None;
        for op in &lifted.ops {
            match step(&mut m, op) {
                Step::Next => {}
                Step::Jump(to) => {
                    jumped = Some(usize::try_from(to.get().checked_sub(BASE)?).ok()?);
                    break;
                }
                _ => return None,
            }
        }
        at = match jumped {
            Some(to) => to,
            None => at + insn.len as usize,
        };
    }
    Some(m.reg(lift::arm::gpr_offset(0), 4) as u32)
}

#[test]
fn the_arm32_lifter_computes_what_the_processor_computes() {
    check(CASES, false, "A32");
}

#[test]
fn the_thumb_lifter_computes_what_the_processor_computes() {
    check(THUMB_CASES, true, "Thumb");
}

fn check(cases: &[(&str, &str)], thumb: bool, what: &str) {
    let Some(expected) = on_hardware(cases, thumb) else {
        return; // no clang, no qemu-arm, or the corpus has not been built
    };
    let mut checked = 0;
    for ((name, asm), want) in cases.iter().zip(expected) {
        // Not a silent skip: `on_hardware` has already built and run a
        // program with these same cases in it, so an assembler that cannot
        // assemble one of them now is a broken harness reporting a pass.
        let (bytes, end) =
            assemble(asm, thumb).unwrap_or_else(|| panic!("{name}: did not assemble"));
        let got = interpreted(&bytes, end, thumb).unwrap_or_else(|| panic!("{name}: did not run"));
        assert_eq!(
            got, want,
            "{name}: the processor says {want:#x}, the lifter says {got:#x}"
        );
        checked += 1;
    }
    assert_eq!(checked, cases.len());
    eprintln!("{checked} {what} case(s) agree with the processor");
}
