//! The i386 lifter measured against a processor.
//!
//! i386 and x86-64 are one decoder and, now, one lifter: the rules are the
//! same and the pointer is half as wide. That difference is not cosmetic --
//! every stack adjustment, return address and effective address is computed at
//! the narrower width, and 32-bit arithmetic wraps where 64-bit arithmetic
//! does not. So the cases here are the ones where the two modes disagree,
//! rather than a second pass over what the x86-64 oracle already covers.
//!
//! This host is aarch64, so the i386 side runs under qemu, which is how the
//! rest of the lifter's hardware oracle already works. Nothing below is an
//! assertion about what the lifter ought to do: every expected value came out
//! of a processor.

use std::process::Command;

use r12e_core::{Addr, Arch};
use r12e_ir::interp::{Step, step};
use r12e_ir::{Machine, lift};

/// Where the interpreted machine's stack goes, and where qemu will not put
/// anything of its own.
const STACK: u64 = 0x4000_0000;

/// One case: a name, and AT&T assembly that leaves its answer in `eax`.
///
/// `esp` is the harness's, so a case that moves it has to put it back. The
/// sequences that push do exactly that, which is the point of testing them.
const CASES: &[(&str, &str)] = &[
    // The arithmetic wraps at 32 bits, where the same lifter at 64 would not.
    ("add_wraps", "movl $0xffffffff, %eax\n addl $2, %eax\n"),
    ("sub_wraps", "movl $1, %eax\n subl $3, %eax\n"),
    ("imul_wraps", "movl $0x10000, %eax\n imull $0x10000, %eax\n"),
    ("neg_wraps", "movl $0, %eax\n negl %eax\n"),
    ("shl_drops", "movl $0x80000001, %eax\n shll $1, %eax\n"),
    ("sar_signed", "movl $0x80000000, %eax\n sarl $4, %eax\n"),
    ("shr_unsigned", "movl $0x80000000, %eax\n shrl $4, %eax\n"),
    // A push moves the stack by four, and the pop has to find the same place.
    (
        "push_pop",
        "movl $0x12345678, %eax\n pushl %eax\n xorl %eax, %eax\n popl %eax\n",
    ),
    (
        "push_order",
        "pushl $0x11111111\n pushl $0x22222222\n popl %eax\n addl (%esp), %eax\n addl $4, %esp\n",
    ),
    // An effective address computed at 32 bits, including the scaled index
    // form a compiler uses for array access.
    (
        "lea_scaled",
        "movl $0x1000, %eax\n movl $3, %ecx\n leal 8(%eax,%ecx,4), %eax\n",
    ),
    (
        "lea_wraps",
        "movl $0xfffffff0, %eax\n leal 0x20(%eax), %eax\n",
    ),
    // Flags, which 32-bit code branches on exactly as 64-bit code does but at
    // a different width: the sign bit is bit 31 here.
    (
        "sign_at_31",
        "movl $0x7fffffff, %eax\n addl $1, %eax\n setsb %al\n movzbl %al, %eax\n",
    ),
    (
        "carry_at_32",
        "movl $0xffffffff, %eax\n addl $1, %eax\n setcb %al\n movzbl %al, %eax\n",
    ),
    (
        "overflow_at_31",
        "movl $0x7fffffff, %eax\n addl $1, %eax\n setob %al\n movzbl %al, %eax\n",
    ),
    // `leave` is `mov esp, ebp; pop ebp` at the narrow width.
    (
        "leave_frame",
        "pushl %ebp\n movl %esp, %ebp\n subl $16, %esp\n movl $0xabcd, %eax\n leave\n",
    ),
    // A byte and a word destination leave the rest of the register alone,
    // which is the same rule as in long mode and is easy to get wrong when the
    // register file is modelled eight bytes wide and the machine is four.
    ("byte_dest", "movl $0x11223344, %eax\n movb $0x99, %al\n"),
    ("word_dest", "movl $0x11223344, %eax\n movw $0x9988, %ax\n"),
    ("movzx_byte", "movl $0xffffffff, %eax\n movzbl %al, %eax\n"),
    ("movsx_byte", "movl $0x000000ff, %eax\n movsbl %al, %eax\n"),
];

fn tool(name: &str) -> Option<String> {
    Command::new(name)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|_| name.to_string())
}

/// Run every case on a processor and hand back the `eax` each one leaves.
///
/// One program rather than one per case, because the build dominates and a
/// single run keeps the cases in step with the table above by construction.
fn on_hardware() -> Option<Vec<u32>> {
    let cc = tool("clang")?;
    let qemu = tool("qemu-i386").or_else(|| tool("qemu-i386-static"))?;
    // A test runs with its crate as the working directory, not the workspace.
    let lld = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build/ld");
    if !lld.join("ld.lld").exists() {
        return None; // the corpus has not been built
    }
    let dir = std::env::temp_dir().join(format!("r12e-i386-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("m.s");
    let bin = dir.join("m");

    // Written as assembly rather than C with inline assembly: this host has no
    // i386 libc headers, and the cases are assembly anyway. The results go out
    // through a raw `write` and the program exits with a raw `_exit`, both
    // through `int $0x80`, which is how a 32-bit process reaches the kernel.
    let mut body = String::from(".text\n.globl _start\n_start:\n");
    for (_, asm) in CASES {
        body.push_str(asm);
        // Keep the answer where the harness can find it, then print it. `eax`
        // is the syscall number, so the answer goes to memory first.
        body.push_str("  movl %eax, out\n");
        body.push_str(
            "  movl $4, %eax\n  movl $1, %ebx\n  movl $out, %ecx\n  movl $4, %edx\n  int $0x80\n",
        );
    }
    body.push_str("  movl $1, %eax\n  xorl %ebx, %ebx\n  int $0x80\n");
    body.push_str(".data\nout: .long 0\n");
    std::fs::write(&src, body).ok()?;

    let built = Command::new(&cc)
        .args([
            "--target=i386-unknown-linux-gnu",
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
    if raw.len() != CASES.len() * 4 {
        return None;
    }
    Some(
        raw.chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
            .collect(),
    )
}

/// Assemble one case and hand back its bytes.
fn assemble(text: &str) -> Option<Vec<u8>> {
    let cc = tool("clang")?;
    let dir = std::env::temp_dir().join(format!("r12e-i386asm-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("a.s");
    let obj = dir.join("a.o");
    let bin = dir.join("a.bin");
    std::fs::write(&src, format!(".text\n{text}\n")).ok()?;
    let ok = Command::new(&cc)
        .args(["--target=i386-unknown-linux-gnu", "-c", "-o"])
        .arg(&obj)
        .arg(&src)
        .status()
        .ok()?;
    if !ok.success() {
        return None;
    }
    // The bytes rather than a disassembly, because a case is several
    // instructions and reading them back out of a listing would re-parse what
    // the decoder is about to be handed.
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
    Some(out)
}

/// Decode, lift and run a case's bytes, and read `eax` back.
fn interpreted(bytes: &[u8]) -> Option<u32> {
    let mut m = Machine::new();
    m.set_reg(lift::x86::sp_offset(), 8, STACK);
    let mut at = 0usize;
    while at < bytes.len() {
        let insn = r12e_arch::x86::decode32(&bytes[at..], Addr(0x1000 + at as u64))?;
        let lifted = lift::x86::lift32(&insn);
        assert!(
            lifted.complete,
            "{} is not modelled",
            r12e_arch::format(&Arch::X86, &insn, false)
        );
        for op in &lifted.ops {
            if !matches!(step(&mut m, op), Step::Next) {
                return None;
            }
        }
        at += insn.len as usize;
    }
    Some(m.reg(lift::x86::gpr_offset(0), 4) as u32)
}

#[test]
fn the_i386_lifter_computes_what_the_processor_computes() {
    let Some(expected) = on_hardware() else {
        return; // no clang, no qemu-i386, or the corpus has not been built
    };
    let mut checked = 0;
    for ((name, asm), want) in CASES.iter().zip(expected) {
        let Some(bytes) = assemble(asm) else {
            return; // no assembler or no objcopy here
        };
        let got = interpreted(&bytes).unwrap_or_else(|| panic!("{name}: did not run"));
        assert_eq!(
            got, want,
            "{name}: the processor says {want:#x}, the lifter says {got:#x}"
        );
        checked += 1;
    }
    assert_eq!(checked, CASES.len());
    eprintln!("{checked} i386 case(s) agree with the processor");
}
