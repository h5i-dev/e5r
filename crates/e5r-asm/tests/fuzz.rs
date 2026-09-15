//! Mutation fuzzing of the assembler's text path, in the ordinary test run.
//!
//! Modelled on `e5r-format`'s loader fuzz for the same reason: a fuzz target
//! that needs nightly and a separate invocation finds nothing on a machine
//! where nobody runs it. The contract checked here is the one the error model
//! promises, and it is the whole reason the parser has its own bounds: given
//! any text at all, the assembler returns bytes or a typed error, and never
//! panics, hangs, or allocates from a number the text chose.

use std::time::{Duration, Instant};

use e5r_asm::{assemble, assemble_all, error::MAX_TEXT, pad, parse};
use e5r_core::{Addr, Arch};

/// How long each target gets. Enough to find a systematic fault, short enough
/// that nobody is tempted to skip the suite.
const BUDGET: Duration = Duration::from_millis(1200);

/// A small deterministic generator, so a failure is reproducible from its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

/// Real disassembly, which is what a user pastes in and therefore the only
/// interesting seed corpus.
const SEEDS: &[&str] = &[
    "mov\trax, rcx",
    "mov\teax, dword ptr [rbx + 4*rcx + 0x10]",
    "lea\trax, [rip + 0x2a]",
    "movabs\trax, 0x1122334455667788",
    "push\trbp",
    "jmp\t0x401000",
    "je\t0x401000",
    "call\t0x401000",
    "nop\tword ptr cs:[rax + rax]",
    "shl\teax, 0x3",
    "imul\teax, ecx, 0x10",
    "test\tbyte ptr [rdi], 0x1",
    "setne\tal",
    "movzx\teax, word ptr [rsi]",
    "rep\t\tstosq",
    "lock\tcmpxchg dword ptr [rdi], esi",
    "add\tx0, x1, x2, lsl #3",
    "ldr\tx0, [sp, #16]",
    "stp\tx29, x30, [sp, #-16]!",
    "ldrb\tw0, [x1, x2, sxtw #0]",
    "b.eq\t0x401000",
    "cbz\tx0, 0x401000",
    "tbnz\tw0, #3, 0x401000",
    "adrp\tx0, 0x402000",
    "movk\tw0, #0x5a5a, lsl #16",
    "ret",
    "svc\t#0",
    "bti\tc",
    "dmb\tish",
    "csel\tx0, x1, x2, eq",
    "ubfx\tx0, x1, #4, #8",
    "",
    "   \t  ",
    "# a comment only",
];

const BYTES: &[u8] = b"0123456789abcdefxyzXABCDEF[](),.:;#+-*!/%$_ \t\n\r\\\"'{}<>=|&^~?@`";

fn mutate(seed: &str, rng: &mut Rng) -> String {
    let mut v: Vec<u8> = seed.as_bytes().to_vec();
    match rng.below(7) {
        // Truncate, which is what a half-pasted line looks like.
        0 => {
            let n = if v.is_empty() { 0 } else { rng.below(v.len()) };
            v.truncate(n);
        }
        // Replace a byte with another printable one.
        1 if !v.is_empty() => {
            let i = rng.below(v.len());
            v[i] = *rng.pick(BYTES);
        }
        // Insert a byte.
        2 => {
            let i = rng.below(v.len() + 1);
            v.insert(i, *rng.pick(BYTES));
        }
        // Delete a byte.
        3 if !v.is_empty() => {
            let i = rng.below(v.len());
            v.remove(i);
        }
        // Repeat a run, which is how a number becomes enormous.
        4 if !v.is_empty() => {
            let i = rng.below(v.len());
            let n = rng.below(40);
            let b = v[i];
            for _ in 0..n {
                v.insert(i, b);
            }
        }
        // Splice two seeds together.
        5 => {
            v.extend_from_slice(b", ");
            v.extend_from_slice(rng.pick(SEEDS).as_bytes());
        }
        // Scramble, which reaches the shapes a targeted mutation never does.
        _ => {
            for b in v.iter_mut() {
                if rng.below(4) == 0 {
                    *b = *rng.pick(BYTES);
                }
            }
        }
    }
    String::from_utf8_lossy(&v).into_owned()
}

fn arches() -> [Arch; 2] {
    [Arch::X86_64, Arch::AArch64]
}

#[test]
fn mutated_assembly_text_never_panics() {
    let mut rng = Rng(0x5eed_1234_abcd_0101);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let text = mutate(rng.pick(SEEDS), &mut rng);
        let arch = arches()[rng.below(2)].clone();
        let at = Addr(rng.next());
        // The contract: bytes or a typed error, nothing else. A successful
        // encode has to fit the architecture's own limit.
        if let Ok(e) = assemble(&arch, &text, at) {
            assert!(!e.is_empty() && e.len() <= e5r_asm::MAX_INSN, "{text:?}");
            if arch == Arch::AArch64 {
                assert_eq!(e.len(), 4, "{text:?}");
            }
        }
        let _ = parse(&arch, &text, at);
        n += 1;
    }
    assert!(
        n > 1000,
        "only {n} cases in {BUDGET:?}; something is very slow"
    );
    println!("assembler fuzz: {n} mutated lines, no panics");
}

#[test]
fn arbitrary_bytes_never_panic() {
    let mut rng = Rng(0x5eed_dead_beef_0202);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let len = rng.below(MAX_TEXT * 2);
        let text: String = (0..len).map(|_| *rng.pick(BYTES) as char).collect();
        let arch = arches()[rng.below(2)].clone();
        let _ = assemble(&arch, &text, Addr(rng.next()));
        n += 1;
    }
    assert!(n > 500, "only {n} cases in {BUDGET:?}");
    println!("assembler fuzz: {n} random lines, no panics");
}

/// Every input is bounded before anything is allocated from it, so the time
/// one line takes cannot depend on what the line says.
#[test]
fn a_hostile_line_is_bounded_in_time_and_length() {
    let cases = [
        "mov ".to_string() + &"rax, ".repeat(4000),
        "mov rax, 0x".to_string() + &"f".repeat(4000),
        "[".repeat(4000),
        "mov rax, ".to_string() + &"[".repeat(400),
        "b".to_string() + &".".repeat(4000),
        "\0".repeat(4000),
        "mov\trax, [rax + ".to_string() + &"1*rcx + ".repeat(1000) + "0]",
    ];
    for text in cases {
        for arch in arches() {
            let started = Instant::now();
            let r = assemble(&arch, &text, Addr(0x1000));
            assert!(
                started.elapsed() < Duration::from_millis(100),
                "{arch:?} took too long on {} bytes",
                text.len()
            );
            // Anything this long is refused, and the refusal says why.
            if text.len() > MAX_TEXT {
                assert!(r.is_err(), "{arch:?} accepted {} bytes", text.len());
            }
        }
    }
}

/// A multi-line paste is the same contract, once per line.
#[test]
fn a_block_of_text_assembles_line_by_line() {
    let block = "push\trbp\nmov\trbp, rsp\n# a note\n\nsub\trsp, 0x20\npop\trbp\nret\n";
    let bytes = assemble_all(&Arch::X86_64, block, Addr(0x1000)).expect("block");
    assert_eq!(
        bytes,
        [0x55, 0x48, 0x89, 0xe5, 0x48, 0x83, 0xec, 0x20, 0x5d, 0xc3]
    );

    let a64 = "stp\tx29, x30, [sp, #-16]!\nmov\tx29, sp\nldp\tx29, x30, [sp], #16\nret\n";
    let bytes = assemble_all(&Arch::AArch64, a64, Addr(0x1000)).expect("block");
    assert_eq!(bytes.len(), 16);

    let mut rng = Rng(0x5eed_0f0f_0303);
    for _ in 0..2000 {
        let mut block = String::new();
        for _ in 0..rng.below(8) {
            block.push_str(&mutate(rng.pick(SEEDS), &mut rng));
            block.push('\n');
        }
        let arch = arches()[rng.below(2)].clone();
        let _ = assemble_all(&arch, &block, Addr(rng.next()));
    }
}

/// Padding is exact or it is refused; a patch that pads the wrong length has
/// left a hole in the middle of a function.
#[test]
fn padding_is_exactly_the_length_asked_for() {
    for n in 0..256usize {
        let p = pad(&Arch::X86_64, n).expect("x86 pads any length");
        assert_eq!(p.len(), n);
        match pad(&Arch::AArch64, n) {
            Ok(p) => {
                assert_eq!(n % 4, 0);
                assert_eq!(p.len(), n);
            }
            Err(_) => assert_ne!(n % 4, 0),
        }
    }
}
