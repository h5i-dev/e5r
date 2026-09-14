//! Decoding and lifting are given hostile input and must not misbehave.
//!
//! Two things are hostile here and they are different threats.
//!
//! The **bytes** are whatever was in the file. A decoder walks them, and a
//! specification can ask it to read at an offset another operand computed, so
//! an instruction stream of noise reaches paths a real program never does.
//! Nothing here may panic, loop, or take time that depends on anything but the
//! specification's size.
//!
//! The **specification** is a file too, and a corrupted one is the worse case:
//! it is the thing that says how far to read, how deep to recurse and how many
//! of everything there are. A `.slaspec` mutated at random reaches the front
//! end's own limits, and one that parses but describes a nonsense machine
//! reaches the decoder's.
//!
//! The generator is a fixed sequence, not a random one, so a failure is
//! reproducible from the seed printed in the message. `crates/r12e-sleigh/
//! tests/fuzz.rs` does the same for the parser; this is its counterpart for
//! the engine.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use r12e_sleigh::{DecodeLimits, Decoder, Spec, pcode};

/// A small deterministic generator. The multiplier is the one from Knuth's
/// tables; nothing here needs statistical quality, only repeatability.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 16
    }

    fn byte(&mut self) -> u8 {
        self.next() as u8
    }

    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() as usize) % n
        }
    }
}

/// The specification used where a real one is not needed: small, and with a
/// context register, a subtable, an attachment with a hole, a disassembly
/// action and a `globalset`, so a fuzzed stream can reach each of them.
const TOY: &str = r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 r2 r3 ];
define register offset=0x100 size=4 [ ctxreg ];
define context ctxreg
    mode=(0,0)
    phase=(1,1)
;
define token instr(16)
    op=(12,15)
    rd=(8,11)
    rs=(4,7)
    imm8=(0,7)
    simm8=(0,7) signed
;
define token suffix(8) sx=(0,7);
attach variables [ rd rs ] [ r0 r1 _ r3 ];

Mode: rd     is mode=0 & rd { export rd; }
Mode: imm8   is mode=1 & imm8 { local t:4 = imm8; export t; }
Tail: sx     is sx { export *[const]:1 sx; }

:add rd,Mode  is op=0 & rd & Mode { rd = rd + Mode; }
:ldx rd,Mode,Tail is op=1 & rd & Mode ; Tail { rd = Mode + Tail; }
:sw  rd,rs    is op=2 & rd & rs { *:4 rd = rs; }
:br  simm8    is op=3 & simm8 [ mode=1; globalset(inst_next, mode); ] { goto inst_start; }
:sel rd       is op=4 & phase=0 & rd [ phase=1; ] { rd = rd + 1; }
:sel2 rd      is op=4 & phase=1 & rd { rd = rd - 1; }
:mac rd,rs    is op=5 & rd & rs { rd = rd * rs; rd = rd + 1; }
:deep rd      is op=6 & rd unimpl
"#;

/// A decode must never take longer than this. Generous by three orders of
/// magnitude: a real one is under a microsecond.
const BUDGET: Duration = Duration::from_millis(200);

fn toy() -> Spec {
    r12e_sleigh::parse_str(TOY).expect("the toy specification parses")
}

#[test]
fn random_bytes_never_panic_and_always_finish() {
    let spec = toy();
    let mut rng = Rng(0x5eed_1234_abcd_0001);
    let mut decoded = 0usize;
    for round in 0..20_000u64 {
        let n = 1 + rng.below(24);
        let bytes: Vec<u8> = (0..n).map(|_| rng.byte()).collect();
        let addr = rng.next();
        let mut d = Decoder::new(&spec);
        let start = Instant::now();
        let out = d.decode(&bytes, addr);
        let took = start.elapsed();
        assert!(
            took < BUDGET,
            "round {round} took {took:?} on {bytes:02x?} at {addr:#x}"
        );
        if let Ok(insn) = out {
            decoded += 1;
            // The length must be inside the bytes it was given, or every
            // caller sweeping forwards will read past the end or stand still.
            assert!(
                insn.len > 0 && insn.len <= bytes.len(),
                "round {round}: length {} from {} bytes",
                insn.len,
                bytes.len()
            );
            let text = insn.text(&spec);
            assert!(text.len() < 4096, "round {round}: runaway text");
            let p = pcode::lift(&spec, &insn);
            assert!(p.ops.len() <= 4096, "round {round}: runaway lift");
        }
    }
    assert!(
        decoded > 1_000,
        "only {decoded} of 20000 random inputs decoded, so most of the walk was \
         never reached and this test is measuring nothing"
    );
}

/// Decoding must never move an address backwards or stand still, whatever the
/// bytes say. A sweep that does either does not terminate.
#[test]
fn a_sweep_over_noise_always_advances() {
    let spec = toy();
    let mut rng = Rng(0xfeed_0000_0000_0002);
    let bytes: Vec<u8> = (0..1 << 16).map(|_| rng.byte()).collect();
    let mut d = Decoder::new(&spec);
    let mut at = 0usize;
    let mut steps = 0usize;
    let start = Instant::now();
    while at < bytes.len() {
        let step = match d.decode(&bytes[at..], at as u64) {
            Ok(insn) => insn.len,
            Err(_) => 1,
        };
        assert!(step > 0, "a decode at {at} claimed zero bytes");
        at += step;
        steps += 1;
        assert!(steps <= bytes.len(), "the sweep did not terminate");
    }
    assert!(start.elapsed() < Duration::from_secs(30));
}

/// A specification mutated at random either fails to parse or produces a
/// decoder that behaves.
///
/// This is the case that matters most: the file being corrupted is the file
/// that says how big everything is.
#[test]
fn a_corrupted_specification_does_not_produce_a_misbehaving_decoder() {
    let original = TOY.as_bytes();
    let mut rng = Rng(0x00c0_ffee_0000_0003);
    let mut parsed = 0usize;
    for round in 0..3_000u64 {
        let mut text = original.to_vec();
        for _ in 0..1 + rng.below(6) {
            let at = rng.below(text.len());
            text[at] = rng.byte();
        }
        let Ok(text) = String::from_utf8(text) else {
            continue;
        };
        let Ok(spec) = r12e_sleigh::parse_str(&text) else {
            continue;
        };
        parsed += 1;
        // A specification with no instruction table is a specification a
        // decoder must refuse, not one it may walk.
        let mut d = Decoder::new(&spec);
        for seed in 0..16u64 {
            let bytes: Vec<u8> = (0..8).map(|i| (seed as u8).wrapping_mul(31 + i)).collect();
            let start = Instant::now();
            let out = d.decode(&bytes, seed * 0x1000);
            assert!(
                start.elapsed() < BUDGET,
                "round {round} seed {seed}: a mutated specification made a decode hang"
            );
            if let Ok(insn) = out {
                assert!(insn.len > 0 && insn.len <= bytes.len());
                let _ = insn.text(&spec);
                let _ = pcode::lift(&spec, &insn);
            }
        }
    }
    // Most mutations of a structured text file stop it parsing, which is the
    // front end doing its job; what this test needs is that enough of them get
    // through to reach the decoder at all.
    assert!(
        parsed > 20,
        "only {parsed} mutations parsed, so the decoder was barely exercised"
    );
}

/// A specification that recurses into its own root table must be stopped by
/// the depth limit rather than by the stack running out.
#[test]
fn unbounded_recursion_is_an_error_rather_than_a_crash() {
    let spec = r12e_sleigh::parse_str(
        r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0x100 size=4 [ ctxreg ];
define context ctxreg flag=(0,0);
define token instr(8) op=(0,7);
:^instruction is flag=0 & instruction { build instruction; }
:halt is flag=1 & op=0xff { }
"#,
    )
    .expect("parses");
    let mut d = Decoder::new(&spec).with_limits(DecodeLimits {
        max_depth: 8,
        ..DecodeLimits::default()
    });
    // The wrapper never sets `flag`, so it matches itself for ever and the one
    // real constructor, which needs `flag=1`, is never reachable. The depth
    // limit is what stops it, and the caller is told which limit it was.
    let start = Instant::now();
    let err = d.decode(&[0xff], 0).unwrap_err();
    assert!(start.elapsed() < BUDGET);
    assert_eq!(err, r12e_sleigh::DecodeError::TooDeep);
}

/// The real specifications, on noise.
///
/// A toy specification cannot reach the paths that x86's ModR/M and AArch64's
/// context re-parse do, and those are where a decode engine goes wrong.
#[test]
fn the_published_specifications_survive_noise() {
    let Some(root) = ghidra() else { return };
    let mut rng = Rng(0xabad_1dea_0000_0004);
    let bytes: Vec<u8> = (0..1 << 14).map(|_| rng.byte()).collect();
    for rel in [
        "AARCH64/data/languages/AARCH64.slaspec",
        "x86/data/languages/x86-64.slaspec",
        "RISCV/data/languages/riscv.lp64d.slaspec",
        "ARM/data/languages/ARM7_le.slaspec",
        "MIPS/data/languages/mips32be.slaspec",
        "PowerPC/data/languages/ppc_32_be.slaspec",
        "Sparc/data/languages/SparcV9_32.slaspec",
        "SuperH4/data/languages/SuperH4_le.slaspec",
        "68000/data/languages/68030.slaspec",
        "6502/data/languages/6502.slaspec",
        "Z80/data/languages/z80.slaspec",
        "Atmel/data/languages/avr8.slaspec",
        "TI_MSP430/data/languages/TI_MSP430.slaspec",
        "Xtensa/data/languages/xtensa_le.slaspec",
        "tricore/data/languages/tricore.slaspec",
        "V850/data/languages/V850.slaspec",
        "Loongarch/data/languages/loongarch64.slaspec",
    ] {
        let p = root.join("Ghidra/Processors").join(rel);
        if !p.is_file() {
            continue;
        }
        let spec = r12e_sleigh::parse_file(&p).expect("the specification parses");
        let mut d = Decoder::new(&spec);
        let mut at = 0usize;
        let mut steps = 0usize;
        let start = Instant::now();
        while at + 16 <= bytes.len() {
            let step = match d.decode(&bytes[at..], at as u64) {
                Ok(insn) => {
                    assert!(insn.len > 0, "{rel} claimed a zero length instruction");
                    let _ = insn.text(&spec);
                    let p = pcode::lift(&spec, &insn);
                    assert!(p.ops.len() <= 4096);
                    insn.len
                }
                Err(_) => 1,
            };
            at += step;
            steps += 1;
        }
        let took = start.elapsed();
        eprintln!("{rel}: {steps} decodes over noise in {took:?}");
        assert!(took < Duration::from_secs(60), "{rel} took {took:?}");
    }
}

fn ghidra() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("R12E_GHIDRA") {
        let p = PathBuf::from(p);
        return p.is_dir().then_some(p);
    }
    for guess in [
        "../ghidra",
        "../../ghidra",
        concat!(env!("HOME"), "/Ref/ghidra"),
        "/opt/ghidra",
    ] {
        let p = PathBuf::from(guess);
        if p.join("Ghidra/Processors").is_dir() {
            return Some(p);
        }
    }
    None
}

/// A decoder that is handed a specification with no tables at all says so.
#[test]
fn a_specification_with_no_instruction_table_is_refused() {
    let spec = Spec::default();
    let mut d = Decoder::new(&spec);
    assert_eq!(
        d.decode(&[0, 1, 2, 3], 0).unwrap_err(),
        r12e_sleigh::DecodeError::NoRootTable
    );
    let _ = Path::new("");
}
