//! Truncated and corrupted specifications, on stable and in the ordinary run.
//!
//! A `.slaspec` is input like an executable is input: it arrives from a
//! processor tree somebody else maintains, and a front end that panics or
//! spins on a bad one is a denial of service in whatever loaded it. The
//! contract is the same as the loaders': any bytes in, a value or a typed
//! error out, inside a bounded time and a bounded allocation.
//!
//! The seeds are the specifications checked in next to this file plus, when a
//! Ghidra tree is present, a sample of real ones. The mutations are the ones
//! that actually break parsers: truncation, a delimiter turned into another
//! delimiter, a count turned enormous, and a construct repeated until it
//! nests.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Total time for the mutation loop. Enough to find a systematic fault, short
/// enough that nobody is tempted to skip the suite.
const BUDGET: Duration = Duration::from_millis(1500);
/// No single input may take longer than this. A parser that hits it has a loop
/// that does not advance, which is the bug this catches.
const PER_INPUT: Duration = Duration::from_millis(400);

/// xorshift64*, so a failure is reproducible from its seed.
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
}

fn ghidra_root() -> Option<PathBuf> {
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

fn seeds() -> Vec<String> {
    let mut out = vec![
        std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/toy.slaspec"),
        )
        .expect("the toy specification is checked in"),
    ];
    // A second seed that reaches the parts the toy does not: macros, a with
    // block, a disassembly action, labels, branches and unimpl.
    out.push(
        r#"
        @define SIZE "4"
        define endian=little;
        define space ram type=ram_space size=$(SIZE) default;
        define space register type=register_space size=4;
        define register offset=0 size=4 [ r0 r1 r2 sp pc statusreg ];
        define token base(16) op=(10,15) cc=(8,9) rd=(4,7) rs=(0,3) simm8=(0,7) signed;
        define token ext(16) imm16=(0,15);
        define context statusreg mode=(0,1) noflow;
        define pcodeop arctan;
        define bitrange zf=statusreg[10,1];
        attach variables [ rd rs ] [ r0 r1 r2 sp ];
        attach names [ cc ] [ "eq" "ne" "cs" "cc" ];
        macro flags(v) { zf = (v == 0); }
        dest: rel is simm8 [ rel = inst_next + simm8 * 4; ] { export *[ram]:4 rel; }
        with : mode=1 {
          :add rd,rs is op=1 & rd & rs { rd = rd + rs; flags(rd); }
          :ldi rd,imm16 is op=2 & rd; imm16 { rd = imm16:4; }
        }
        :b^cc dest is op=3 & cc & dest { if (zf != 0) goto dest; }
        :loop rd is op=4 & rd { <top> rd = rd - 1; if (rd s> 0) goto <top>; }
        :atan rd,rs is op=5 & rd & rs { rd = arctan(rs); }
        :cache rd is op=6 & rd unimpl
        "#
        .to_string(),
    );
    if let Some(root) = ghidra_root() {
        for name in [
            "6502/data/languages/6502.slaspec",
            "Z80/data/languages/z80.slaspec",
            "Toy/data/languages/toy_be.slaspec",
        ] {
            let Ok(text) = std::fs::read_to_string(root.join("Ghidra/Processors").join(name))
            else {
                continue;
            };
            // Only files that stand on their own: these seeds go through
            // `parse_str`, which has no include resolution, and a seed that
            // does not parse would fuzz the error path and nothing else.
            if r12e_sleigh::parse_str(&text).is_ok() {
                out.push(text);
            }
        }
    }
    out
}

fn mutate(seed: &str, rng: &mut Rng) -> String {
    let mut v = seed.as_bytes().to_vec();
    if v.is_empty() {
        return String::new();
    }
    match rng.below(8) {
        // Truncation, the most common real corruption.
        0 => v.truncate(rng.below(v.len())),
        // Flip a bit.
        1 => {
            let i = rng.below(v.len());
            v[i] ^= 1 << rng.below(8);
        }
        // Turn one delimiter into another, which is how a parser loses track
        // of where it is.
        2 => {
            let i = rng.below(v.len());
            v[i] = *b"{}[]()<>;:,\"#^&|$@".get(rng.below(18)).unwrap_or(&b'{');
        }
        // A number that saturates every width.
        3 => {
            let i = rng.below(v.len());
            let mut digits = b"0xffffffffffffffffff".to_vec();
            digits.extend_from_slice(&v[i..]);
            v.truncate(i);
            v.append(&mut digits);
        }
        // Delete a run.
        4 => {
            let i = rng.below(v.len());
            let n = rng.below(v.len() - i).min(256);
            v.drain(i..i + n);
        }
        // Repeat a run, which turns a construct into a nest of itself.
        5 => {
            let i = rng.below(v.len());
            let n = rng.below((v.len() - i).min(64)).max(1);
            let chunk = v[i..i + n].to_vec();
            for _ in 0..rng.below(32) {
                v.extend_from_slice(&chunk);
            }
        }
        // Splice two seeds together.
        6 => {
            let i = rng.below(v.len());
            v.truncate(i);
            v.extend_from_slice(b"\n} } } ] ] ) ) is { export\n");
        }
        // Random bytes, including invalid UTF-8 once it goes through lossy.
        _ => {
            let i = rng.below(v.len());
            let end = (i + 1 + rng.below(32)).min(v.len());
            for b in &mut v[i..end] {
                *b = (rng.next() & 0xff) as u8;
            }
        }
    }
    String::from_utf8_lossy(&v).into_owned()
}

fn check(text: &str, what: &str) {
    let started = Instant::now();
    // The contract: a value or an error, never a panic.
    let _ = r12e_sleigh::parse_str(text);
    let took = started.elapsed();
    assert!(
        took < PER_INPUT,
        "{what} took {took:?}, over the {PER_INPUT:?} ceiling"
    );
}

/// A fuzz test seeded with text that does not parse is only testing the error
/// path, so the seeds are checked first.
#[test]
fn the_seeds_themselves_parse() {
    for (i, seed) in seeds().iter().enumerate() {
        let spec = r12e_sleigh::parse_str(seed)
            .unwrap_or_else(|e| panic!("seed {i} should parse, but {e}"));
        assert!(!spec.constructors.is_empty(), "seed {i} produced nothing");
    }
}

#[test]
fn mutated_specifications_do_not_panic_or_hang() {
    let seeds = seeds();
    let mut rng = Rng(0x5eed_1234_abcd_ef01);
    let started = Instant::now();
    let mut iterations = 0u64;
    while started.elapsed() < BUDGET {
        let seed = &seeds[rng.below(seeds.len())];
        let text = mutate(seed, &mut rng);
        check(&text, &format!("mutation {iterations}"));
        iterations += 1;
    }
    assert!(iterations > 50, "only {iterations} mutations in the budget");
}

/// Every prefix of a valid specification, which is truncation done exhaustively
/// rather than at random.
#[test]
fn every_prefix_of_a_valid_specification_is_handled() {
    for seed in seeds() {
        let bytes = seed.as_bytes();
        // A stride keeps this a test rather than a sweep; the interesting
        // cut points are dense enough that it still lands inside every
        // construct.
        let stride = (bytes.len() / 400).max(1);
        let mut at = 0;
        while at <= bytes.len() {
            let text = String::from_utf8_lossy(&bytes[..at]);
            check(&text, &format!("prefix of {at} bytes"));
            at += stride;
        }
    }
}

/// The shapes that are specifically designed to make a recursive descent
/// parser recurse, or a preprocessor loop.
#[test]
fn hostile_shapes_are_refused_rather_than_survived() {
    let header = "define endian=little;\ndefine space ram type=ram_space size=4 default;\n";
    let cases: Vec<(String, &str)> = vec![
        (
            format!(
                "{header}define token t(8) f=(0,7);\n:x is {}f=1{}\n{{ }}\n",
                "(".repeat(50_000),
                ")".repeat(50_000)
            ),
            "a pattern nested fifty thousand deep",
        ),
        (
            format!(
                "{header}define token t(8) f=(0,7);\n:x is f=1 {{ a = {}1{}; }}\n",
                "(".repeat(50_000),
                ")".repeat(50_000)
            ),
            "an expression nested fifty thousand deep",
        ),
        (
            format!(
                "{}{}",
                "@ifdef X\n".repeat(50_000),
                "@endif\n".repeat(50_000)
            ),
            "fifty thousand nested conditionals",
        ),
        (
            format!("@define A \"$(A)\"\n{header}define alignment=$(A);\n"),
            "a macro that expands to itself",
        ),
        (
            format!(
                "{header}define register offset=0 size=1 [ {} ];\n",
                "r ".repeat(200_000)
            ),
            "a register list of two hundred thousand names",
        ),
        (
            format!("{header}define token t(8) f=(0,7);\n:x is f=1 {{ a = b"),
            "a body that never closes",
        ),
        (
            format!("{header}define token t(8) f=(0,7);\n:x is f=1 [ a = 1"),
            "a disassembly action that never closes",
        ),
        (
            format!("{header}:x is"),
            "a pattern that ends at the end of the file",
        ),
        (
            format!("{header}{}", "with : {\n".repeat(20_000)),
            "twenty thousand nested with blocks",
        ),
        // A flat chain costs the parser no stack but leans the tree it builds
        // one level per term, and the reducer and the drop glue both walk that
        // tree recursively.
        (
            format!(
                "{header}define token t(8) f=(0,7);\n:x is {}f=1 {{ }}\n",
                "f=1 & ".repeat(200_000)
            ),
            "a conjunction of two hundred thousand terms",
        ),
        (
            format!(
                "{header}define token t(8) f=(0,7);\n:x is {}f=1 {{ }}\n",
                "f=1 | ".repeat(200_000)
            ),
            "a disjunction of two hundred thousand terms",
        ),
        (
            format!(
                "{header}define token t(8) f=(0,7);\n:x is f=1 {{ a = {}1; }}\n",
                "1 + ".repeat(200_000)
            ),
            "a sum of two hundred thousand terms",
        ),
        (
            format!("{header}define token t(8000000) f=(0,7);\n"),
            "a token of eight million bits",
        ),
        (
            format!("{header}define space bad type=ram_space size=99999999;\n"),
            "an address space of a hundred million bytes",
        ),
        (
            ":no display section and no is keyword ever arrives".to_string(),
            "a display section that runs off the end",
        ),
    ];
    for (text, what) in cases {
        let started = Instant::now();
        let result = r12e_sleigh::parse_str(&text);
        let took = started.elapsed();
        assert!(took < PER_INPUT, "{what} took {took:?}");
        assert!(result.is_err(), "{what} should have been refused");
    }
}

/// An `@include` cycle terminates on the depth limit rather than the stack.
#[test]
fn an_include_cycle_stops_at_the_depth_limit() {
    let mut loader = r12e_sleigh::preprocess::MemoryLoader::new();
    loader.insert("a.slaspec", "@include \"b.sinc\"\n");
    loader.insert("b.sinc", "@include \"a.slaspec\"\n");
    let started = Instant::now();
    let result = r12e_sleigh::parse_with(
        Path::new("a.slaspec"),
        &mut loader,
        r12e_sleigh::Limits::default(),
        &[],
    );
    assert!(started.elapsed() < PER_INPUT);
    let error = result.expect_err("an include cycle is an error");
    assert!(error.message.contains("nests"), "{error}");
}
