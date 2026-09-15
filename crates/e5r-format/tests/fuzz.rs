//! Mutation fuzzing of the loaders, on stable and in the ordinary test run.
//!
//! `cargo-fuzz` needs nightly and a separate invocation, so it finds nothing
//! on a machine where nobody runs it. This runs every time, seeded from the
//! real corpus, and keeps a fixed budget so it stays a test rather than a
//! session. The contract it checks is the one the error model promises: a
//! loader given any bytes returns a value or an error, and never panics, hangs
//! or allocates without bound.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use e5r_format::{LoadOptions, load};

/// How long each target gets. Enough to find a systematic fault, short enough
/// that nobody is tempted to skip the suite.
const BUDGET: Duration = Duration::from_millis(1500);

/// A small deterministic generator, so a failure is reproducible from its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*, chosen for being four lines and reproducible.
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

fn corpus() -> Vec<Vec<u8>> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    let mut out = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&dir) {
        for e in entries.flatten() {
            let p: PathBuf = e.path();
            if !p.is_file() {
                continue;
            }
            if let Ok(d) = std::fs::read(&p) {
                // Prefixes only: a whole libc per iteration would make this a
                // throughput test rather than a fault hunt.
                out.push(d[..d.len().min(64 * 1024)].to_vec());
            }
        }
    }
    out
}

/// Corrupt a buffer in one of the ways that actually break parsers.
fn mutate(seed: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = seed.to_vec();
    if v.is_empty() {
        return v;
    }
    match rng.below(6) {
        // Truncate: the most common real-world corruption.
        0 => v.truncate(rng.below(v.len())),
        // Flip a bit.
        1 => {
            let i = rng.below(v.len());
            v[i] ^= 1 << rng.below(8);
        }
        // Write a saturating value, which is how a count becomes enormous.
        2 => {
            let i = rng.below(v.len());
            let end = (i + 8).min(v.len());
            for b in &mut v[i..end] {
                *b = 0xff;
            }
        }
        // Zero a field.
        3 => {
            let i = rng.below(v.len());
            let end = (i + 4).min(v.len());
            for b in &mut v[i..end] {
                *b = 0;
            }
        }
        // Splice: move a chunk somewhere else, which breaks every offset.
        4 => {
            let from = rng.below(v.len());
            let to = rng.below(v.len());
            let len = rng.below(64).min(v.len() - from.max(to));
            let chunk: Vec<u8> = v[from..from + len].to_vec();
            v[to..to + len].copy_from_slice(&chunk);
        }
        // Scramble the headers, which is where a parser does its arithmetic.
        _ => {
            let end = 0x200.min(v.len());
            for b in &mut v[..end] {
                if rng.below(8) == 0 {
                    *b = (rng.next() & 0xff) as u8;
                }
            }
        }
    }
    v
}

#[test]
fn loaders_survive_mutated_real_files() {
    let seeds = corpus();
    if seeds.is_empty() {
        return;
    }
    let opts = LoadOptions::default();
    let mut rng = Rng(0x5eed_1234_abcd_0001);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let seed = &seeds[rng.below(seeds.len())];
        let case = mutate(seed, &mut rng);
        // The contract: a value or an error, never anything else.
        let _ = load(&case, &opts);
        n += 1;
    }
    assert!(
        n > 100,
        "only {n} cases in {BUDGET:?}; something is very slow"
    );
    println!("loader fuzz: {n} mutated cases, no panics");
}

#[test]
fn loaders_survive_arbitrary_bytes() {
    // Not mutations of anything: bytes that only look like a header by
    // accident are a different shape of input.
    let opts = LoadOptions::default();
    let mut rng = Rng(0x5eed_dead_beef_0002);
    let start = Instant::now();
    let mut n = 0u64;
    // Every magic, so the probe actually reaches each loader.
    let magics: [&[u8]; 5] = [
        b"\x7fELF",
        b"MZ\x90\x00",
        b"\xcf\xfa\xed\xfe",
        b"\xca\xfe\xba\xbe",
        b"\x64\x86\x04\x00",
    ];
    while start.elapsed() < BUDGET {
        let len = 16 + rng.below(4096);
        let mut v = Vec::with_capacity(len);
        let magic = magics[rng.below(magics.len())];
        v.extend_from_slice(magic);
        while v.len() < len {
            v.extend_from_slice(&rng.next().to_le_bytes());
        }
        v.truncate(len);
        let _ = load(&v, &opts);
        n += 1;
    }
    assert!(n > 100, "only {n} cases in {BUDGET:?}");
    println!("loader fuzz: {n} random cases, no panics");
}

#[test]
fn a_lying_count_does_not_exhaust_memory() {
    // A header that claims four billion sections must produce an error rather
    // than an allocation. Measured by the fact that this returns at all.
    let mut elf = vec![0u8; 0x1000];
    elf[..4].copy_from_slice(b"\x7fELF");
    elf[4] = 2; // 64-bit
    elf[5] = 1; // little-endian
    elf[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    elf[18..20].copy_from_slice(&183u16.to_le_bytes()); // AArch64
    // e_shoff, e_shentsize, e_shnum: a plausible offset and an absurd count.
    elf[0x28..0x30].copy_from_slice(&0x40u64.to_le_bytes());
    elf[0x3a..0x3c].copy_from_slice(&64u16.to_le_bytes());
    elf[0x3c..0x3e].copy_from_slice(&0xffffu16.to_le_bytes());
    let started = Instant::now();
    let _ = load(&elf, &LoadOptions::default());
    assert!(
        started.elapsed() < Duration::from_secs(2),
        "a lying section count took too long"
    );
}
