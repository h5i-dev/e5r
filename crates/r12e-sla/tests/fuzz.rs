//! Mutation fuzzing of the `.sla` reader, in the ordinary test run.
//!
//! The shape follows `r12e-format/tests/fuzz.rs`: a fixed time budget, a
//! deterministic generator so a failure is reproducible from its seed, and one
//! contract to check. Here the contract is that `Sla::parse` given any bytes
//! returns a value or a typed error, never a panic, and returns inside a bound
//! whatever counts the file claims.
//!
//! A `.sla` is a compressed container, so the interesting inputs are of two
//! kinds and both are generated: corrupt the compressed image, which mostly
//! exercises the inflater, and corrupt the decompressed payload and recompress
//! it, which is the only way to reach the element decoder with hostile input.

use std::path::Path;
use std::time::{Duration, Instant};

use r12e_sla::{Sla, decode, inflate};

const BUDGET: Duration = Duration::from_millis(1500);

/// Anything slower than this on one input means a walk that does not advance.
const PER_CASE_CEILING: Duration = Duration::from_secs(2);

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

fn seeds() -> Vec<Vec<u8>> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let mut out = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&dir) {
        for e in entries.flatten() {
            let p = e.path();
            if p.extension().is_some_and(|x| x == "sla") {
                if let Ok(d) = std::fs::read(&p) {
                    out.push(d);
                }
            }
        }
    }
    out
}

fn mutate(seed: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = seed.to_vec();
    if v.is_empty() {
        return v;
    }
    match rng.below(6) {
        0 => v.truncate(rng.below(v.len())),
        1 => {
            let i = rng.below(v.len());
            v[i] ^= 1 << rng.below(8);
        }
        2 => {
            let i = rng.below(v.len());
            let end = (i + 8).min(v.len());
            v[i..end].fill(0xff);
        }
        3 => {
            let i = rng.below(v.len());
            let end = (i + 4).min(v.len());
            v[i..end].fill(0);
        }
        4 => {
            let from = rng.below(v.len());
            let to = rng.below(v.len());
            let len = rng.below(64).min(v.len() - from.max(to));
            let chunk: Vec<u8> = v[from..from + len].to_vec();
            v[to..to + len].copy_from_slice(&chunk);
        }
        _ => {
            let end = 0x80.min(v.len());
            for b in &mut v[..end] {
                if rng.below(8) == 0 {
                    *b = (rng.next() & 0xff) as u8;
                }
            }
        }
    }
    v
}

fn timed(case: &[u8]) {
    let started = Instant::now();
    let _ = Sla::parse(case);
    assert!(
        started.elapsed() < PER_CASE_CEILING,
        "one input took {:?}; a walk is not advancing",
        started.elapsed()
    );
}

#[test]
fn truncation_at_every_length_is_an_error_not_a_panic() {
    for seed in seeds() {
        for n in 0..seed.len() {
            timed(&seed[..n]);
        }
    }
}

#[test]
fn mutated_files_never_panic() {
    let corpus = seeds();
    assert!(!corpus.is_empty(), "fixtures should be present");
    let mut rng = Rng(0x51a_0000_0000_0001);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let seed = &corpus[rng.below(corpus.len())];
        timed(&mutate(seed, &mut rng));
        n += 1;
    }
    assert!(
        n > 100,
        "only {n} cases in {BUDGET:?}; something is very slow"
    );
    println!("sla fuzz: {n} mutated files, no panics");
}

#[test]
fn arbitrary_bytes_behind_the_magic_never_panic() {
    let mut rng = Rng(0x51a_0000_0000_0002);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let len = 8 + rng.below(2048);
        let mut v: Vec<u8> = b"sla\x04".to_vec();
        while v.len() < len {
            v.extend_from_slice(&rng.next().to_le_bytes());
        }
        v.truncate(len);
        timed(&v);
        n += 1;
    }
    assert!(n > 100, "only {n} cases in {BUDGET:?}");
    println!("sla fuzz: {n} random payloads, no panics");
}

/// Reach the element decoder directly. Corrupting the compressed image almost
/// always fails the Adler-32 first, so the decoder would otherwise never see a
/// hostile input at all.
#[test]
fn mutated_element_streams_never_panic() {
    let mut payloads: Vec<Vec<u8>> = Vec::new();
    for seed in seeds() {
        if seed.len() > 4 {
            if let Ok(p) = inflate::inflate_zlib(&seed[4..], inflate::DEFAULT_LIMIT) {
                payloads.push(p);
            }
        }
    }
    assert!(!payloads.is_empty(), "fixtures should inflate");

    let mut rng = Rng(0x51a_0000_0000_0003);
    let start = Instant::now();
    let mut n = 0u64;
    let mut decoded = 0u64;
    while start.elapsed() < BUDGET {
        let case = mutate(&payloads[rng.below(payloads.len())], &mut rng);
        let started = Instant::now();
        if decode::decode(&case).is_ok() {
            decoded += 1;
        }
        assert!(
            started.elapsed() < PER_CASE_CEILING,
            "one element stream took {:?}",
            started.elapsed()
        );
        n += 1;
    }
    assert!(n > 100, "only {n} cases in {BUDGET:?}");
    println!("sla fuzz: {n} mutated element streams, {decoded} still decoded, no panics");
}

/// A string length is the one count in the format big enough to matter, so it
/// gets its own case: an attribute claiming a four-gigabyte string must come
/// back as an error without reserving anything.
#[test]
fn a_lying_string_length_does_not_allocate() {
    // element 4, attribute 12, string value with five length chunks all 0x7f.
    let payload = vec![0x44, 0xcc, 0x75, 0xff, 0xff, 0xff, 0xff, 0xff, 0x84];
    let started = Instant::now();
    assert!(decode::decode(&payload).is_err());
    assert!(started.elapsed() < PER_CASE_CEILING);
}

/// The inflater has its own bound, and a stored block that claims more than
/// the input holds is the cheapest way to test it.
#[test]
fn a_lying_stored_block_length_does_not_allocate() {
    let z = vec![0x78, 0x01, 0x01, 0xff, 0xff, 0x00, 0x00, 0, 0, 0, 0];
    let started = Instant::now();
    assert!(inflate::inflate_zlib(&z, inflate::DEFAULT_LIMIT).is_err());
    assert!(started.elapsed() < PER_CASE_CEILING);
}
