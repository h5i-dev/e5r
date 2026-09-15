//! Mutation fuzzing of the decoders.
//!
//! A decoder's contract is narrower than a loader's but no less absolute: given
//! any bytes it returns an instruction or nothing, never a panic, and the
//! length it reports is never longer than the bytes it was given.

use std::time::{Duration, Instant};

use e5r_arch::{aarch64, x86};
use e5r_core::Addr;

const BUDGET: Duration = Duration::from_millis(1200);

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
}

#[test]
fn aarch64_decodes_anything_without_panicking() {
    let mut rng = Rng(0xa64_0001);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let w = rng.next() as u32;
        if let Some(i) = aarch64::decode_word(w, Addr(0x40_0000)) {
            // Fixed-width architecture: anything else is a decoder bug.
            assert_eq!(i.len, 4, "{w:08x} decoded as {} bytes", i.len);
            // Formatting must not panic either; it is the other half of the
            // decoder's surface.
            let _ = aarch64::format(&i, aarch64::Style { objdump: true });
        }
        n += 1;
    }
    assert!(n > 10_000, "only {n} words in {BUDGET:?}");
    println!("aarch64 fuzz: {n} words, no panics");
}

#[test]
fn x86_decodes_anything_without_panicking() {
    let mut rng = Rng(0x86_0002);
    let start = Instant::now();
    let mut n = 0u64;
    let mut buf = [0u8; 16];
    while start.elapsed() < BUDGET {
        for chunk in buf.chunks_mut(8) {
            chunk.copy_from_slice(&rng.next().to_le_bytes()[..chunk.len()]);
        }
        // Every prefix length, so the walk through the prefix loop is covered.
        let len = 1 + (rng.next() % 16) as usize;
        if let Some(i) = x86::decode(&buf[..len], Addr(0x40_0000)) {
            assert!(
                i.len as usize <= len,
                "{:02x?} decoded {} bytes from {len}",
                &buf[..len],
                i.len
            );
            assert!(
                i.len > 0 && i.len <= 15,
                "{:02x?} length {}",
                &buf[..len],
                i.len
            );
            let _ = x86::format(&i, x86::Style::default());
        }
        n += 1;
    }
    assert!(n > 10_000, "only {n} cases in {BUDGET:?}");
    println!("x86 fuzz: {n} cases, no panics");
}

#[test]
fn x86_prefix_storms_terminate() {
    // A run of prefixes with no opcode is the shape that makes a naive prefix
    // loop run off the end or loop forever.
    for prefix in [0x66u8, 0x67, 0xf0, 0xf2, 0xf3, 0x2e, 0x64, 0x40, 0x48] {
        for len in 1..64usize {
            let buf = vec![prefix; len];
            let started = Instant::now();
            let _ = x86::decode(&buf, Addr(0x1000));
            assert!(
                started.elapsed() < Duration::from_millis(50),
                "{len} copies of {prefix:#x} took too long"
            );
        }
    }
}

#[test]
fn every_aarch64_top_level_group_is_reached() {
    // A stride that crosses each of the sixteen top-level groups many times,
    // so a change that accidentally drops one shows up here.
    let mut seen = [false; 16];
    let mut w: u32 = 0;
    loop {
        if aarch64::decode_word(w, Addr(0x1000)).is_some() {
            seen[((w >> 25) & 0xf) as usize] = true;
        }
        let Some(next) = w.checked_add(0x1_0001) else {
            break;
        };
        w = next;
    }
    let reached = seen.iter().filter(|x| **x).count();
    assert!(
        reached >= 8,
        "only {reached} of 16 top-level groups decode anything"
    );
}
