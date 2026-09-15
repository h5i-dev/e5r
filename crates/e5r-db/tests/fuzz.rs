//! Mutation fuzzing of the signature reader, in the ordinary test run.
//!
//! A signature library is the one file in this crate that somebody else wrote.
//! It is produced by a script run over packages nobody here chose, it travels
//! between machines, and it gets checked into other people's repositories, so
//! the reader has to treat it the way the loaders treat a binary: any bytes in,
//! a value or a skipped line out, never a panic, never a hang, and never an
//! allocation the file gets to choose the size of.

use std::time::{Duration, Instant};

use e5r_db::signature::{Library, MAX_SIGNATURES, Signature};

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
}

/// A real library to mutate, with the shapes a written one actually has.
fn seed() -> String {
    let mut v = Vec::new();
    for n in 0..200u64 {
        v.push(Signature {
            shape: n.wrapping_mul(0x9e37_79b9_7f4a_7c15),
            bytes: n.wrapping_mul(0xc2b2_ae3d_27d4_eb4f),
            insns: 12 + (n as u32 % 90),
            name: format!("_ZN4libc7routine{n}Ev"),
            source: format!("libc.a(part{}.o)", n % 17),
        });
    }
    Library::build(v).to_text()
}

/// Corrupt a buffer in the ways that actually break a text parser.
fn mutate(seed: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = seed.to_vec();
    if v.is_empty() {
        return v;
    }
    match rng.below(7) {
        // Truncate, including in the middle of a multi-byte character.
        0 => v.truncate(rng.below(v.len())),
        // Flip a bit, which is how a digit becomes a letter.
        1 => {
            let i = rng.below(v.len());
            v[i] ^= 1 << rng.below(8);
        }
        // Delete the separators, so every field runs into the next.
        2 => v.retain(|b| *b != b' '),
        // Delete the line breaks, so the whole file is one enormous line.
        3 => v.retain(|b| *b != b'\n'),
        // A number far past what the field can hold.
        4 => {
            let i = rng.below(v.len());
            let end = (i + 24).min(v.len());
            for b in &mut v[i..end] {
                *b = b'9';
            }
        }
        // Arbitrary bytes in the middle, including invalid UTF-8 and NULs.
        5 => {
            let i = rng.below(v.len());
            let end = (i + rng.below(32)).min(v.len());
            for b in &mut v[i..end] {
                *b = (rng.next() & 0xff) as u8;
            }
        }
        // Repeat a chunk, so the file claims the same name for many shapes.
        _ => {
            let from = rng.below(v.len());
            let len = rng.below(256).min(v.len() - from);
            let chunk: Vec<u8> = v[from..from + len].to_vec();
            for _ in 0..rng.below(8) {
                v.extend_from_slice(&chunk);
            }
        }
    }
    v
}

#[test]
fn the_signature_reader_survives_mutated_files() {
    let base = seed();
    let mut rng = Rng(0x5eed_51c0_0000_0001);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let case = mutate(base.as_bytes(), &mut rng);
        // Not every mutation leaves valid UTF-8, which is itself a case the
        // caller has to handle rather than a reason not to test the reader.
        let text = String::from_utf8_lossy(&case);
        let library = Library::from_text(&text);
        // Whatever came back has to be usable: every index the reader built
        // has to still address the list it indexes, which a lookup for each
        // signature is what checks.
        for s in &library.signatures {
            let _ = library.identify(&anchor(s));
        }
        n += 1;
    }
    assert!(
        n > 50,
        "only {n} cases in {BUDGET:?}; something is very slow"
    );
    println!("signature fuzz: {n} mutated cases, no panics");
}

#[test]
fn arbitrary_text_is_not_a_signature_library() {
    let mut rng = Rng(0x5eed_51c0_0000_0002);
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < BUDGET {
        let len = rng.below(4096);
        let mut s = String::with_capacity(len);
        while s.len() < len {
            match rng.below(6) {
                0 => s.push('\n'),
                1 => s.push(' '),
                2 => s.push('#'),
                3 => s.push_str(&format!("{:x}", rng.next())),
                4 => s.push_str(&rng.next().to_string()),
                _ => s.push(char::from_u32((rng.next() % 0x2000) as u32).unwrap_or('?')),
            }
        }
        let _ = Library::from_text(&s);
        n += 1;
    }
    assert!(n > 50, "only {n} cases in {BUDGET:?}");
    println!("signature fuzz: {n} random cases, no panics");
}

#[test]
fn a_field_that_cannot_fit_is_skipped_rather_than_wrapped() {
    // Each of these is one plausible-looking line with one impossible field.
    // Skipping the line is the answer; wrapping the value would put a
    // fabricated fingerprint in the library, which is worse than losing it.
    let text = concat!(
        "# e5r signatures v1\n",
        "ffffffffffffffffff 0000000000000002 20 too_wide_shape libc.a\n",
        "0000000000000001 zzzzzzzzzzzzzzzz 20 not_hex libc.a\n",
        "0000000000000001 0000000000000002 99999999999 too_many_insns libc.a\n",
        "0000000000000001 0000000000000002 -3 negative_insns libc.a\n",
        "0000000000000001 0000000000000002 20\n",
        "0000000000000003 0000000000000004 20 fine libc.a\n",
    );
    let library = Library::from_text(text);
    assert_eq!(library.len(), 1);
    assert_eq!(library.signatures[0].name, "fine");
    assert!(!library.truncated);
}

#[test]
fn a_file_longer_than_the_cap_stops_at_a_number() {
    // The text form carries no count for a hostile file to lie about, so the
    // bound is on the result. It has to be reported, because a silently
    // truncated library would answer "not found" for real code.
    let mut text = String::from("# e5r signatures v1\n");
    for n in 0..64u64 {
        text.push_str(&format!("{n:016x} {n:016x} 30 name{n} src\n"));
    }
    let full = Library::from_text_capped(&text, 1000);
    assert_eq!(full.len(), 64);
    assert!(!full.truncated);

    let capped = Library::from_text_capped(&text, 10);
    assert_eq!(capped.len(), 10);
    assert!(capped.truncated, "a truncated library did not say so");
    // And the ceiling the default reads with is one a real library lives
    // under: every static archive a distribution ships, together, is short of
    // it, so an ordinary file comes back whole.
    let default = Library::from_text_capped(&text, MAX_SIGNATURES);
    assert_eq!(default.len(), 64);
    assert!(!default.truncated);
}

#[test]
fn a_file_that_is_one_enormous_line_is_read_in_bounded_time() {
    // The reader splits on line breaks; a file with none of them is one field
    // a megabyte long, and it must not become quadratic in that length.
    let mut text = String::from("0000000000000001 0000000000000002 20 ");
    text.push_str(&"a".repeat(4 * 1024 * 1024));
    let started = Instant::now();
    let library = Library::from_text(&text);
    assert_eq!(library.len(), 1);
    assert!(
        started.elapsed() < Duration::from_secs(2),
        "one long line took {:?}",
        started.elapsed()
    );
}

#[test]
fn a_library_full_of_one_name_still_refuses_the_coin_flip() {
    // The shape a repeated chunk produces: many signatures, disagreeing. The
    // reader must not turn that into a confident answer downstream.
    let mut text = String::from("# e5r signatures v1\n");
    for n in 0..500u64 {
        text.push_str(&format!(
            "0000000000000001 0000000000000002 40 name{n} src\n"
        ));
    }
    let library = Library::from_text(&text);
    assert_eq!(library.len(), 500);
    let a = e5r_db::Anchor {
        shape: 1,
        bytes: 2,
        insns: 40,
        abs: e5r_core::Addr(0x1000),
        offset: 0,
    };
    assert!(library.identify(&a).is_none(), "500 names named one thing");
}

/// The anchor a signature describes, for feeding the matcher its own output.
fn anchor(s: &Signature) -> e5r_db::Anchor {
    e5r_db::Anchor {
        shape: s.shape,
        bytes: s.bytes,
        insns: s.insns,
        abs: e5r_core::Addr(0x1000),
        offset: 0,
    }
}
