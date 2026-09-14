//! Mutation fuzzing of the declaration parser, on stable and in the ordinary
//! test run.
//!
//! Same contract as the loaders in `r12e-format`: given any text, the parser
//! returns a value or an error, and never panics, hangs or allocates without
//! bound. This one is worth more than most, because the text comes straight
//! from a person's keyboard and from headers nobody in this project wrote.

use std::time::{Duration, Instant};

use r12e_types::cdecl;
use r12e_types::ctype::Types;

/// How long the whole hunt gets. Enough to find a systematic fault, short
/// enough that nobody is tempted to skip the suite.
const BUDGET: Duration = Duration::from_millis(2000);

/// No single declaration may take longer than this. A parser that backtracks
/// exponentially passes a no-panic test and is still a denial of service.
const PER_INPUT: Duration = Duration::from_millis(200);

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

const SEEDS: &[&str] = &[
    "int arith8(unsigned char a, unsigned char b)",
    "struct header { uint32_t magic; uint16_t len; char name[16]; };",
    "typedef struct node { struct node *next; int value; } node_t;",
    "void *(*handler)(int, char **)",
    "union v { uint64_t bits; double d; };",
    "enum kind { A = 1, B, C = 10 };",
    "struct f { uint32_t a : 3; uint32_t b : 5; };",
    "const volatile char *const *p",
    "int main(int argc, char *argv[])",
    "#define X 1\n/* comment */ static inline int f(void);",
];

/// The characters that actually break a C parser, rather than random bytes.
const INTERESTING: &[u8] = b"*()[]{},;:.<>#\\\"'/=+-~!&^|%?\n\t ";

fn mutate(seed: &str, rng: &mut Rng) -> String {
    let mut v = seed.as_bytes().to_vec();
    if v.is_empty() {
        return String::new();
    }
    match rng.below(7) {
        // Truncation: the commonest way a declaration arrives half-typed.
        0 => v.truncate(rng.below(v.len())),
        1 => {
            let i = rng.below(v.len());
            v[i] = INTERESTING[rng.below(INTERESTING.len())];
        }
        2 => {
            let i = rng.below(v.len());
            v.insert(i, INTERESTING[rng.below(INTERESTING.len())]);
        }
        3 => {
            let i = rng.below(v.len());
            v.remove(i);
        }
        // Deep nesting, which is where a recursive descent parser dies.
        4 => {
            let n = 1 + rng.below(2000);
            let mut s = b"int ".to_vec();
            s.extend(std::iter::repeat_n(b'(', n));
            s.extend_from_slice(b"*x");
            s.extend(std::iter::repeat_n(b')', n));
            v = s;
        }
        5 => {
            let n = 1 + rng.below(2000);
            let mut s = b"int x".to_vec();
            s.extend(std::iter::repeat_n(b'*', n));
            v = s;
        }
        // Repetition, which is how a quadratic loop shows up.
        _ => {
            let times = 1 + rng.below(40);
            let mut s = Vec::new();
            for _ in 0..times {
                s.extend_from_slice(&v);
            }
            v = s;
        }
    }
    String::from_utf8_lossy(&v).into_owned()
}

fn drive(text: &str) {
    let started = Instant::now();
    let mut types = Types::new();
    // Every entry point, because each one has its own recovery.
    let _ = cdecl::declaration(&mut types, text);
    let _ = cdecl::prototype(&mut types, text);
    let _ = cdecl::translation_unit(&mut types, text);
    let unit = cdecl::header(&mut types, text);
    // The recovering reader must always terminate, and must account for what
    // it did not read rather than dropping it.
    assert!(unit.attempted() <= text.len() + 1);
    let took = started.elapsed();
    assert!(
        took < PER_INPUT,
        "{:?} took {took:?}, which is not a bounded parse",
        text.chars().take(80).collect::<String>()
    );
}

#[test]
fn no_declaration_text_panics_or_runs_long() {
    let mut rng = Rng(0x1234_5678_9abc_def0);
    let started = Instant::now();
    let mut cases = 0usize;
    while started.elapsed() < BUDGET {
        let seed = SEEDS[rng.below(SEEDS.len())];
        drive(&mutate(seed, &mut rng));
        cases += 1;
    }
    assert!(cases > 500, "only {cases} cases fit in the budget");
}

#[test]
fn every_prefix_of_every_seed_is_survivable() {
    // Truncation deserves an exhaustive pass rather than a sampled one: it is
    // exactly what a half-typed command line looks like.
    for seed in SEEDS {
        for n in 0..=seed.len() {
            if !seed.is_char_boundary(n) {
                continue;
            }
            drive(&seed[..n]);
        }
    }
}

#[test]
fn pathological_nesting_is_refused_rather_than_crashing() {
    let mut types = Types::new();
    let deep = format!("int {}{}{}", "(".repeat(5000), "*x", ")".repeat(5000));
    assert!(cdecl::declaration(&mut types, &deep).is_err());
    let stars = format!("int {}x", "*".repeat(5000));
    // A long chain of pointers is legal and must not be refused for depth,
    // because it is a loop rather than a recursion.
    assert!(cdecl::declaration(&mut types, &stars).is_ok());
    let braces = "struct s {".repeat(5000);
    assert!(cdecl::declaration(&mut types, &braces).is_err());
    let expr = format!("int x[{}1{}]", "(".repeat(5000), ")".repeat(5000));
    assert!(cdecl::declaration(&mut types, &expr).is_err());
}
