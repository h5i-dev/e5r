//! Every declaration this parser reads must print as a declaration it reads
//! back to the same type.
//!
//! The property matters beyond tidiness. The annotation log stores an
//! assertion as the text a person typed, the decompiler prints types with
//! `Types::declare`, and a type archive is a set of declarations written out
//! and read in again. If printing and parsing disagree anywhere, a type
//! silently changes on the way through a file somebody reviews in a diff.
//!
//! Two normalizations are deliberate and are checked rather than worked
//! around: a parameter declared as an array is a pointer, because that is what
//! is passed, and `const int a[3]` is an array of `const int` rather than a
//! `const` array, because that is what C says it is. Both are idempotent, so
//! the second pass through is stable.

use r12e_types::cdecl;
use r12e_types::ctype::{Type, TypeId, Types};

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

/// A store holding the named types the generated corpus refers to.
fn seeded() -> Types {
    let mut t = Types::new();
    for text in [
        "struct point { int32_t x; int32_t y; char tag; };",
        "union bits { uint64_t whole; double d; };",
        "enum kind { A = 1, B, C = 10 };",
        "typedef uint32_t word;",
        "typedef struct node { struct node *next; int value; } node_t;",
    ] {
        cdecl::translation_unit(&mut t, text).unwrap_or_else(|e| panic!("{text}: {e}"));
    }
    t
}

/// The named types, plus the basic ones, as leaves for the generator.
fn leaves(t: &mut Types) -> Vec<TypeId> {
    let mut out = vec![
        t.add(Type::Bool),
        t.add(Type::Float { size: 4 }),
        t.add(Type::Float { size: 8 }),
        t.add(Type::Float { size: 16 }),
    ];
    for size in [1u8, 2, 4, 8] {
        for signed in [true, false] {
            out.push(t.add(Type::Int { size, signed }));
        }
    }
    out.push(t.composite(false, "point").unwrap());
    out.push(t.composite(true, "bits").unwrap());
    out.push(t.enumeration("kind").unwrap());
    out.push(t.typedef("word").unwrap());
    out.push(t.typedef("node_t").unwrap());
    out
}

/// A type that may be declared as an object: complete, and neither a function
/// nor `void`.
fn object(t: &mut Types, base: &[TypeId], rng: &mut Rng, depth: u32) -> TypeId {
    if depth == 0 {
        return base[rng.below(base.len())];
    }
    match rng.below(6) {
        0 => {
            let inner = any(t, base, rng, depth - 1);
            let p = t.pointer(inner);
            // A qualifier on the pointer itself, which is the half of
            // `int *const` people get backwards.
            maybe_qualify(t, p, rng, true)
        }
        1 => {
            let inner = object(t, base, rng, depth - 1);
            let n = 1 + rng.below(8) as u64;
            t.add(Type::Array(inner, Some(n)))
        }
        2 => {
            let inner = object(t, base, rng, depth - 1);
            // Not over an array or a function: C rewrites `const int a[3]` as
            // an array of `const int`, and the parser produces that form.
            if matches!(
                t.get(inner),
                Some(Type::Array(..)) | Some(Type::Function(_))
            ) {
                return inner;
            }
            maybe_qualify(t, inner, rng, false)
        }
        _ => base[rng.below(base.len())],
    }
}

/// Anything a pointer may point at, which adds functions and `void`.
fn any(t: &mut Types, base: &[TypeId], rng: &mut Rng, depth: u32) -> TypeId {
    match rng.below(8) {
        0 => Types::VOID,
        1 if depth > 0 => {
            let returns = match rng.below(4) {
                0 => None,
                // A function returns neither an array nor another function, so
                // generating one would be generating text C has no spelling
                // for rather than exercising the round trip.
                _ => Some(scalarish(t, base, rng, depth - 1)),
            };
            let count = rng.below(4);
            let mut parameters = Vec::new();
            for n in 0..count {
                // Arrays and functions decay to pointers as parameters, so
                // generating one would be testing the decay rather than the
                // round trip; both are covered by their own test.
                let ty = scalarish(t, base, rng, depth - 1);
                parameters.push((Some(format!("p{n}")), ty));
            }
            let varargs = !parameters.is_empty() && rng.below(4) == 0;
            t.add(Type::Function(r12e_types::ctype::Signature {
                returns,
                parameters,
                varargs,
            }))
        }
        _ => object(t, base, rng, depth),
    }
}

/// An object type that is neither an array nor a function, which is what a
/// parameter decays to and the only thing a function may return.
fn scalarish(t: &mut Types, base: &[TypeId], rng: &mut Rng, depth: u32) -> TypeId {
    let mut ty = object(t, base, rng, depth);
    while matches!(
        t.get(t.resolve(ty)),
        Some(Type::Array(..)) | Some(Type::Function(_))
    ) {
        ty = base[rng.below(base.len())];
    }
    ty
}

fn maybe_qualify(t: &mut Types, id: TypeId, rng: &mut Rng, pointer: bool) -> TypeId {
    let pick = rng.below(8);
    let q = r12e_types::ctype::Qualifiers {
        is_const: pick & 1 != 0,
        is_volatile: pick & 2 != 0,
        // `restrict` only ever applies to a pointer.
        is_restrict: pointer && pick & 4 != 0,
    };
    t.qualified(id, q)
}

#[test]
fn a_generated_corpus_prints_and_parses_back_to_itself() {
    let mut t = seeded();
    let base = leaves(&mut t);
    let mut rng = Rng(0x5eed_1234_9876_abcd);
    let mut checked = 0usize;
    for _ in 0..4000 {
        let depth = 1 + rng.below(3) as u32;
        let id = object(&mut t, &base, &mut rng, depth);
        let text = t.declare(id, "subject");
        let parsed = match cdecl::declaration(&mut t, &text) {
            Ok(d) => d,
            Err(e) => panic!("`{text}` came out of the printer and would not parse: {e}"),
        };
        assert_eq!(
            parsed.ty,
            id,
            "`{text}` parsed back as `{}`",
            t.name_of(parsed.ty)
        );
        assert_eq!(
            t.declare(parsed.ty, "subject"),
            text,
            "printing is not stable"
        );
        checked += 1;
    }
    assert!(checked >= 4000);
}

#[test]
fn the_declarations_an_analyst_types_survive_the_trip() {
    let corpus = [
        "int arith8(unsigned char a, unsigned char b)",
        "struct header { uint32_t magic; uint16_t len; char name[16]; };",
        "typedef struct node { struct node *next; int value; } node_t;",
        "void *(*handler)(int, char **)",
        "union v { uint64_t bits; double d; };",
        "enum kind { A = 1, B, C = 10 };",
        "const char *const *environ",
        "int (*compare)(const void *, const void *)",
        "unsigned long long counter",
        "volatile int *volatile flag",
        "struct packet { uint8_t version : 4; uint8_t kind : 4; uint16_t length; };",
        "char *strncpy(char *dst, const char *src, unsigned long n)",
        "int printf(const char *fmt, ...)",
        "double (*matrix)[4]",
        "void free(void *)",
    ];
    for text in corpus {
        let mut t = Types::new();
        let first = cdecl::declaration(&mut t, text)
            .unwrap_or_else(|e| panic!("{text:?} should parse: {e}"));
        let printed = print_back(&t, &first);
        let mut again = Types::new();
        let second = cdecl::declaration(&mut again, &printed)
            .unwrap_or_else(|e| panic!("{printed:?} came from {text:?} and would not parse: {e}"));
        let reprinted = print_back(&again, &second);
        assert_eq!(
            printed, reprinted,
            "{text:?} is not stable through a second pass"
        );
    }
}

/// Write a parsed declaration back out the way the text it came from spelled
/// it. Both passes go through this, because a second pass that printed by a
/// different rule would be comparing two printers rather than the round trip.
fn print_back(t: &Types, d: &cdecl::Declaration) -> String {
    match &d.name {
        // A typedef and a tagged type each define themselves; anything else is
        // a declaration of a name with a type.
        Some(n) if d.typedef => t
            .definition(d.ty)
            .unwrap_or_else(|| format!("typedef {};", t.declare(d.ty, n))),
        Some(n) => format!("{};", t.declare(d.ty, n)),
        None => t.definition(d.ty).expect("a tagged type defines itself"),
    }
}

#[test]
fn a_whole_archive_of_types_writes_out_and_reads_back() {
    // What a type archive does: print every definition in dependency order,
    // then read the printed text into a fresh store and get the same types.
    let mut t = Types::new();
    cdecl::translation_unit(
        &mut t,
        "typedef struct node { struct node *next; int value; } node_t;
         struct outer { node_t *head; enum kind { A = 1, B } k; union v { int i; float f; } u; };",
    )
    .expect("an archive");
    let outer = t.composite(false, "outer").expect("the tag");
    let mut text = String::new();
    for id in t.dependencies(outer) {
        if let Some(d) = t.definition(id) {
            text.push_str(&d);
            text.push('\n');
        }
    }
    let mut again = Types::new();
    cdecl::translation_unit(&mut again, &text)
        .unwrap_or_else(|e| panic!("the printed archive would not parse: {e}\n{text}"));
    let there = again.composite(false, "outer").expect("the tag again");
    assert_eq!(again.size_of(there), t.size_of(outer));
    assert_eq!(again.name_of(there), t.name_of(outer));
}
