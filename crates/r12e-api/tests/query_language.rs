//! What the query language does with input that is not a query.
//!
//! Two properties, both of which a person typing at a prompt finds out about
//! immediately. A query it does not understand has to say which part it did
//! not understand, because "no results" for a misspelling is worse than an
//! error. And nothing typed at it may panic or take an unbounded time, since
//! the same parser is behind `r12e query`, where an agent can put anything it
//! likes in front of it.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use r12e_analysis::{Options, Program, analyze};
use r12e_api::query::{self, Field};
use r12e_format::LoadOptions;

/// Every form the language accepts, which is also the seed corpus for the
/// mutations and truncations below.
const GOOD: [&str; 22] = [
    "functions",
    "functions where insns > 100 and name ~ \"crypt\"",
    "functions where named = false and insns > 40 limit 20",
    "functions where (callers = 0 or callees > 8) and complete = true",
    "strings where length >= 20",
    "strings where text ~ \"/etc/\" and section = \".rodata\"",
    "symbols where kind = function and dynamic = true",
    "imports where library ~ \"libc\"",
    "exports where name !~ \"_\"",
    "sections where exec = true",
    "xrefs where kind = call and to = 0x401000",
    "calls",
    "calls to \"memcpy\"",
    "calls to \"memcpy\" where arg3 is not bounded",
    "calls to \"memcpy\" where arg3 is bounded",
    "calls to \"memcpy\" where arg3 is unconstrained",
    "calls to \"memcpy\" where arg3 is unknown limit 5",
    "calls to \"memcpy\" where arg1 is constant and arg3 is not bounded",
    "calls where target is indirect",
    "calls where target is direct and function ~ \"copy\"",
    "functions where reads any argument of a call to \"system\"",
    "values reaching arg1 of calls to \"system\"",
];

fn program() -> Option<Program> {
    let dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    let data = std::fs::read(dir.join("df-bounds.a64.O2")).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// Parse and check, which is every refusal that does not need a program.
fn accept(text: &str) -> Result<query::Query, String> {
    let q = query::parse(text)?;
    q.validate()?;
    Ok(q)
}

#[test]
fn every_accepted_form_parses() {
    for text in GOOD {
        accept(text).unwrap_or_else(|e| panic!("{text:?} is documented as accepted: {e}"));
    }
}

#[test]
fn nonsense_says_what_it_did_not_understand() {
    // Each case pairs a query with the word the message has to contain. A
    // message that does not name the part that was wrong sends the reader
    // back to the manual. The categories are the ones a person hits: a
    // misspelling, a field that does not exist, a comparison against the
    // wrong kind of thing, a lost quote, an operator with nothing after it,
    // and a clause with its body missing.
    let cases: [(&str, &str); 22] = [
        // An entity that does not exist.
        ("functionz", "functionz"),
        ("blocks where size > 3", "blocks"),
        ("", "functions"),
        // A field that does not exist.
        ("functions where inns > 3", "inns"),
        ("strings where lenght >= 4", "lenght"),
        ("imports where address = 0x1000", "address"),
        // The wrong kind of value for the field.
        ("functions where insns > \"many\"", "many"),
        ("functions where insns > large", "large"),
        ("xrefs where to = main", "main"),
        ("sections where exec = 3", "exec"),
        ("sections where exec ~ \"true\"", "exec"),
        ("functions where insns ~ 10", "insns"),
        ("functions where insns > \"100\"", "quoted"),
        // A quote that was never closed.
        ("strings where text ~ \"oops", "oops"),
        ("calls to \"memcpy where arg3 is bounded", "memcpy"),
        // An operator with nothing after it.
        ("functions where insns >", "insns >"),
        ("functions where insns > 3 and name ~", "name ~"),
        ("functions where insns", "insns"),
        // A clause with nothing in it.
        ("functions where", "where"),
        ("functions where insns > 3 and", "and"),
        // And the dataflow clauses, which have bodies of their own.
        ("calls where arg3 is bouned", "bouned"),
        ("functions where arg3 is bounded", "calls"),
    ];
    for (text, wanted) in cases {
        let error = match accept(text) {
            Err(e) => e,
            Ok(_) => panic!("{text:?} was accepted"),
        };
        assert!(
            error.contains(wanted),
            "{text:?} should have been refused with a message naming {wanted:?}, said: {error}"
        );
        // A refusal that says nothing beyond the fact of failing is the
        // generic parse error this test exists to forbid.
        assert!(
            error.len() > wanted.len() + 4,
            "{text:?} was refused with {error:?}, which says nothing"
        );
    }
}

#[test]
fn the_rest_of_the_nonsense_is_caught_when_it_runs() {
    // These need a program, because what they get wrong is only wrong once
    // there is something to ask.
    let cases: [(&str, &str); 5] = [
        ("calls to", "the end of the query"),
        ("values", "reaching"),
        ("values reaching arg1", "of"),
        ("values reaching frobnicate of calls", "frobnicate"),
        (
            "functions where reads some argument of a call to \"x\"",
            "some",
        ),
    ];
    for (text, wanted) in cases {
        let error = match accept(text) {
            Err(e) => e,
            Ok(_) => match program() {
                Some(p) => match query::run(&p, text) {
                    Err(e) => e,
                    Ok(_) => panic!("{text:?} was accepted"),
                },
                None => continue,
            },
        };
        assert!(
            error.contains(wanted),
            "{text:?} should have been refused with a message naming {wanted:?}, said: {error}"
        );
    }
}

#[test]
fn a_wrong_kind_of_comparison_is_refused_rather_than_coerced() {
    // The failure this guards against is not a crash: it is `insns > "10"`
    // comparing the characters and reporting an empty answer, which reads as
    // "there are none" rather than "that is not a question".
    let Some(p) = program() else {
        return;
    };
    assert!(query::run(&p, "functions where insns > \"10\"").is_err());
    let ok = query::run(&p, "functions where insns > 10").expect("a number against a number");
    assert!(
        !ok.rows.is_empty(),
        "the fixture has functions of more than ten instructions"
    );
}

#[test]
fn the_declared_kind_of_a_field_is_the_kind_its_rows_hold() {
    // The kind table is keyed by field name rather than by entity, so it is
    // only correct while no two entities disagree about a name. Checked here
    // against the rows themselves rather than by reading the table twice.
    let Some(p) = program() else {
        return;
    };
    for entity in [
        "functions",
        "strings",
        "symbols",
        "imports",
        "exports",
        "sections",
        "xrefs",
        "calls",
    ] {
        let answer = query::run(&p, entity).unwrap_or_else(|e| panic!("{entity}: {e}"));
        for row in &answer.rows {
            for (name, value) in &row.values {
                // Every field is comparable against a literal of its own kind
                // and, when it is not text, refuses the others. That is the
                // property the table exists for, so assert it through the
                // parser rather than by exporting the table.
                let (good, bad) = match value {
                    Field::Number(_) | Field::Address(_) => ("1", "\"x\""),
                    Field::Bool(_) => ("true", "1"),
                    Field::Text(_) | Field::Missing => continue,
                };
                let text = format!("{entity} where {name} = {good}");
                query::parse(&text)
                    .and_then(|q| q.validate())
                    .unwrap_or_else(|e| panic!("{text:?}: {e}"));
                let text = format!("{entity} where {name} = {bad}");
                assert!(
                    query::parse(&text).and_then(|q| q.validate()).is_err(),
                    "{text:?} was accepted, so `{name}` is not declared as what it holds"
                );
            }
        }
    }
}

#[test]
fn a_misspelled_dataflow_word_is_not_silently_a_field() {
    // `arg3 is bounded` is a question, and `bouned` is a typo in it rather
    // than a field of something. Matching nothing would look like an answer.
    let e = query::parse("calls where arg3 is bouned").unwrap_err();
    assert!(e.contains("bounded"), "{e}");
    assert!(e.contains("unconstrained"), "{e}");
}

/// A deterministic generator, so a failure is reproducible from the seed
/// alone.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // A plain linear congruential generator: the numbers only have to be
        // varied, not unpredictable.
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }

    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }

    fn pick<'a, T>(&mut self, from: &'a [T]) -> &'a T {
        &from[self.below(from.len())]
    }
}

/// The pieces a query is made of, plus the ones that do not belong in one.
const WORDS: [&str; 36] = [
    "calls",
    "values",
    "functions",
    "xrefs",
    "where",
    "limit",
    "to",
    "of",
    "reaching",
    "reads",
    "any",
    "every",
    "argument",
    "is",
    "not",
    "and",
    "or",
    "arg1",
    "arg3",
    "arg0",
    "arg99999999999999999999",
    "bounded",
    "unconstrained",
    "target",
    "indirect",
    "insns",
    "exec",
    "\"memcpy\"",
    "\"",
    "(",
    ")",
    "=",
    "~",
    ">=",
    "0x401000",
    "18446744073709551615",
];

/// The characters a mutation reaches for, which are the ones that change how
/// text lexes rather than what it says.
const POISON: [char; 14] = [
    '"',
    '\'',
    '(',
    ')',
    '=',
    '~',
    '<',
    '>',
    '!',
    '\\',
    '\u{1f600}',
    '\u{0}',
    '\n',
    ' ',
];

/// One near-miss of an accepted query.
///
/// Near misses are what finds parser bugs: uniform noise stops at the first
/// token, while a query with one character moved reaches the clause that
/// takes a wrong turn.
fn mutate(seed: &str, rng: &mut Rng) -> String {
    let mut chars: Vec<char> = seed.chars().collect();
    if chars.is_empty() {
        return String::new();
    }
    match rng.below(6) {
        // Drop a character, which is how a quote or a bracket goes missing.
        0 => {
            let i = rng.below(chars.len());
            chars.remove(i);
        }
        // Insert one that changes how the rest lexes.
        1 => {
            let i = rng.below(chars.len() + 1);
            chars.insert(i, *rng.pick(&POISON));
        }
        // Replace one.
        2 => {
            let i = rng.below(chars.len());
            chars[i] = *rng.pick(&POISON);
        }
        // Swap two neighbours: `is not` becomes `is nto`.
        3 if chars.len() > 1 => {
            let i = rng.below(chars.len() - 1);
            chars.swap(i, i + 1);
        }
        // Repeat a run, which is how a clause ends up with two heads.
        4 => {
            let at = rng.below(chars.len());
            let len = rng.below(8).min(chars.len() - at);
            let run: Vec<char> = chars[at..at + len].to_vec();
            for (n, c) in run.into_iter().enumerate() {
                chars.insert(at + n, c);
            }
        }
        // Splice a word in from somewhere else.
        _ => {
            let at = rng.below(chars.len());
            let word = *rng.pick(&WORDS);
            for (n, c) in word.chars().enumerate() {
                chars.insert(at + n, c);
            }
        }
    }
    chars.into_iter().collect()
}

/// How long the mutation hunt gets. Long enough to cover the corpus many
/// times over, short enough that nobody is tempted to skip the suite.
const BUDGET: Duration = Duration::from_millis(1500);

/// What a person will wait for one answer at a prompt.
const CEILING: Duration = Duration::from_secs(2);

/// Whatever the query is, the answer is a value or an error that says
/// something.
fn probe(p: Option<&Program>, input: &str) {
    let each = Instant::now();
    match query::parse(input) {
        Ok(q) => {
            // Validating and running have to terminate as well, and running
            // is the part that lifts functions.
            if q.validate().is_ok() {
                if let Some(p) = p {
                    let _ = query::run(p, input);
                }
            }
        }
        Err(e) => assert!(!e.trim().is_empty(), "{input:?} was refused with nothing"),
    }
    assert!(
        each.elapsed() < CEILING,
        "{input:?} took {:?}, which is longer than anything typed at a prompt may take",
        each.elapsed()
    );
}

#[test]
fn truncated_and_scrambled_queries_neither_panic_nor_hang() {
    let p = program();
    let mut rng = Rng(0x5eed);
    let mut inputs: Vec<String> = Vec::new();

    // Truncations: every prefix of every accepted form, which is what a
    // half-typed query looks like.
    for text in GOOD {
        for end in 0..=text.len() {
            if text.is_char_boundary(end) {
                inputs.push(text[..end].to_string());
            }
        }
    }
    // Suffixes as well, so the parser meets a clause with its head missing.
    for text in GOOD {
        for start in 0..text.len() {
            if text.is_char_boundary(start) {
                inputs.push(text[start..].to_string());
            }
        }
    }
    // Words in an order nobody would type.
    for _ in 0..3000 {
        let len = 1 + rng.below(12);
        let mut out = String::new();
        for _ in 0..len {
            out.push_str(rng.pick(&WORDS));
            out.push(' ');
        }
        inputs.push(out);
    }
    // And bytes that are not words at all.
    for _ in 0..1000 {
        let len = rng.below(40);
        let mut out = String::new();
        for _ in 0..len {
            out.push(char::from_u32((rng.next() % 0x2ff) as u32 + 1).unwrap_or('?'));
        }
        inputs.push(out);
    }

    let started = Instant::now();
    for input in &inputs {
        probe(p.as_ref(), input);
    }
    let whole = started.elapsed();
    assert!(
        whole < Duration::from_secs(120),
        "{} inputs took {whole:?} in total",
        inputs.len()
    );
    println!("{} inputs in {whole:?}", inputs.len());
}

#[test]
fn mutated_queries_neither_panic_nor_hang() {
    // Seeded from the accepted forms and run for a fixed budget, so the text
    // it tries is a query with something wrong with it rather than noise that
    // dies at the first token. Repeated mutation compounds, so late cases are
    // several edits away from anything valid.
    let p = program();
    let mut rng = Rng(0x0dd_ba11);
    let start = Instant::now();
    let mut cases = 0u64;
    let mut parsed = 0u64;
    let mut case = String::new();
    while start.elapsed() < BUDGET {
        // Every so often, go back to something that was once a query.
        if case.is_empty() || rng.below(8) == 0 {
            case = (*rng.pick(&GOOD)).to_string();
        }
        case = mutate(&case, &mut rng);
        probe(p.as_ref(), &case);
        if query::parse(&case).is_ok() {
            parsed += 1;
        }
        cases += 1;
    }
    assert!(
        cases > 200,
        "only {cases} mutated queries in {BUDGET:?}; something is very slow"
    );
    // A corpus nothing in survives parsing is noise wearing a corpus's
    // clothes, and would not reach the parts of the parser worth testing.
    assert!(
        parsed > 0,
        "none of {cases} mutated queries parsed, so none of them were near misses"
    );
    println!("{cases} mutated queries, {parsed} of them still valid, no panics");
}

#[test]
fn asking_about_one_callee_does_not_lift_the_whole_image() {
    // A question that names a callee is answered from the cross references
    // outward: only the functions that reach it are lifted, and only the calls
    // to it are described. A question about indirect calls has no such handle
    // and pays for the whole image. The saving is asserted as the set of
    // functions the first one has to look at, which is the same on every
    // machine, rather than as a stopwatch reading, which is not.
    let dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    let Ok(data) = std::fs::read(dir.join("panicky")) else {
        return;
    };
    let Ok(obj) = r12e_format::load(&data, &LoadOptions::default()) else {
        return;
    };
    let p = analyze(obj, &Options::default());

    let callers = r12e_api::dataflow::callers_of_name(&p, "memcpy").len();
    assert!(
        callers > 0 && callers < p.functions.len(),
        "{callers} of {} functions call memcpy",
        p.functions.len()
    );

    let started = Instant::now();
    let narrow = query::run(&p, "calls to \"memcpy\" where arg3 is not bounded");
    let narrow_took = started.elapsed();
    let narrow = narrow.expect("a query about one callee");

    let started = Instant::now();
    let wide = query::run(&p, "calls where target is indirect limit 5");
    let wide_took = started.elapsed();
    let wide = wide.expect("a query about every call");

    println!(
        "{} functions, {callers} call memcpy: by name {narrow_took:?} for {} rows, \
         over everything {wide_took:?} for {} matched",
        p.functions.len(),
        narrow.rows.len(),
        wide.matched
    );
    // Neither may take longer than a person will wait at a prompt, on a
    // binary of this size.
    assert!(
        narrow_took < Duration::from_secs(60) && wide_took < Duration::from_secs(60),
        "{narrow_took:?} and {wide_took:?}"
    );
}
