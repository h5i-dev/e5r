//! Applied types in the annotation log.
//!
//! The log stores a type as the text a person typed, and parses it on read.
//! What makes that a decision rather than a shrug is the check on the way in:
//! a typo is refused at the moment it is typed, when the person who made it is
//! still there, instead of sitting in the file forever being ignored.

use r12e_core::Addr;
use r12e_db::anchor::Anchor;
use r12e_db::log::{Declared, Field, Log, declared};
use r12e_types::ctype::{Type, Types};

fn anchor(n: u64) -> Anchor {
    Anchor {
        shape: 0x1000 + n,
        bytes: 0x2000 + n,
        insns: 12,
        abs: Addr(0x40_0000 + n * 0x10),
        offset: 0,
    }
}

#[test]
fn a_valid_declaration_is_accepted_and_read_back_as_a_prototype() {
    let mut log = Log::new();
    log.assert_checked(
        anchor(1),
        Field::Type,
        Some("int arith8(unsigned char a, unsigned char b)".into()),
        "ht",
    )
    .expect("a declaration an analyst would type");

    let stored = log.records()[0].value.clone().expect("the source text");
    let mut types = Types::new();
    let Declared::Function {
        name, signature, ..
    } = declared(&mut types, &stored).expect("it parses on read")
    else {
        panic!("a function declaration")
    };
    assert_eq!(name.as_deref(), Some("arith8"));
    assert_eq!(signature.parameters.len(), 2);
    assert_eq!(
        types.get(signature.parameters[0].1),
        Some(&Type::Int {
            size: 1,
            signed: false
        })
    );
}

#[test]
fn a_type_on_a_data_object_is_a_bare_type_name() {
    let mut log = Log::new();
    for text in [
        "struct header",
        "uint32_t [16]",
        "void (*)(int)",
        "const char *",
        "struct header { uint32_t magic; uint16_t len; };",
    ] {
        log.assert_checked(anchor(2), Field::Type, Some(text.into()), "ht")
            .unwrap_or_else(|e| panic!("{text:?} should be accepted: {e}"));
    }
    let mut types = Types::new();
    let d = declared(&mut types, "uint32_t [16]").expect("an array of sixteen words");
    assert_eq!(types.size_of(d.ty()), Some(64));
    assert!(matches!(d, Declared::Object { .. }));
}

#[test]
fn a_typo_is_refused_at_the_moment_it_is_typed() {
    let mut log = Log::new();
    let e = log
        .assert_checked(
            anchor(3),
            Field::Type,
            Some("int arith8(unsinged char a)".into()),
            "ht",
        )
        .expect_err("a misspelled type is not a type");
    let message = format!("{e}");
    assert!(message.contains("unsinged"), "{message}");
    assert!(log.is_empty(), "nothing was written");

    for bad in ["int f(", "struct { ", "int 3x", "??"] {
        assert!(
            log.assert_checked(anchor(3), Field::Type, Some(bad.into()), "ht")
                .is_err(),
            "{bad:?} should have been refused"
        );
    }
    assert!(log.is_empty());
}

#[test]
fn a_name_is_checked_too_and_a_comment_is_not() {
    let mut log = Log::new();
    assert!(
        log.assert_checked(anchor(4), Field::Name, Some("  ".into()), "ht")
            .is_err()
    );
    assert!(
        log.assert_checked(anchor(4), Field::Name, Some("a\nb".into()), "ht")
            .is_err()
    );
    // A demangled C++ name is full of punctuation and is a perfectly good name.
    log.assert_checked(
        anchor(4),
        Field::Name,
        Some("std::vector<int>::push_back(int const&)".into()),
        "ht",
    )
    .expect("a demangled name");
    // A comment is prose and is nobody's business to validate.
    log.assert_checked(
        anchor(4),
        Field::Comment,
        Some("looks like a ??? state machine".into()),
        "ht",
    )
    .expect("a comment");
}

#[test]
fn clearing_a_field_needs_no_value_to_check() {
    let mut log = Log::new();
    log.assert_checked(anchor(5), Field::Type, Some("int f(void)".into()), "ht")
        .unwrap();
    log.assert_checked(anchor(5), Field::Type, None, "ht")
        .expect("a tombstone clears the field");
    assert!(log.fold().is_empty());
}

#[test]
fn reading_a_log_never_rejects_what_writing_would_have() {
    // A log written by a newer build, or hand-edited, must still fold. Refusing
    // the whole file because one type no longer parses would throw away the
    // names and comments beside it, which is the opposite of what the store is
    // for.
    let mut log = Log::new();
    log.assert(
        anchor(6),
        Field::Type,
        Some("_Atomic(int) f(void) [[weird]]".into()),
        "someone",
    );
    log.assert(
        anchor(6),
        Field::Name,
        Some("parse_header".into()),
        "someone",
    );
    let text = log.to_text();
    let back = Log::from_text(&text).expect("it reads");
    assert_eq!(back.records().len(), 2);
    assert_eq!(back.to_text(), text);

    // And the unreadable type is reported when something asks for it, rather
    // than crashing whatever asked.
    let mut types = Types::new();
    assert!(declared(&mut types, "_Atomic(int) f(void) [[weird]]").is_err());
}

#[test]
fn the_source_text_is_what_survives_into_the_file() {
    // Keeping the text rather than a serialized type is what makes the log
    // reviewable in a diff, and what lets the parser improve without anybody
    // rewriting history.
    let mut log = Log::new();
    let source = "typedef struct node { struct node *next; int value; } node_t;";
    log.assert_checked(anchor(7), Field::Type, Some(source.into()), "ht")
        .expect("a typedef");
    let text = log.to_text();
    assert!(text.contains("struct node *next"), "{text}");
    let back = Log::from_text(&text).unwrap();
    assert_eq!(back.records()[0].value.as_deref(), Some(source));
}
