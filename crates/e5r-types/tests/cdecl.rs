//! The C declaration grammar, checked against the declarations an analyst
//! actually types and against the ones that are easy to get backwards.

use e5r_types::cdecl::{self, Storage};
use e5r_types::ctype::{Model, Type, Types};

fn parse(text: &str) -> (Types, cdecl::Declaration) {
    let mut t = Types::new();
    let d =
        cdecl::declaration(&mut t, text).unwrap_or_else(|e| panic!("{text:?} should parse: {e}"));
    (t, d)
}

fn refused(text: &str) -> String {
    let mut t = Types::new();
    match cdecl::declaration(&mut t, text) {
        Ok(_) => panic!("{text:?} should have been refused"),
        Err(e) => e.message,
    }
}

#[test]
fn a_prototype_gives_its_parameters_their_widths() {
    let mut t = Types::new();
    let (name, sig) = cdecl::prototype(&mut t, "int arith8(unsigned char a, unsigned char b)")
        .expect("a prototype");
    assert_eq!(name.as_deref(), Some("arith8"));
    assert_eq!(sig.parameters.len(), 2);
    assert_eq!(sig.parameters[0].0.as_deref(), Some("a"));
    assert_eq!(
        t.get(sig.parameters[0].1),
        Some(&Type::Int {
            size: 1,
            signed: false
        })
    );
    assert_eq!(t.size_of(sig.returns.unwrap()), Some(4));
    assert!(!sig.varargs);
}

#[test]
fn a_declarator_binds_the_way_c_says_and_not_the_way_it_reads() {
    // The one everybody gets wrong: an array of pointers, not a pointer to an
    // array.
    let (t, d) = parse("char *argv[]");
    let Some(Type::Array(inner, None)) = t.get(d.ty) else {
        panic!("argv should be an array, got {}", t.name_of(d.ty))
    };
    assert!(matches!(t.get(*inner), Some(Type::Pointer(_))));

    let (t, d) = parse("char (*argv)[8]");
    let Some(Type::Pointer(inner)) = t.get(d.ty) else {
        panic!("should be a pointer, got {}", t.name_of(d.ty))
    };
    assert!(matches!(t.get(*inner), Some(Type::Array(_, Some(8)))));
}

#[test]
fn a_function_pointer_round_trips_through_its_own_spelling() {
    let (t, d) = parse("void *(*handler)(int, char **)");
    assert_eq!(d.name.as_deref(), Some("handler"));
    assert_eq!(
        t.declare(d.ty, "handler"),
        "void *(*handler)(int32_t, int8_t **)"
    );
}

#[test]
fn a_structure_is_laid_out_the_way_the_target_does() {
    let (t, d) = parse("struct header { uint32_t magic; uint16_t len; char name[16]; };");
    let Some(Type::Composite(c)) = t.get(d.ty) else {
        panic!("a structure")
    };
    let offsets: Vec<u64> = c.fields.iter().map(|f| f.offset).collect();
    assert_eq!(offsets, vec![0, 4, 6]);
    assert_eq!(c.size, Some(24));
    assert_eq!(t.align_of(d.ty), Some(4));
}

#[test]
fn a_self_referential_structure_resolves_to_itself() {
    let mut t = Types::new();
    let d = cdecl::declaration(
        &mut t,
        "typedef struct node { struct node *next; int value; } node_t;",
    )
    .expect("a linked list node");
    assert!(d.typedef);
    let inner = t.resolve(d.ty);
    let Some(Type::Composite(c)) = t.get(inner) else {
        panic!("a structure")
    };
    let Some(Type::Pointer(to)) = t.get(c.fields[0].ty) else {
        panic!("next is a pointer")
    };
    assert_eq!(
        *to, inner,
        "the pointer points back at the structure itself"
    );
    assert_eq!(c.size, Some(16));
}

#[test]
fn a_union_starts_every_member_at_zero() {
    let (t, d) = parse("union v { uint64_t bits; double d; };");
    let Some(Type::Composite(c)) = t.get(d.ty) else {
        panic!("a union")
    };
    assert!(c.union);
    assert!(c.fields.iter().all(|f| f.offset == 0));
    assert_eq!(c.size, Some(8));
}

#[test]
fn an_enumeration_counts_on_from_what_it_was_given() {
    let (t, d) = parse("enum kind { A = 1, B, C = 10 };");
    let Some(Type::Enum(e)) = t.get(d.ty) else {
        panic!("an enumeration")
    };
    assert_eq!(
        e.values,
        vec![("A".into(), 1), ("B".into(), 2), ("C".into(), 10)]
    );
    assert_eq!(e.size, 4);
}

#[test]
fn an_enumerator_can_be_computed_from_the_ones_before_it() {
    let (t, d) =
        parse("enum flags { NONE = 0, READ = 1 << 0, WRITE = 1 << 1, BOTH = READ | WRITE };");
    let Some(Type::Enum(e)) = t.get(d.ty) else {
        panic!("an enumeration")
    };
    assert_eq!(e.values.last().unwrap().1, 3);
}

#[test]
fn qualifiers_land_on_the_half_of_the_type_they_qualify() {
    let (t, d) = parse("const char *p");
    assert_eq!(t.declare(d.ty, "p"), "const int8_t *p");
    let Some(Type::Pointer(inner)) = t.get(d.ty) else {
        panic!("a pointer to const")
    };
    assert!(t.qualifiers(*inner).is_const);

    let (t, d) = parse("char *const p");
    assert_eq!(t.declare(d.ty, "p"), "int8_t *const p");
    assert!(t.qualifiers(d.ty).is_const);
    // The pointee is not const, which is the whole difference.
    let Some(Type::Pointer(inner)) = t.get(t.resolve(d.ty)) else {
        panic!("a const pointer")
    };
    assert!(!t.qualifiers(*inner).is_const);
}

#[test]
fn volatile_survives_a_typedef() {
    let (t, d) = parse("volatile unsigned long counter");
    assert!(t.qualifiers(d.ty).is_volatile);
    assert_eq!(t.size_of(d.ty), Some(8));
}

#[test]
fn bitfields_share_a_storage_unit_until_it_is_full() {
    let (t, d) = parse("struct f { uint32_t a : 3; uint32_t b : 5; uint32_t c : 30; };");
    let Some(Type::Composite(c)) = t.get(d.ty) else {
        panic!("a structure")
    };
    assert_eq!(c.fields[0].offset, 0);
    assert_eq!(c.fields[1].offset, 0);
    // Thirty bits do not fit in the eight left, so `c` opens the next unit.
    assert_eq!(c.fields[2].offset, 4);
    assert_eq!(c.fields[2].bits, Some(30));
    assert_eq!(c.size, Some(8));
}

#[test]
fn an_unnamed_bitfield_is_padding_and_a_zero_width_one_closes_the_unit() {
    let (t, d) = parse("struct f { uint8_t a : 1; uint8_t : 0; uint8_t b : 1; };");
    let Some(Type::Composite(c)) = t.get(d.ty) else {
        panic!("a structure")
    };
    assert_eq!(c.fields.len(), 2, "a zero-width bitfield declares no field");
    assert_eq!(c.fields[1].offset, 1);
}

#[test]
fn an_anonymous_member_keeps_its_own_shape() {
    let (t, d) = parse("struct outer { int tag; struct { int x; int y; }; };");
    let Some(Type::Composite(c)) = t.get(d.ty) else {
        panic!("a structure")
    };
    assert_eq!(c.fields.len(), 2);
    assert!(c.fields[1].name.is_empty());
    assert_eq!(c.fields[1].offset, 4);
    assert_eq!(c.size, Some(12));
}

#[test]
fn a_forward_reference_is_completed_when_the_definition_arrives() {
    let mut t = Types::new();
    let unit = cdecl::translation_unit(
        &mut t,
        "struct opaque; struct holder { struct opaque *p; }; struct opaque { int v; };",
    )
    .expect("three declarations");
    assert_eq!(unit.len(), 3);
    let opaque = t.composite(false, "opaque").expect("the tag is registered");
    assert_eq!(t.size_of(opaque), Some(4));
}

#[test]
fn widths_follow_the_target_and_not_the_parser() {
    let mut lp64 = Types::for_model(Model::lp64());
    let a = cdecl::declaration(&mut lp64, "long x").unwrap();
    assert_eq!(lp64.size_of(a.ty), Some(8));

    let mut win = Types::for_model(Model::llp64());
    let b = cdecl::declaration(&mut win, "long x").unwrap();
    assert_eq!(win.size_of(b.ty), Some(4));

    let mut x86 = Types::for_model(Model::ilp32());
    let c = cdecl::declaration(&mut x86, "struct s { char c; double d; };").unwrap();
    // i386 aligns a double to four, so the structure is twelve bytes and not
    // sixteen. This is the whole reason the model is carried.
    assert_eq!(x86.size_of(c.ty), Some(12));
    let d = cdecl::declaration(&mut x86, "void *p").unwrap();
    assert_eq!(x86.size_of(d.ty), Some(4));
}

#[test]
fn the_fixed_width_names_are_the_widths_they_name() {
    for (text, size, signed) in [
        ("int8_t v", 1, true),
        ("uint16_t v", 2, false),
        ("int32_t v", 4, true),
        ("uint64_t v", 8, false),
        ("size_t v", 8, false),
        ("ptrdiff_t v", 8, true),
    ] {
        let (t, d) = parse(text);
        assert_eq!(
            t.get(d.ty),
            Some(&Type::Int { size, signed }),
            "{text} should be a {size}-byte integer"
        );
    }
}

#[test]
fn storage_classes_are_recorded_and_do_not_change_the_type() {
    let (_, d) = parse("extern int errno;");
    assert_eq!(d.storage, Some(Storage::Extern));
    assert!(!d.typedef);
    let (_, d) = parse("static void f(void);");
    assert_eq!(d.storage, Some(Storage::Static));
}

#[test]
fn an_empty_parameter_list_and_void_mean_the_same_thing() {
    let mut t = Types::new();
    let (_, a) = cdecl::prototype(&mut t, "void f(void)").unwrap();
    let (_, b) = cdecl::prototype(&mut t, "void g()").unwrap();
    assert!(a.parameters.is_empty());
    assert!(b.parameters.is_empty());
    assert_eq!(a.returns, None);
}

#[test]
fn varargs_are_read_and_printed() {
    let (t, d) = parse("int printf(const char *fmt, ...)");
    let Some(Type::Function(sig)) = t.get(d.ty) else {
        panic!("a function")
    };
    assert!(sig.varargs);
    assert_eq!(
        t.declare(d.ty, "printf"),
        "int32_t printf(const int8_t *fmt, ...)"
    );
}

#[test]
fn an_array_parameter_is_a_pointer_because_that_is_what_is_passed() {
    let (t, d) = parse("int main(int argc, char *argv[])");
    let Some(Type::Function(sig)) = t.get(d.ty) else {
        panic!("a function")
    };
    assert!(matches!(t.get(sig.parameters[1].1), Some(Type::Pointer(_))));
    assert_eq!(t.size_of(sig.parameters[1].1), Some(8));
}

#[test]
fn what_it_refuses_says_what_it_did_not_understand() {
    assert!(refused("struct s { widget w; };").contains("widget"));
    assert!(refused("frobnicate x").contains("frobnicate"));
    assert!(refused("int x[-1]").contains("negative"));
    assert!(refused("struct s { struct s inner; };").contains("size is not known"));
    assert!(refused("int f(void)[3]").contains("cannot return"));
    assert!(refused("struct s { int a; ").contains("never closed"));
    assert!(refused("long long long x").contains("not a type"));
    // An attribute that moves fields around is refused rather than ignored,
    // because ignoring it gives wrong offsets and the reader believes them.
    assert!(refused("struct s { char a; int b; } __attribute__((packed));").contains("layout"));
    assert!(refused("int n[x]").contains("no value here"));
    assert!(refused("int a; int b;").contains("more"));
}

#[test]
fn a_typedef_redefined_to_something_else_is_refused_rather_than_ignored() {
    let mut t = Types::new();
    cdecl::translation_unit(&mut t, "typedef long my_t;").unwrap();
    // The same definition again is ordinary in a header.
    cdecl::translation_unit(&mut t, "typedef long my_t;").unwrap();
    let e = cdecl::translation_unit(&mut t, "typedef short my_t;").unwrap_err();
    assert!(e.message.contains("my_t"), "{}", e.message);
}

#[test]
fn comments_and_preprocessor_lines_are_skipped() {
    let mut t = Types::new();
    let out = cdecl::translation_unit(
        &mut t,
        "#ifndef X\n#define X 1\n/* a comment */ int a; // trailing\nint b;\n#endif\n",
    )
    .expect("two declarations");
    assert_eq!(out.len(), 2);
}

#[test]
fn an_error_points_at_the_line_and_column_it_happened_on() {
    let mut t = Types::new();
    let e = cdecl::translation_unit(&mut t, "int a;\nint b;\nwidget c;\n").unwrap_err();
    assert_eq!(e.line, 3);
    assert_eq!(e.column, 1);
}
