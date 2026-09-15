//! C++ class recovery, measured against a hierarchy known by construction.
//!
//! `fixtures/cpp/hierarchy.cpp` is the oracle: the expected hierarchy below is
//! written out from that source, not derived from what the tool found, so a
//! reader who disagrees with the test can settle it by reading the source. The
//! same program is built with type information and with `-fno-rtti`, at two
//! optimization levels on two architectures, which is what makes the
//! degradation a measurement rather than an assumption.
//!
//! Names are checked against `c++filt` where it is installed, because a
//! demangler measured against itself measures nothing.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_analysis::{Options, Program, analyze};
use e5r_api::classes::{Abi, Basis, Class, Role, Rtti, TypeInfoKind};
use e5r_core::Strength;
use e5r_format::LoadOptions;

/// The hierarchy `fixtures/cpp/hierarchy.cpp` declares: for each class, its
/// direct bases with the byte offset of the base subobject.
///
/// A virtual base has no such offset. What the ABI stores for one is the place
/// in the virtual table where the real offset is found at run time, because a
/// virtual base moves depending on the complete object, so the expectation for
/// one of those is that it comes back marked virtual and measured backwards
/// into the table. Everything else is the offset the compiler must lay out:
/// `Leftish` is a vtable pointer plus one word, so `Rightish` starts at 16.
/// One class and what it inherits: the base's name, the byte offset of the
/// base subobject, and whether the inheritance is virtual.
type Bases = &'static [(&'static str, i64, bool)];

const HIERARCHY: &[(&str, Bases)] = &[
    ("Base", &[]),
    ("Single", &[("Base", 0, false)]),
    ("Leftish", &[]),
    ("Rightish", &[]),
    ("Pair", &[("Leftish", 0, false), ("Rightish", 16, false)]),
    ("Root", &[]),
    ("ViaA", &[("Root", 0, true)]),
    ("ViaB", &[("Root", 0, true)]),
    ("Join", &[("ViaA", 0, false), ("ViaB", 16, false)]),
];

/// Which of the three type-information classes each one has to be, which
/// follows from the source: no bases, one public non-virtual base at zero, or
/// anything else.
const KINDS: &[(&str, TypeInfoKind)] = &[
    ("Base", TypeInfoKind::Class),
    ("Leftish", TypeInfoKind::Class),
    ("Rightish", TypeInfoKind::Class),
    ("Root", TypeInfoKind::Class),
    ("Single", TypeInfoKind::SingleInheritance),
    ("Pair", TypeInfoKind::MultipleInheritance),
    ("ViaA", TypeInfoKind::MultipleInheritance),
    ("ViaB", TypeInfoKind::MultipleInheritance),
    ("Join", TypeInfoKind::MultipleInheritance),
];

/// Every build of the fixture that carries type information.
const WITH_RTTI: &[&str] = &[
    "cpp-hierarchy.a64.O0.rtti",
    "cpp-hierarchy.a64.O2.rtti",
    "cpp-hierarchy.x64.O0.rtti",
    "cpp-hierarchy.x64.O2.rtti",
];

/// The same source in the Microsoft C++ ABI, linked as a PE, on both machines.
const MSVC: &[&str] = &[
    "cpp-hierarchy.win-x64.O0.rtti.exe",
    "cpp-hierarchy.win-x64.O2.rtti.exe",
    "cpp-hierarchy.win-a64.O0.rtti.exe",
    "cpp-hierarchy.win-a64.O2.rtti.exe",
];

/// The same program with `-fno-rtti`.
const WITHOUT_RTTI: &[&str] = &[
    "cpp-hierarchy.a64.O0.nortti",
    "cpp-hierarchy.a64.O2.nortti",
    "cpp-hierarchy.x64.O0.nortti",
    "cpp-hierarchy.x64.O2.nortti",
];

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let path = corpus()?.join(name);
    let data = std::fs::read(path).ok()?;
    let mut obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    // A shared library writes its tables at load time; these fixtures are
    // static and need none, but taking the same path as a real library means
    // the test exercises what a user's binary will.
    e5r_api::apply_relative_relocations(&mut obj);
    Some(analyze(obj, &Options::default()))
}

/// Recovering the fields through `this` lifts every member function, which is
/// the expensive half and not what most of these tests are about.
fn quick() -> e5r_api::classes::Options {
    e5r_api::classes::Options {
        stores: true,
        fields: false,
    }
}

/// The hierarchy, against the source, whichever ABI wrote it down.
///
/// `into_the_table` says whether a virtual base's stored number is an offset
/// backwards into the virtual table, which is what the Itanium ABI puts there.
/// The Microsoft ABI puts the displacement of the virtual base table instead,
/// and neither number is an offset the source declared, so neither is compared
/// against one.
fn check_hierarchy(fixture: &str, classes: &[Class], into_the_table: bool) {
    let by_name: BTreeMap<&str, &Class> = classes
        .iter()
        .filter_map(|c| c.name.as_deref().map(|n| (n, c)))
        .collect();

    for (class, bases) in HIERARCHY {
        let c = by_name
            .get(class)
            .unwrap_or_else(|| panic!("{fixture}: {class} was not recovered at all"));
        let got: Vec<(&str, i64, bool)> = c
            .bases
            .iter()
            .map(|b| (b.name.as_str(), b.offset, b.is_virtual))
            .collect();
        assert_eq!(
            got.len(),
            bases.len(),
            "{fixture}: {class} came back with bases {got:?}, the source declares {bases:?}"
        );
        for (got, want) in got.iter().zip(bases.iter()) {
            assert_eq!(got.0, want.0, "{fixture}: {class} base name");
            assert_eq!(got.2, want.2, "{fixture}: {class} base {} virtual", want.0);
            if want.2 {
                if into_the_table {
                    assert!(
                        got.1 < 0,
                        "{fixture}: {class} virtual base {} has table offset {}, \
                         which does not point into the table",
                        want.0,
                        got.1
                    );
                }
            } else {
                assert_eq!(
                    got.1, want.1,
                    "{fixture}: {class} base {} is at offset {}, the source puts it at {}",
                    want.0, got.1, want.1
                );
            }
        }
        for b in &c.bases {
            assert!(b.is_public, "{fixture}: {class} base {} is public", b.name);
            assert_eq!(
                b.basis.strength(),
                Strength::Proven,
                "{fixture}: {class} base {} came back as {}, and a base the type \
                 information states is not a guess",
                b.name,
                b.basis.as_str()
            );
        }
    }
}

#[test]
fn the_hierarchy_is_the_one_the_source_declares() {
    let mut ran = 0;
    for fixture in WITH_RTTI {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let found = e5r_api::classes_with(&p, &quick());
        assert_eq!(
            found.rtti,
            Rtti::Present,
            "{fixture}: built with type information but none was read"
        );
        assert_eq!(found.abi, Abi::Itanium, "{fixture}");
        check_hierarchy(fixture, &found.classes, true);
    }
    assert!(ran > 0, "no fixture with type information was built");
}

/// The same source through the Microsoft ABI, whose type information is a
/// different set of structures reached by relative addresses, and whose base
/// array lists every base in the lattice rather than the direct ones.
#[test]
fn the_microsoft_abi_gives_the_same_hierarchy() {
    let mut ran = 0;
    for fixture in MSVC {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let found = e5r_api::classes_with(&p, &quick());
        assert_eq!(found.rtti, Rtti::Present, "{fixture}");
        assert_eq!(found.abi, Abi::Msvc, "{fixture}");
        check_hierarchy(fixture, &found.classes, false);
        // Nothing in a linked PE with no symbols named any of this.
        assert_eq!(found.named_by_symbol, 0, "{fixture}");
        assert!(found.named_by_rtti > 0, "{fixture}");
        for c in &found.classes {
            assert_eq!(
                c.kind,
                None,
                "{fixture}: {} has an Itanium type-information kind",
                c.display_name()
            );
        }
    }
    assert!(ran > 0, "no Microsoft ABI fixture was built");
}

/// Without type information a PE gives nothing at all, and says so.
///
/// The Itanium scan finds a table by its offset-to-top and type-information
/// words; a Microsoft vftable has neither, so with the locators gone there is
/// nothing left that tells a table of function pointers from any other array
/// of them. That is the honest answer and it is worse than the Itanium one,
/// where the tables are still found and only the hierarchy is lost.
#[test]
fn a_microsoft_binary_without_rtti_gives_nothing() {
    for fixture in [
        "cpp-hierarchy.win-x64.O0.nortti.exe",
        "cpp-hierarchy.win-x64.O2.nortti.exe",
        "cpp-hierarchy.win-a64.O0.nortti.exe",
        "cpp-hierarchy.win-a64.O2.nortti.exe",
    ] {
        let Some(p) = open(fixture) else { continue };
        let found = e5r_api::classes_with(&p, &quick());
        assert_eq!(found.abi, Abi::Unknown, "{fixture}");
        assert!(found.classes.is_empty(), "{fixture}");
        assert_eq!(found.rtti, Rtti::NoClasses, "{fixture}");
    }
}

/// The Microsoft ABI's constructors, found the same way the Itanium ones are:
/// by the vftable pointer the function writes into its own object.
///
/// Six of the nine classes come back on the AArch64 PE. The three missing are
/// `ViaA`, `ViaB` and `Join`, the ones with a virtual base: the Microsoft ABI
/// puts their pointer at an offset the constructor loads out of a virtual base
/// table at run time, so the store is not at a constant place in the object
/// and nothing static says which class it belongs to. The x86-64 PE gives
/// fewer still, and that is not about the ABI: at `-O0` the compiler spills
/// `this` and reloads it across the base constructor call, and the stack
/// promotion in `e5r-ir` does not follow a reload past a call.
#[test]
fn the_microsoft_constructors_come_out_of_what_they_write() {
    let declared: BTreeSet<&str> = HIERARCHY.iter().map(|(name, _)| *name).collect();
    let mut ran = 0;
    for fixture in ["cpp-hierarchy.win-a64.O0.rtti.exe"] {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let found = e5r_api::classes_with(&p, &quick());
        let mut built: BTreeSet<&str> = BTreeSet::new();
        for c in &found.classes {
            for m in c.constructors() {
                assert_eq!(
                    m.basis,
                    Basis::VptrStore,
                    "{fixture}: {} at {} is a constructor because a name said so, and a \
                     linked PE with no symbols has no names",
                    m.class,
                    m.addr
                );
                assert_eq!(m.basis.strength(), Strength::Inferred, "{fixture}");
                let this = m.this.as_ref().expect("a member has a typed this");
                assert_eq!(this.declaration, format!("{} *this", m.class), "{fixture}");
                assert!(
                    declared.contains(m.class.as_str()),
                    "{fixture}: a constructor of {}, which the source does not declare",
                    m.class
                );
                built.insert(c.name.as_deref().unwrap_or_default());
            }
        }
        assert!(
            built.len() >= 6,
            "{fixture}: {} classes got a constructor out of the stores, six were \
             expected: {built:?}",
            built.len()
        );
    }
    assert!(ran > 0, "no Microsoft ABI fixture was built");
}

#[test]
fn each_class_has_the_type_information_kind_its_shape_requires() {
    for fixture in WITH_RTTI {
        let Some(p) = open(fixture) else { continue };
        let found = e5r_api::classes_with(&p, &quick());
        for (class, kind) in KINDS {
            let c = found
                .classes
                .iter()
                .find(|c| c.name.as_deref() == Some(*class))
                .unwrap_or_else(|| panic!("{fixture}: {class} was not recovered"));
            assert_eq!(
                c.kind,
                Some(*kind),
                "{fixture}: {class} came back as {:?}, the ABI requires {}",
                c.kind.map(TypeInfoKind::as_str),
                kind.as_str()
            );
        }
    }
}

/// The same hierarchy out of a binary with no symbols at all.
///
/// With the ABI's own `__class_type_info` symbols gone there is nothing to
/// compare a type-information object's first word against, so which of the
/// three kinds it is has to come out of the structure. That is a conclusion
/// and not a reading, and the strength says so.
#[test]
fn a_stripped_binary_still_gives_the_hierarchy_and_says_it_is_inferred() {
    let mut ran = 0;
    for fixture in [
        "cpp-hierarchy.a64.O0.rtti.stripped",
        "cpp-hierarchy.a64.O2.rtti.stripped",
    ] {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let found = e5r_api::classes_with(&p, &quick());
        assert_eq!(found.rtti, Rtti::Present, "{fixture}");
        assert_eq!(
            found.named_by_symbol, 0,
            "{fixture}: a stripped binary has no symbols to name a table"
        );
        for (class, bases) in HIERARCHY {
            let Some(c) = found
                .classes
                .iter()
                .find(|c| c.name.as_deref() == Some(*class))
            else {
                panic!("{fixture}: {class} was not recovered");
            };
            let got: Vec<(&str, bool)> = c
                .bases
                .iter()
                .map(|b| (b.name.as_str(), b.is_virtual))
                .collect();
            let want: Vec<(&str, bool)> = bases.iter().map(|b| (b.0, b.2)).collect();
            assert_eq!(got, want, "{fixture}: {class} bases");
            for b in &c.bases {
                assert_eq!(
                    b.basis,
                    Basis::RttiShape,
                    "{fixture}: {class} base {} claims to rest on {}, but nothing in a \
                     stripped binary states the kind",
                    b.name,
                    b.basis.as_str()
                );
                assert_eq!(b.basis.strength(), Strength::Inferred);
            }
        }
    }
    assert!(ran > 0, "no stripped fixture was built");
}

/// The degradation, measured rather than assumed.
#[test]
fn without_rtti_there_is_no_hierarchy_and_the_answer_says_so() {
    let mut ran = 0;
    for fixture in WITHOUT_RTTI {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let found = e5r_api::classes_with(&p, &quick());
        assert_eq!(
            found.rtti,
            Rtti::Absent,
            "{fixture}: built with -fno-rtti, so there is nothing to read"
        );
        assert!(
            found.tables > 0,
            "{fixture}: the tables are still there without type information"
        );
        for c in &found.classes {
            assert!(
                c.bases.is_empty(),
                "{fixture}: {} came back with bases {:?}, and nothing in this binary \
                 says what they are",
                c.display_name(),
                c.bases.iter().map(|b| &b.name).collect::<Vec<_>>()
            );
            assert_eq!(c.kind, None, "{fixture}: {}", c.display_name());
            assert!(c.typeinfo.is_none(), "{fixture}: {}", c.display_name());
        }
        // The names that survive are the ones the symbol table carries, and
        // they are proven for that reason and no other.
        for c in found.classes.iter().filter(|c| c.name.is_some()) {
            assert_eq!(c.basis, Basis::MangledName, "{fixture}: {:?}", c.name);
        }
    }
    assert!(ran > 0, "no fixture without type information was built");
}

/// What the two builds cost each other, stated as numbers so a regression in
/// either direction shows up.
#[test]
fn the_rtti_build_recovers_strictly_more_than_the_one_without() {
    for (with, without) in WITH_RTTI.iter().zip(WITHOUT_RTTI.iter()) {
        let (Some(a), Some(b)) = (open(with), open(without)) else {
            continue;
        };
        let rtti = e5r_api::classes_with(&a, &quick());
        let none = e5r_api::classes_with(&b, &quick());
        let bases: usize = rtti.classes.iter().map(|c| c.bases.len()).sum();
        // Base under Single, Leftish and Rightish under Pair, Root under
        // each of ViaA and ViaB, and ViaA and ViaB under Join.
        assert_eq!(
            bases, 7,
            "{with}: the source declares seven base relationships, {bases} came back"
        );
        assert_eq!(
            none.classes.iter().map(|c| c.bases.len()).sum::<usize>(),
            0,
            "{without}"
        );
        let named = |c: &e5r_api::Classes| c.classes.iter().filter(|x| x.name.is_some()).count();
        assert!(
            named(&rtti) >= named(&none),
            "{with}: type information named {} classes, without it {} were named",
            named(&rtti),
            named(&none)
        );
        assert!(
            rtti.named_by_rtti > 0,
            "{with}: no table got its name from type information, so nothing was gained"
        );
        assert_eq!(
            none.named_by_rtti, 0,
            "{without}: there is no type information to name anything"
        );
    }
}

/// Every class name, against `c++filt` on the fixture's own `_ZTI` symbols.
#[test]
fn the_class_names_are_the_ones_cxxfilt_gives() {
    let Some(dir) = corpus() else { return };
    for fixture in WITH_RTTI {
        let path = dir.join(fixture);
        if !path.exists() {
            continue;
        }
        let Some(symbols) = symbol_names(&path) else {
            return;
        };
        let mangled: Vec<String> = symbols
            .iter()
            .filter(|s| s.starts_with("_ZTI"))
            .cloned()
            .collect();
        if mangled.is_empty() {
            continue;
        }
        let Some(expected) = cxxfilt(&mangled) else {
            return;
        };
        let expected: BTreeSet<String> = expected
            .iter()
            .filter_map(|t| t.strip_prefix("typeinfo for ").map(str::to_string))
            // The ABI's own type-information classes are named here too; the
            // fixture defines their vtable symbols but not their type
            // information, so they are not classes of this program.
            .filter(|n| !n.starts_with("__cxxabiv1::"))
            .collect();

        let Some(p) = open(fixture) else { continue };
        let found: BTreeSet<String> = e5r_api::classes_with(&p, &quick())
            .classes
            .iter()
            .filter_map(|c| c.name.clone())
            .collect();
        for name in &expected {
            assert!(
                found.contains(name),
                "{fixture}: c++filt names a class {name:?} that did not come back; got {found:?}"
            );
        }
    }
}

/// Constructors and destructors, by name and by what they write.
///
/// The names are the oracle for the shapes: what a stripped binary infers has
/// to be a subset of what the symbols prove, at the same addresses and with
/// the same roles. A shape that finds something the names do not is a false
/// positive, and this is where it would show.
#[test]
fn what_the_shapes_find_is_what_the_names_prove() {
    let mut ran = 0;
    for (named, stripped, least) in [
        (
            "cpp-hierarchy.a64.O0.rtti",
            "cpp-hierarchy.a64.O0.rtti.stripped",
            8,
        ),
        // At -O2 the compiler inlines every constructor in this program into
        // its one caller and drops the vtable-pointer store from every
        // destructor, because nothing reads it back. There is then nothing of
        // the shape to find, and the number that matters is that nothing
        // wrong is claimed either.
        (
            "cpp-hierarchy.a64.O2.rtti",
            "cpp-hierarchy.a64.O2.rtti.stripped",
            0,
        ),
    ] {
        let (Some(a), Some(b)) = (open(named), open(stripped)) else {
            continue;
        };
        ran += 1;
        let proven = e5r_api::classes_with(&a, &quick());
        let inferred = e5r_api::classes_with(&b, &quick());

        // What the symbols say, by address.
        let mut truth: BTreeMap<u64, (String, Role)> = BTreeMap::new();
        for c in &proven.classes {
            for m in &c.members {
                // A member with a C++ symbol is proven by it. The exception is
                // `__cxa_pure_virtual`, which sits in tables without being a
                // member of anything, and which a slot is all there is for.
                if m.name.as_deref().is_some_and(|n| n.contains("::")) {
                    assert_eq!(
                        m.basis,
                        Basis::MangledName,
                        "{named}: {:?} at {} rests on {}, but its symbol is right there",
                        m.name,
                        m.addr,
                        m.basis.as_str()
                    );
                }
                truth.insert(m.addr.get(), (m.class.clone(), m.role));
            }
        }
        if least > 0 {
            assert!(
                truth.values().any(|(_, r)| *r == Role::Constructor),
                "{named}: no constructor came out of the symbol table"
            );
        }

        let mut checked = 0;
        for c in &inferred.classes {
            for m in c.members.iter().filter(|m| {
                matches!(
                    m.role,
                    Role::Constructor | Role::Destructor | Role::DeletingDestructor
                )
            }) {
                assert_eq!(
                    m.basis.strength(),
                    Strength::Inferred,
                    "{stripped}: {} at {} claims to be {}, and nothing in a stripped \
                     binary proves that",
                    m.class,
                    m.addr,
                    m.basis.as_str()
                );
                let (class, role) = truth.get(&m.addr.get()).unwrap_or_else(|| {
                    panic!(
                        "{stripped}: called {} at {} a {}, and the symbols of {named} \
                         say nothing is there",
                        m.class,
                        m.addr,
                        m.role.as_str()
                    )
                });
                assert_eq!(
                    (&m.class, m.role),
                    (class, *role),
                    "{stripped}: {} at {} is a {} of {}, the symbols say a {} of {}",
                    m.class,
                    m.addr,
                    m.role.as_str(),
                    m.class,
                    role.as_str(),
                    class
                );
                checked += 1;
            }
        }
        assert!(
            checked >= least,
            "{stripped}: only {checked} constructors and destructors were inferred, \
             and {least} were expected"
        );
    }
    assert!(ran > 0, "neither half of the pair was built");
}

/// Every class with a virtual destructor spends its first two table slots on
/// it, complete then deleting. That is the ABI, and it is what has to come
/// back.
#[test]
fn the_two_destructor_slots_come_back_as_the_two_destructors() {
    // At -O0 only: at -O2 the vtable-pointer store a destructor makes is dead
    // and the compiler drops it, so nothing identifies slot zero and the rule
    // that keys off it never fires. That is measured in the subset gate above.
    for fixture in ["cpp-hierarchy.a64.O0.rtti.stripped"] {
        let Some(p) = open(fixture) else { continue };
        let found = e5r_api::classes_with(&p, &quick());
        let mut pairs = 0;
        for c in &found.classes {
            let complete = c.members.iter().find(|m| m.slot == Some(0));
            let deleting = c.members.iter().find(|m| m.slot == Some(1));
            let (Some(complete), Some(deleting)) = (complete, deleting) else {
                continue;
            };
            if complete.role != Role::Destructor {
                continue;
            }
            assert_eq!(
                deleting.role,
                Role::DeletingDestructor,
                "{fixture}: {} has a destructor in slot 0 and {} in slot 1",
                c.display_name(),
                deleting.role.as_str()
            );
            pairs += 1;
        }
        assert!(pairs >= 5, "{fixture}: only {pairs} destructor pairs found");
    }
}

/// `this` typing: every member function of a class takes a pointer to it, and
/// what the code touches through that pointer is the class's fields.
///
/// The counts differ by architecture and that is not about the typing. On
/// AArch64 the `this` that a -O0 prologue spills and reloads is promoted back
/// to the incoming argument; on x86-64 that promotion does not survive a
/// function that calls, so a constructor that builds its bases first comes
/// back with no fields at all. The class and the declaration are right either
/// way, and the number here is what says when that gap closes.
#[test]
fn every_member_takes_a_this_of_its_own_class() {
    let mut ran = 0;
    for (fixture, least) in [
        ("cpp-hierarchy.a64.O0.rtti", 9),
        ("cpp-hierarchy.x64.O0.rtti", 4),
    ] {
        let Some(p) = open(fixture) else { continue };
        ran += 1;
        let found = e5r_api::classes(&p);
        let mut described = 0;
        for c in &found.classes {
            for m in &c.members {
                let this = m
                    .this
                    .as_ref()
                    .unwrap_or_else(|| panic!("{fixture}: {:?} has no typed this", m.name));
                assert_eq!(this.class, m.class, "{fixture}: {:?}", m.name);
                assert_eq!(
                    this.declaration,
                    format!("{} *this", c.name.clone().unwrap_or_default()),
                    "{fixture}: {:?}",
                    m.name
                );
                // A typed `this` is never stronger than whatever named the
                // class it points at.
                assert!(this.basis.strength() >= Strength::Inferred);
            }
            // Every class here has virtual functions, so offset zero of one of
            // its objects is the vtable pointer, and a constructor of it
            // writes exactly that. A constructor whose fields did not come
            // back at all says nothing either way.
            for ctor in c.constructors() {
                let fields = &ctor.this.as_ref().unwrap().fields;
                if fields.is_empty() {
                    continue;
                }
                assert!(
                    fields.iter().any(|f| f.offset == 0 && f.written),
                    "{fixture}: {} touched {fields:?} through its own object and wrote \
                     nothing at offset zero, where its vtable pointer goes",
                    ctor.name.clone().unwrap_or_default()
                );
                described += 1;
            }
        }
        assert!(
            described >= least,
            "{fixture}: {described} constructors came back with fields, {least} were expected"
        );
    }
    assert!(ran > 0, "no fixture was built");
}

/// The fields a class's own code touches, against what the source declares.
///
/// `Single` is a vtable pointer, `Base::id` and `Single::extra`, so its
/// members reach offsets 0, 8 and 16 and nothing past them.
#[test]
fn the_fields_are_inside_the_object_the_source_declares() {
    for fixture in ["cpp-hierarchy.a64.O0.rtti", "cpp-hierarchy.x64.O0.rtti"] {
        let Some(p) = open(fixture) else { continue };
        let found = e5r_api::classes(&p);
        let c = found
            .classes
            .iter()
            .find(|c| c.name.as_deref() == Some("Single"))
            .unwrap();
        for f in &c.fields {
            assert!(
                (0..=16).contains(&f.offset),
                "{fixture}: Single has a field at {}, and the source declares three words",
                f.offset
            );
            assert_eq!(f.basis, Basis::Accesses);
        }
        assert_eq!(
            c.size(),
            Some(24),
            "{fixture}: Single is a vtable pointer, an id and an extra"
        );
    }
}

/// Over a real library, what the shapes infer has to agree with what the
/// symbols prove, on the class as well as on the role.
///
/// `libstdc++` is where this is worth measuring: 283 tables, 337 classes and
/// enough virtual inheritance and enough polymorphic members to break a rule
/// that only looks at whether a vtable pointer was written. Eighteen functions
/// used to come back a constructor of the class of a member they set the
/// pointer of, `~basic_ofstream` as a `basic_filebuf` among them, which is the
/// wrong class and the wrong role at once. Requiring the store to land at the
/// offset the table itself says its subobject begins at is what rules those
/// out, and this is the gate that keeps them out.
///
/// The symbols are cleared after the analysis rather than before, so function
/// discovery still had them. That makes this a test of the class rules with no
/// names, not a simulation of a stripped file end to end.
#[test]
fn nothing_inferred_from_a_real_library_contradicts_its_symbols() {
    let path = Path::new("/usr/lib/aarch64-linux-gnu/libstdc++.so.6");
    let Ok(data) = std::fs::read(path) else {
        return;
    };
    let Ok(mut obj) = e5r_format::load(&data, &LoadOptions::default()) else {
        return;
    };
    // Every virtual table in a shared library is zeroes in the file until the
    // loader fills it in, so without this there is nothing to read at all.
    assert!(e5r_api::apply_relative_relocations(&mut obj) > 0);
    let p = analyze(obj, &Options::default());

    let named = e5r_api::classes_with(&p, &quick());
    assert_eq!(named.rtti, Rtti::Present);
    assert!(named.classes.len() > 200, "{}", named.classes.len());
    let truth: BTreeMap<u64, (String, Role)> = named
        .classes
        .iter()
        .flat_map(|c| c.members.iter())
        .map(|m| (m.addr.get(), (m.class.clone(), m.role)))
        .collect();

    let mut bare = analyze(
        e5r_format::load(&data, &LoadOptions::default()).unwrap(),
        &Options::default(),
    );
    assert!(e5r_api::apply_relative_relocations(&mut bare.object) > 0);
    bare.object.symbols.clear();
    let stripped = e5r_api::classes_with(&bare, &quick());
    assert_eq!(stripped.named_by_symbol, 0);

    let mut checked = 0;
    for m in stripped.classes.iter().flat_map(|c| c.members.iter()) {
        if !matches!(
            m.role,
            Role::Constructor | Role::Destructor | Role::DeletingDestructor
        ) {
            continue;
        }
        assert_eq!(m.basis.strength(), Strength::Inferred, "{}", m.addr);
        let Some((class, role)) = truth.get(&m.addr.get()) else {
            panic!(
                "called {} at {} a {}, and the symbols say nothing is there",
                m.class,
                m.addr,
                m.role.as_str()
            );
        };
        assert_eq!(
            (&m.class, m.role),
            (class, *role),
            "{} at {} is a {} of {}, the symbols say a {} of {}",
            m.class,
            m.addr,
            m.role.as_str(),
            m.class,
            role.as_str(),
            class
        );
        checked += 1;
    }
    assert!(
        checked >= 200,
        "only {checked} constructors and destructors were inferred out of a library \
         whose symbols prove hundreds"
    );
}

/// A C program has no classes, and nothing here invents any.
#[test]
fn a_c_program_has_no_classes() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let found = e5r_api::classes(&p);
    assert_eq!(found.rtti, Rtti::NoClasses);
    assert!(
        found.classes.is_empty(),
        "found {:?} in a C program",
        found
            .classes
            .iter()
            .map(|c| c.display_name())
            .collect::<Vec<_>>()
    );
}

/// Symbol names out of `readelf`, which is the file's own account of itself.
fn symbol_names(path: &Path) -> Option<Vec<String>> {
    let out = Command::new("readelf").arg("-sW").arg(path).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(
        String::from_utf8_lossy(&out.stdout)
            .lines()
            .filter_map(|l| l.split_whitespace().nth(7))
            .map(|s| s.split('@').next().unwrap_or(s).to_string())
            .collect(),
    )
}

/// `c++filt`, one name per line, in order.
fn cxxfilt(names: &[String]) -> Option<Vec<String>> {
    let out = Command::new("c++filt").args(names).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(
        String::from_utf8_lossy(&out.stdout)
            .lines()
            .map(str::to_string)
            .collect(),
    )
}
