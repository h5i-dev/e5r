//! Swift reflection metadata, against hand-built images.
//!
//! There is no Swift toolchain on this machine, so there is no compiler output
//! to compare against and no `swift demangle` to check a name with. What these
//! tests measure is a fixture written from the published ABI: the section
//! names Swift's IRGen emits, the field descriptor record layout, the context
//! descriptor layout, and the conformance record, with every relative pointer
//! computed by hand from the address of the field that holds it. That is a
//! weaker claim than the Go and DWARF gates, which are measured against other
//! implementations, and the scorecard should say so.
//!
//! What the fixture does check that a compiler could not check better: a
//! displacement measured from the wrong place lands somewhere deliberately
//! nearby, so each expected value here is one an off-by-a-field reader gets
//! wrong. The section walk landing exactly on the section's end is the second
//! check, and it is the one that catches a record size read wrong.

use std::time::{Duration, Instant};

use r12e_core::Addr;
use r12e_format::swift::{ContextKind, FieldDescriptorKind, TypeReference};
use r12e_format::{LoadOptions, load, metadata, swift};

const MACHO_BASE: u64 = 0x1_0000_0000;

// __TEXT. Every Swift reflection section lives here on Mach-O.
const TEXT_CODE: u64 = 0x400;
const CONST: u64 = 0x500;
const MODULE: u64 = 0x500;
const POINT: u64 = 0x520;
const COLOR: u64 = 0x540;
const CONFORMANCE: u64 = 0x560;
const PROTOCOL: u64 = 0x580;
const WITNESS: u64 = 0x5a0;
const TYPEREF: u64 = 0x700;
const SYMBOLIC: u64 = 0x730;
const REFLSTR: u64 = 0x780;
const FIELDMD: u64 = 0x800;
const FIELDMD_SIZE: u64 = 0x50;
const TYPES: u64 = 0x900;
const PROTO: u64 = 0x910;
const PROTOS: u64 = 0x920;
// __DATA: one slot, so the indirect form of a relative pointer has somewhere
// to indirect through the way a linker's GOT does.
const GOT: u64 = 0x1000;

fn at(offset: u64) -> Addr {
    Addr(MACHO_BASE + offset)
}

/// A Mach-O image carrying Swift reflection metadata.
///
/// Written out resolved, for the same reason the Objective-C fixture is: a
/// relocatable object has zero where each of these pointers belongs.
fn synth_swift() -> Vec<u8> {
    let mut f = vec![0u8; 0x2000];
    let put = |f: &mut Vec<u8>, at: u64, b: &[u8]| {
        f[at as usize..at as usize + b.len()].copy_from_slice(b);
    };
    let u16at = |f: &mut Vec<u8>, at: u64, v: u16| put(f, at, &v.to_le_bytes());
    let u32at = |f: &mut Vec<u8>, at: u64, v: u32| put(f, at, &v.to_le_bytes());
    let u64at = |f: &mut Vec<u8>, at: u64, v: u64| put(f, at, &v.to_le_bytes());
    // A relative pointer: the displacement from the field's own address, which
    // is the whole thing this format gets wrong when it is got wrong.
    let rel = |f: &mut Vec<u8>, field: u64, target: u64| {
        u32at(f, field, (target as i64 - field as i64) as i32 as u32);
    };
    let name16 = |s: &str| {
        let mut b = [0u8; 16];
        b[..s.len()].copy_from_slice(s.as_bytes());
        b
    };

    let text_sections: [(&str, u64, u64, u32); 8] = [
        ("__text", TEXT_CODE, 0x100, 0x8000_0400),
        ("__const", CONST, 0x200, 0),
        ("__swift5_typeref", TYPEREF, 0x80, 2),
        ("__swift5_reflstr", REFLSTR, 0x80, 2),
        ("__swift5_fieldmd", FIELDMD, FIELDMD_SIZE, 0),
        ("__swift5_types", TYPES, 8, 0),
        ("__swift5_proto", PROTO, 4, 0),
        ("__swift5_protos", PROTOS, 4, 0),
    ];
    let data_sections: [(&str, u64, u64, u32); 1] = [("__got", GOT, 0x40, 6)];

    // mach_header_64: 64-bit little-endian arm64 executable.
    u32at(&mut f, 0, 0xfeed_facf);
    u32at(&mut f, 4, 0x0100_000c);
    u32at(&mut f, 12, 2);
    u32at(&mut f, 16, 2);
    let text_cmd = 72 + 80 * text_sections.len() as u32;
    let data_cmd = 72 + 80 * data_sections.len() as u32;
    u32at(&mut f, 20, text_cmd + data_cmd);

    let seg = |f: &mut Vec<u8>,
               cmd: u64,
               name: &str,
               vmaddr: u64,
               fileoff: u64,
               prot: u32,
               sects: &[(&str, u64, u64, u32)]| {
        u32at(f, cmd, 0x19);
        u32at(f, cmd + 4, 72 + 80 * sects.len() as u32);
        put(f, cmd + 8, &name16(name));
        u64at(f, cmd + 24, vmaddr);
        u64at(f, cmd + 32, 0x1000);
        u64at(f, cmd + 40, fileoff);
        u64at(f, cmd + 48, 0x1000);
        u32at(f, cmd + 56, 7);
        u32at(f, cmd + 60, prot);
        u32at(f, cmd + 64, sects.len() as u32);
        for (i, (sn, offset, size, flags)) in sects.iter().enumerate() {
            let s = cmd + 72 + 80 * i as u64;
            put(f, s, &name16(sn));
            put(f, s + 16, &name16(name));
            u64at(f, s + 32, MACHO_BASE + offset);
            u64at(f, s + 40, *size);
            // __TEXT starts at file offset zero and __DATA at 0x1000, which is
            // where each section's own address puts it.
            u32at(f, s + 48, *offset as u32);
            u32at(f, s + 64, *flags);
        }
    };
    seg(&mut f, 32, "__TEXT", MACHO_BASE, 0, 5, &text_sections);
    seg(
        &mut f,
        32 + text_cmd as u64,
        "__DATA",
        MACHO_BASE + GOT,
        GOT,
        3,
        &data_sections,
    );

    // Reflection strings: field and type names.
    put(
        &mut f,
        REFLSTR,
        b"x\0y\0red\0green\0Point\0Color\0Demo\0Drawable\0",
    );
    let x = REFLSTR;
    let y = REFLSTR + 2;
    let red = REFLSTR + 4;
    let green = REFLSTR + 8;
    let point = REFLSTR + 14;
    let color = REFLSTR + 20;
    let module = REFLSTR + 26;
    let drawable = REFLSTR + 31;

    // Mangled type names. The third is symbolic: a control byte, then a
    // four-byte displacement whose bytes include three zeros, which is what
    // breaks a reader that stops the name at the first zero byte.
    put(&mut f, TYPEREF, b"$s4Demo5PointV\0");
    put(&mut f, TYPEREF + 16, b"Si\0");
    put(&mut f, TYPEREF + 20, b"$s4Demo5ColorO\0");
    f[SYMBOLIC as usize] = 0x01;
    u32at(&mut f, SYMBOLIC + 1, 0x20);
    put(&mut f, SYMBOLIC + 5, b"Sg\0");
    let point_mangled = TYPEREF;
    let int_mangled = TYPEREF + 16;
    let color_mangled = TYPEREF + 20;

    // The module descriptor every other context hangs off.
    u32at(&mut f, MODULE, 0);
    u32at(&mut f, MODULE + 4, 0);
    rel(&mut f, MODULE + 8, module);

    // struct Point, with a field descriptor and a metadata accessor.
    u32at(&mut f, POINT, 17 | 0x40);
    rel(&mut f, POINT + 4, MODULE);
    rel(&mut f, POINT + 8, point);
    rel(&mut f, POINT + 12, TEXT_CODE);
    rel(&mut f, POINT + 16, FIELDMD);
    u32at(&mut f, POINT + 20, 2);
    u32at(&mut f, POINT + 24, 2);

    // enum Color.
    u32at(&mut f, COLOR, 18 | 0x40);
    rel(&mut f, COLOR + 4, MODULE);
    rel(&mut f, COLOR + 8, color);
    rel(&mut f, COLOR + 12, TEXT_CODE + 0x20);
    rel(&mut f, COLOR + 16, FIELDMD + 0x28);

    // Point: Drawable. The protocol is reached by the indirect form, which is
    // what an import looks like once the linker has made a slot for it.
    u32at(
        &mut f,
        CONFORMANCE,
        ((GOT as i64 - CONFORMANCE as i64) as i32 | 1) as u32,
    );
    rel(&mut f, CONFORMANCE + 4, POINT);
    rel(&mut f, CONFORMANCE + 8, WITNESS);
    u32at(&mut f, CONFORMANCE + 12, 0);
    u64at(&mut f, GOT, MACHO_BASE + PROTOCOL);

    // protocol Drawable, with two requirements.
    u32at(&mut f, PROTOCOL, 3 | 0x40);
    rel(&mut f, PROTOCOL + 4, MODULE);
    rel(&mut f, PROTOCOL + 8, drawable);
    u32at(&mut f, PROTOCOL + 12, 0);
    u32at(&mut f, PROTOCOL + 16, 2);

    // The field descriptors, packed one after another with no count in front.
    rel(&mut f, FIELDMD, point_mangled);
    u16at(&mut f, FIELDMD + 8, 0); // struct
    u16at(&mut f, FIELDMD + 10, 12);
    u32at(&mut f, FIELDMD + 12, 2);
    u32at(&mut f, FIELDMD + 16, 2); // var
    rel(&mut f, FIELDMD + 20, int_mangled);
    rel(&mut f, FIELDMD + 24, x);
    u32at(&mut f, FIELDMD + 28, 0); // let
    rel(&mut f, FIELDMD + 32, int_mangled);
    rel(&mut f, FIELDMD + 36, y);

    let second = FIELDMD + 40;
    rel(&mut f, second, color_mangled);
    u16at(&mut f, second + 8, 2); // enum
    u16at(&mut f, second + 10, 12);
    u32at(&mut f, second + 12, 2);
    u32at(&mut f, second + 16, 0);
    // A case with no payload has no type name, which is a null relative
    // pointer and not a pointer to an empty string.
    u32at(&mut f, second + 20, 0);
    rel(&mut f, second + 24, red);
    u32at(&mut f, second + 28, 1); // indirect case
    rel(&mut f, second + 32, SYMBOLIC);
    rel(&mut f, second + 36, green);

    // The three lists of relative pointers. The second type record is the
    // indirect form: the low bits of a type record carry the reference kind,
    // and one means the displacement reaches a slot holding the descriptor.
    rel(&mut f, TYPES, POINT);
    u64at(&mut f, GOT + 8, MACHO_BASE + COLOR);
    u32at(
        &mut f,
        TYPES + 4,
        ((GOT as i64 + 8 - (TYPES as i64 + 4)) as i32 | 1) as u32,
    );
    rel(&mut f, PROTO, CONFORMANCE);
    rel(&mut f, PROTOS, PROTOCOL);
    f
}

fn read(bytes: &[u8]) -> swift::SwiftMetadata {
    let obj = load(bytes, &LoadOptions::default()).expect("the synthesized image does not load");
    swift::read(&obj)
}

#[test]
fn nominal_types_are_read_with_their_module() {
    let found = read(&synth_swift());
    assert_eq!(found.types.len(), 2, "{:#?}", found.types);

    let point = &found.types[0];
    assert_eq!(point.name, "Point");
    assert_eq!(point.qualified_name, "Demo.Point");
    assert_eq!(point.kind, ContextKind::Struct);
    assert_eq!(point.addr, at(POINT));
    // The accessor is a function, and the only address here that is one.
    assert_eq!(point.accessor, Some(at(TEXT_CODE)));
    assert_eq!(point.field_descriptor, Some(at(FIELDMD)));

    // Reached through a slot, which is what a record with its kind bit set
    // means and what a reader that ignores the bit gets wrong.
    let color = &found.types[1];
    assert_eq!(color.addr, at(COLOR));
    assert_eq!(color.qualified_name, "Demo.Color");
    assert_eq!(color.kind, ContextKind::Enum);
    assert_eq!(color.accessor, Some(at(TEXT_CODE + 0x20)));

    assert!(
        found.warnings.is_empty(),
        "a fixture built to the ABI should produce no complaints: {:#?}",
        found.warnings
    );
}

#[test]
fn field_descriptors_name_every_field_with_its_type() {
    let found = read(&synth_swift());
    assert_eq!(found.field_descriptors.len(), 2);

    let point = &found.field_descriptors[0];
    assert_eq!(point.addr, at(FIELDMD));
    assert_eq!(point.kind, FieldDescriptorKind::Struct);
    assert_eq!(
        point.mangled_type_name.as_ref().map(|m| m.text.as_str()),
        Some("$s4Demo5PointV")
    );
    assert!(point.superclass.is_none());
    let names: Vec<&str> = point.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["x", "y"]);
    assert!(point.fields[0].mutable, "x is a var");
    assert!(!point.fields[1].mutable, "y is a let");
    for field in &point.fields {
        assert_eq!(
            field.mangled_type.as_ref().map(|m| m.text.as_str()),
            Some("Si")
        );
    }

    let color = &found.field_descriptors[1];
    assert_eq!(color.kind, FieldDescriptorKind::Enum);
    let names: Vec<&str> = color.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["red", "green"]);
    // A case with no payload has no type, and inventing one would be worse
    // than saying so.
    assert!(color.fields[0].mangled_type.is_none());
    assert!(color.fields[1].indirect_case);
}

#[test]
fn a_symbolic_reference_is_followed_and_does_not_end_the_name() {
    // The displacement in this reference is 0x20, whose upper three bytes are
    // zero. A reader that treats a mangled name as a C string stops there and
    // loses both the reference and the rest of the name.
    let found = read(&synth_swift());
    let green = &found.field_descriptors[1].fields[1];
    let mangled = green
        .mangled_type
        .as_ref()
        .expect("the indirect case has a payload type");
    assert!(mangled.symbolic, "the reference was not noticed");
    assert_eq!(mangled.references, vec![at(SYMBOLIC + 1 + 0x20)]);
    assert_eq!(
        mangled.text, "Sg",
        "the characters after the reference were lost"
    );
}

#[test]
fn a_conformance_names_both_sides() {
    let found = read(&synth_swift());
    assert_eq!(found.conformances.len(), 1);
    let c = &found.conformances[0];
    assert_eq!(c.addr, at(CONFORMANCE));
    assert_eq!(c.type_reference, TypeReference::DirectDescriptor);
    assert_eq!(c.type_descriptor, Some(at(POINT)));
    assert_eq!(c.type_name.as_deref(), Some("Point"));
    // Reached through the slot, which is the whole point of the low bit.
    assert_eq!(c.protocol_descriptor, Some(at(PROTOCOL)));
    assert_eq!(c.protocol_name.as_deref(), Some("Drawable"));
    assert_eq!(c.witness_table, Some(at(WITNESS)));
    assert!(!c.retroactive);
    assert_eq!(c.conditional_requirements, 0);

    assert_eq!(found.protocols.len(), 1);
    assert_eq!(found.protocols[0].qualified_name, "Demo.Drawable");
    assert_eq!(found.protocols[0].requirements, 2);
}

#[test]
fn the_accessors_become_hints_and_nothing_else_does() {
    let bytes = synth_swift();
    let obj = load(&bytes, &LoadOptions::default()).unwrap();
    let found = metadata::read(&obj);
    let mut names: Vec<String> = found
        .hints
        .iter()
        .filter(|h| h.provenance.best == r12e_core::Evidence::SwiftMetadata)
        .map(|h| format!("{:#x} {}", h.addr.get(), h.name.clone().unwrap_or_default()))
        .collect();
    names.sort();
    let mut want = vec![
        format!(
            "{:#x} type metadata accessor for Demo.Point",
            at(TEXT_CODE).get()
        ),
        format!(
            "{:#x} type metadata accessor for Demo.Color",
            at(TEXT_CODE + 0x20).get()
        ),
    ];
    want.sort();
    assert_eq!(
        names, want,
        "the witness table or a descriptor was reported as a function"
    );
    assert_eq!(
        found.notes.get("swift.types").map(String::as_str),
        Some("2")
    );
    assert_eq!(
        found.notes.get("swift.fields").map(String::as_str),
        Some("4")
    );
    assert_eq!(
        found.notes.get("swift.conformances").map(String::as_str),
        Some("1")
    );
}

#[test]
fn an_accessor_outside_executable_memory_is_a_warning_and_not_a_hint() {
    let mut bytes = synth_swift();
    // Point the accessor at the string section instead, which is mapped but
    // is not code.
    let field = POINT + 12;
    let displacement = (REFLSTR as i64 - field as i64) as i32 as u32;
    bytes[field as usize..field as usize + 4].copy_from_slice(&displacement.to_le_bytes());
    let found = read(&bytes);
    assert!(found.types[0].accessor.is_none());
    assert!(
        found.warnings.iter().any(|w| w.contains("executable")),
        "{:#?}",
        found.warnings
    );
}

#[test]
fn a_type_record_pointing_out_of_the_image_is_refused() {
    let mut bytes = synth_swift();
    bytes[TYPES as usize..TYPES as usize + 4].copy_from_slice(&0x4000_0000u32.to_le_bytes());
    let found = read(&bytes);
    assert_eq!(found.types.len(), 1, "the unmapped descriptor was believed");
    assert!(
        found
            .warnings
            .iter()
            .any(|w| w.contains("outside the image"))
    );
}

#[test]
fn a_field_count_larger_than_the_section_allocates_nothing() {
    let mut bytes = synth_swift();
    bytes[(FIELDMD + 12) as usize..(FIELDMD + 12) as usize + 4]
        .copy_from_slice(&u32::MAX.to_le_bytes());
    let started = Instant::now();
    let found = read(&bytes);
    assert!(
        started.elapsed() < Duration::from_secs(2),
        "a lying field count took too long"
    );
    // Room for three more records is all there is behind the header.
    assert!(found.field_descriptors[0].fields.len() <= 3);
    assert!(found.warnings.iter().any(|w| w.contains("room for")));
}

#[test]
fn a_parent_chain_that_points_at_itself_terminates() {
    let mut bytes = synth_swift();
    // The module's parent is itself, and the type's parent is the module.
    let field = MODULE + 4;
    let displacement = (MODULE as i64 - field as i64) as i32 as u32;
    bytes[field as usize..field as usize + 4].copy_from_slice(&displacement.to_le_bytes());
    let started = Instant::now();
    let found = read(&bytes);
    assert!(started.elapsed() < Duration::from_secs(2));
    // Eight hops and then it stops, rather than running forever.
    assert!(found.types[0].qualified_name.ends_with("Point"));
}

#[test]
fn a_record_size_the_walk_cannot_advance_on_is_refused() {
    let mut bytes = synth_swift();
    bytes[(FIELDMD + 10) as usize..(FIELDMD + 10) as usize + 2]
        .copy_from_slice(&0u16.to_le_bytes());
    let found = read(&bytes);
    assert!(found.field_descriptors.is_empty());
    assert!(
        found
            .warnings
            .iter()
            .any(|w| w.contains("byte records") || w.contains("could not be read"))
    );
}

#[test]
fn every_truncation_of_the_image_is_survivable() {
    let full = synth_swift();
    let started = Instant::now();
    for cut in (0x20..full.len()).step_by(16) {
        if let Ok(obj) = load(&full[..cut], &LoadOptions::default()) {
            let found = metadata::read(&obj);
            // The contract is a value, not a guess: whatever survives has to
            // be internally consistent.
            if let Some(s) = found.swift {
                for d in &s.field_descriptors {
                    assert!(d.fields.len() < 0x1000);
                }
            }
        }
    }
    assert!(
        started.elapsed() < Duration::from_secs(20),
        "truncation sweep took {:?}",
        started.elapsed()
    );
}

#[test]
fn targeted_corruption_of_every_descriptor_byte_never_panics() {
    let full = synth_swift();
    let started = Instant::now();
    // Only the regions the reader walks, one byte at a time, set to the two
    // values that break arithmetic: all ones and zero.
    for region in [CONST, TYPEREF, FIELDMD, TYPES, PROTO, PROTOS, GOT] {
        for i in region..region + 0x60 {
            for value in [0xffu8, 0x00] {
                let mut bad = full.clone();
                bad[i as usize] = value;
                if let Ok(obj) = load(&bad, &LoadOptions::default()) {
                    let _ = metadata::read(&obj);
                }
            }
        }
    }
    assert!(
        started.elapsed() < Duration::from_secs(30),
        "corruption sweep took {:?}",
        started.elapsed()
    );
}

#[test]
fn an_image_with_no_swift_sections_says_so() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    let Ok(bytes) = std::fs::read(dir.join("greeter.macho.a64.o")) else {
        return;
    };
    let Ok(obj) = load(&bytes, &LoadOptions::default()) else {
        return;
    };
    let found = swift::read(&obj);
    assert!(found.is_empty());
    assert!(found.warnings.is_empty());
}

#[test]
fn the_elf_section_names_are_read_too() {
    // Swift on ELF spells the same sections without a segment prefix, and two
    // of them under different names. Only the matching differs, so renaming
    // the sections of a loaded image tests exactly the part that is different
    // without pretending to be an ELF Swift binary.
    let bytes = synth_swift();
    let mut obj = load(&bytes, &LoadOptions::default()).unwrap();
    for s in &mut obj.sections {
        s.name = match s.name.rsplit(',').next().unwrap_or_default() {
            "__swift5_types" => "swift5_type_metadata".into(),
            "__swift5_fieldmd" => "swift5_fieldmd".into(),
            "__swift5_proto" => "swift5_protocol_conformances".into(),
            "__swift5_protos" => "swift5_protocols".into(),
            "__swift5_typeref" => "swift5_typeref".into(),
            "__swift5_reflstr" => "swift5_reflstr".into(),
            other => other.into(),
        };
    }
    let found = swift::read(&obj);
    assert_eq!(found.types.len(), 2);
    assert_eq!(found.field_descriptors.len(), 2);
    assert_eq!(found.conformances.len(), 1);
    assert_eq!(found.protocols.len(), 1);
    assert!(found.warnings.is_empty(), "{:#?}", found.warnings);
}
