//! The code partition stops at what is provably data.
//!
//! Built by hand rather than taken from a fixture, because the failure this
//! guards against needs a coincidence and no binary in the corpus supplies
//! one: a word inside a literal pool whose bit pattern happens to be a
//! function prologue. The gap scan reads such a word as the start of a
//! function and invents one out of data. Here the coincidence is arranged on
//! purpose, so the guard is measured rather than assumed.
//!
//! The image is four instructions of real function, four `nop`s nobody
//! reaches, and then eight bytes the function loads as a literal. The first
//! four of those are `stp x29, x30, [sp, #-16]!` — a pool entry whose value
//! is a prologue encoding, which is a thing a compiler emits every day: it is
//! just the number 0xa9bf7bfd.

use std::collections::BTreeMap;

use e5r_analysis::{Options, Proof, analyze};
use e5r_core::{
    Addr, AddrRange, Arch, Bits, Endian, Evidence, MemoryMap, Perms, Provenance, Segment,
};
use e5r_format::{Format, FunctionHint, Object, Section};

const BASE: u64 = 0x40_0000;

/// The literal the function reads, and which the gap scan must not walk.
const POOL: u64 = BASE + 0x20;

fn image() -> Vec<u8> {
    let words: [u32; 10] = [
        // 0x00 stp x29, x30, [sp, #-16]!   the real function's prologue
        0xa9bf_7bfd,
        // 0x04 ldr x0, #0x1c               reads eight bytes at 0x20
        0x5800_00e0,
        // 0x08 ldp x29, x30, [sp], #16
        0xa8c1_7bfd,
        // 0x0c ret
        0xd65f_03c0,
        // 0x10..0x1c nop, so the gap before the pool holds nothing
        0xd503_201f,
        0xd503_201f,
        0xd503_201f,
        0xd503_201f,
        // 0x20 the literal's first word, which is also a prologue encoding
        0xa9bf_7bfd,
        // 0x24 and a ret behind it, so a walk that starts here succeeds
        0xd65f_03c0,
    ];
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn object() -> Object {
    let bytes = image();
    let range = AddrRange::sized(Addr(BASE), bytes.len() as u64).unwrap();
    let mut memory = MemoryMap::new();
    memory.add(Segment::new(range, Perms::RX, ".text", 0, bytes.clone()).unwrap());
    Object {
        format: Format::Elf,
        arch: Arch::AArch64,
        endian: Endian::Little,
        bits: Bits::Bits64,
        entry: Some(Addr(BASE)),
        image_base: Addr(BASE),
        pic: false,
        memory,
        sections: vec![Section {
            name: ".text".into(),
            range,
            file_offset: 0,
            file_size: bytes.len() as u64,
            exec: true,
            write: false,
            kind: 1,
        }],
        symbols: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        function_hints: vec![FunctionHint {
            addr: Addr(BASE),
            size: None,
            name: Some("only".into()),
            provenance: Provenance::new(Evidence::SymbolTable),
        }],
        metadata: BTreeMap::new(),
        debug: None,
        warnings: Vec::new(),
    }
}

#[test]
fn a_literal_pool_is_marked_with_the_instruction_that_reads_it() {
    let p = analyze(object(), &Options::default());
    let r = p
        .data()
        .proof_at(Addr(POOL))
        .expect("the pool the function loads is data");
    assert_eq!(r.range.start(), Addr(POOL));
    assert_eq!(r.range.len(), 8, "an `ldr x0` reads eight bytes");
    assert_eq!(
        r.proof,
        Proof::LiteralPool {
            read_by: Addr(BASE + 4)
        },
        "the proof names the instruction that reads it"
    );
    assert_eq!(
        p.data().refused(),
        0,
        "nothing here contradicts a walked block"
    );
}

#[test]
fn the_gap_scan_does_not_invent_a_function_inside_it() {
    let with = analyze(object(), &Options::default());
    let without = analyze(
        object(),
        &Options {
            data: false,
            ..Options::default()
        },
    );

    // The point of the fixture: without the marking the scan does take the
    // bait, so the test is not passing by there being nothing to find.
    assert!(
        without.functions.contains_key(&Addr(POOL)),
        "the pool word is a prologue encoding, so an unguarded scan walks it"
    );
    assert!(
        !with.functions.contains_key(&Addr(POOL)),
        "a function was invented out of a literal pool"
    );
    assert_eq!(with.functions.len(), 1, "only the function that exists");
    assert_eq!(with.functions.keys().next(), Some(&Addr(BASE)));
}

#[test]
fn the_bytes_marked_are_reported_against_the_section() {
    let p = analyze(object(), &Options::default());
    let text = p.object.section(".text").unwrap().range;
    assert_eq!(p.data().bytes(), 8);
    assert_eq!(p.data().bytes_in(text), 8);
    // And the run is one step for a scan, not two words.
    assert_eq!(p.data().end_of_run(Addr(POOL)), Some(Addr(POOL + 8)));
}
