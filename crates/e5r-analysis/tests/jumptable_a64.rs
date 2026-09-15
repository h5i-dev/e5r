//! AArch64 compact jump tables anchored on an `adr`, checked against an
//! external disassembly.
//!
//! The expectations below are transcribed from
//!
//!     aarch64-linux-gnu-objdump -d fixtures/build/em-paths.a64.O1
//!     aarch64-linux-gnu-objdump -d fixtures/build/em-paths.a64.O2
//!     aarch64-linux-gnu-objdump -d fixtures/build/hello.static.a64
//!     od -A x -t x1 -j 0x558 -N 0xb  fixtures/build/em-paths.a64.O1
//!     od -A x -t x1 -j 0x60c -N 0xb  fixtures/build/em-paths.a64.O2
//!     od -A x -t x2 -j 0x5af50 -N 24 fixtures/build/hello.static.a64
//!
//! and nothing here was read off our own recovery: the anchor, the entry
//! count and every target come from outside this codebase. That matters more
//! for this form than for most, because the gap it closes was invisible from
//! the inside. `pick` simply stopped at its `br` and reported an unresolved
//! indirect branch, which looks exactly like a switch nobody could have
//! resolved.
//!
//! The shape is what gcc emits for a small dense switch at `-O1` and `-Os`:
//!
//!     ldrb w1, [x1, w3, uxtw]     ; a one-byte entry
//!     adr  x3, <anchor>           ; not the table's own address
//!     add  x1, x3, w1, sxtb #2    ; sign extended and scaled by four
//!     br   x1
//!
//! Two things have to hold at once for it. The offset is signed and scaled
//! from an anchor that is neither the table nor the entry, and the compare
//! that bounds the switch names a register the value was moved out of, which
//! the `adr` then overwrites two instructions before the branch. The `ldrh`
//! case in `__gettextparse` is the same shape a halfword wide, which is what a
//! compiler emits once the span of the switch outgrows a byte.

use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, TableKind, analyze};
use e5r_core::{Addr, Arch};
use e5r_format::LoadOptions;

/// One switch, as an outside disassembler and `od` report it.
struct Switch {
    fixture: &'static str,
    func: &'static str,
    /// The `br` line of the listing.
    branch: u64,
    /// The `adrp`/`add` pair that addresses the entries.
    table: u64,
    /// Bytes per entry, from the load mnemonic.
    entry_size: u64,
    /// The `adr` line, which is where the offsets are measured from.
    anchor: u64,
    /// `#2` on the add's extend: entries count instructions, not bytes.
    shift: u8,
    /// Every entry, in table order, turned into an address by hand.
    targets: &'static [u64],
    /// True when the fixture statically links whatever libc built it.
    ///
    /// Then these addresses are a fact about that libc and not about the
    /// program, so on a machine whose libc differs they are not a weaker
    /// expectation -- they are a false one. The halfword form still has to be
    /// recovered and bounded there; only the transcribed addresses are held
    /// back, and the run says so rather than passing quietly.
    from_system_libc: bool,
}

const SWITCHES: &[Switch] = &[
    // cmp w2, #0xa ; ... ; mov x3, x2 ; adrp x1, 0x400000 ; add x1, x1, #0x558
    // ldrb w1, [x1, w3, uxtw] ; adr x3, 0x400390 ; add x1, x3, w1, sxtb #2
    // Table bytes: 00 03 05 07 09 0b 0d 0f 11 13 15.
    Switch {
        fixture: "em-paths.a64.O1",
        func: "pick",
        branch: 0x40038c,
        table: 0x400558,
        entry_size: 1,
        anchor: 0x400390,
        shift: 2,
        targets: &[
            0x400390, 0x40039c, 0x4003a4, 0x4003ac, 0x4003b4, 0x4003bc, 0x4003c4, 0x4003cc,
            0x4003d4, 0x4003dc, 0x4003e4,
        ],
        from_system_libc: false,
    },
    // The same source at -O2, where the compare names the index register
    // directly. It recovered before this form was modelled, so it is the
    // control: if it ever changes, the change is not about the anchor.
    // Table bytes: 02 03 04 05 06 07 08 09 0a 00 01.
    Switch {
        fixture: "em-paths.a64.O2",
        func: "pick",
        branch: 0x4003a4,
        table: 0x40060c,
        entry_size: 1,
        anchor: 0x4003a8,
        shift: 2,
        targets: &[
            0x4003b0, 0x4003b4, 0x4003b8, 0x4003bc, 0x4003c0, 0x4003c4, 0x4003c8, 0x4003cc,
            0x4003d0, 0x4003a8, 0x4003ac,
        ],
        from_system_libc: false,
    },
    // cmp w10, #0xb ; b.hi ; adrp x4, 0x45a000 ; add x4, x4, #0xf50
    // ldrh w4, [x4, w10, uxtw #1] ; adr x10, 0x433dbc ; add x4, x10, w4, sxth #2
    // Table halfwords: 0089 008e 00a4 00b8 0077 0028 0028 0028 00ce 010f 0119 00cc.
    Switch {
        fixture: "hello.static.a64",
        func: "__gettextparse",
        branch: 0x433db8,
        table: 0x45af50,
        entry_size: 2,
        anchor: 0x433dbc,
        shift: 2,
        targets: &[
            0x433fe0, 0x433ff4, 0x43404c, 0x43409c, 0x433f98, 0x433e5c, 0x433e5c, 0x433e5c,
            0x4340f4, 0x4341f8, 0x434220, 0x4340ec,
        ],
        from_system_libc: true,
    },
];

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<(Program, Vec<u8>)> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some((analyze(obj, &Options::default()), data))
}

/// The bytes a mapped address names, straight out of the file.
fn at(p: &Program, data: &[u8], addr: u64, len: usize) -> Option<Vec<u8>> {
    let sec = p.object.section_at(Addr(addr))?;
    let off = (sec.file_offset + (addr - sec.range.start().0)) as usize;
    (off + len <= data.len() && addr - sec.range.start().0 + len as u64 <= sec.file_size)
        .then(|| data[off..off + len].to_vec())
}

/// Every expectation here is transcribed from a listing of one build, so a
/// fixture compiled by a different toolchain is a different program sitting at
/// the same path -- and the assertions below would measure it and report a
/// recovery bug that is really a corpus that moved. That is not hypothetical:
/// `build-fixtures.sh` chose its compiler by host, so on an x86-64 machine
/// every `.a64` fixture was an x86-64 binary, and this test failed for a
/// reason its message did not mention.
///
/// So the file is checked against the transcription before anything is
/// concluded from it. The table entries are read out of the fixture and turned
/// into targets here, by the arithmetic the listing's `add` spells out, which
/// makes this an independent derivation of `targets` rather than a second
/// reading of the same recovery.
fn is_the_transcribed_build(p: &Program, data: &[u8], s: &Switch) -> Result<(), String> {
    if p.object.arch != Arch::AArch64 {
        return Err(format!(
            "{} is {}, not AArch64: build-fixtures.sh built the corpus with a \
             host compiler, so this file is not the program these expectations \
             describe",
            s.fixture, p.object.arch
        ));
    }
    let n = s.targets.len();
    let raw = at(p, data, s.table, n * s.entry_size as usize)
        .ok_or_else(|| format!("{}: nothing mapped at {:#x}", s.fixture, s.table))?;
    let derived: Vec<u64> = raw
        .chunks(s.entry_size as usize)
        .map(|e| {
            // Sign extended from the entry's own width, then scaled: the
            // listing's `sxtb #2` and `sxth #2`.
            let v = match e {
                [b] => *b as i8 as i64,
                [lo, hi] => i16::from_le_bytes([*lo, *hi]) as i64,
                _ => unreachable!("entry widths are one and two bytes"),
            };
            (s.anchor as i64 + (v << s.shift)) as u64
        })
        .collect();
    if derived != s.targets {
        return Err(format!(
            "{}: the table at {:#x} does not hold the entries this listing was \
             transcribed from -- the fixture is a different build, and these \
             expectations have to be re-transcribed from it\n  file: {:#x?}\n  \
             transcribed: {:#x?}",
            s.fixture, s.table, derived, s.targets
        ));
    }
    Ok(())
}

#[test]
fn an_anchored_compact_table_recovers_what_objdump_shows() {
    let mut checked = 0;
    let mut present = 0;
    // Cases whose fixture is a different build of a system library, where the
    // transcribed addresses are checked on the machine they came from.
    let mut elsewhere = 0;
    for s in SWITCHES {
        let Some((p, data)) = open(s.fixture) else {
            continue;
        };
        present += 1;
        let transcribed = match is_the_transcribed_build(&p, &data, s) {
            Ok(()) => true,
            // A different libc is a different program, so the addresses below
            // do not describe it. The shape still does, and is checked.
            Err(why) if s.from_system_libc => {
                println!("note: {why}");
                elsewhere += 1;
                false
            }
            Err(why) => panic!("{why}"),
        };
        let f = p
            .functions_by_address()
            .find(|f| f.name.as_deref() == Some(s.func))
            .unwrap_or_else(|| panic!("{}/{}: no such function", s.fixture, s.func));

        let where_ = format!("{}/{}", s.fixture, s.func);
        // By branch address rather than by position: a function can hold more
        // than one switch, and `__gettextparse` holds two. Where the addresses
        // belong to another libc, by entry width instead -- which is the thing
        // this case is here for, the halfword form a byte-wide table cannot
        // reach.
        let t = if transcribed {
            f.cfg.tables.iter().find(|t| t.at == Addr(s.branch))
        } else {
            f.cfg.tables.iter().find(|t| t.entry_size == s.entry_size)
        }
        .unwrap_or_else(|| {
            panic!(
                "{where_}: no table for the branch at {:#x}, {} recovered in this function",
                s.branch,
                f.cfg.tables.len()
            )
        });

        if transcribed {
            assert_eq!(t.table, Addr(s.table), "{where_}: wrong table address");
        }
        assert_eq!(t.entry_size, s.entry_size, "{where_}: wrong entry width");
        assert_eq!(
            t.kind,
            TableKind::RelativeToBase,
            "{where_}: wrong entry encoding"
        );
        if transcribed {
            assert_eq!(
                t.base,
                Addr(s.anchor),
                "{where_}: offsets measured from the wrong place"
            );
        }
        assert_eq!(t.shift, s.shift, "{where_}: wrong scale");
        assert!(
            !t.bounded_by_scan,
            "{where_}: sized by scanning, so the count is a guess"
        );

        let got: Vec<u64> = t.targets.iter().map(|a| a.get()).collect();
        if transcribed {
            assert_eq!(
                got.len(),
                s.targets.len(),
                "{where_}: {} cases recovered, the guard allows {}",
                got.len(),
                s.targets.len()
            );
            assert_eq!(got, s.targets, "{where_}: targets differ from the table");
        } else {
            // Every target inside the function that branched, which is what a
            // bounded table means and what a guess would break.
            assert!(!got.is_empty(), "{where_}: a table with no cases");
            for a in &got {
                assert!(
                    f.range.contains(Addr(*a)),
                    "{where_}: case {a:#x} is outside the function"
                );
            }
        }
        checked += 1;
    }
    assert!(
        checked == present,
        "only {checked} of {present} present fixtures recovered their table"
    );
    assert!(
        present - elsewhere >= 2,
        "{elsewhere} of {present} cases were system-library builds: the \
         transcribed addresses went unchecked here"
    );
}

#[test]
fn the_functions_holding_them_analyze_completely() {
    // The point of the exercise. A switch nobody reads leaves the function
    // with an unresolved indirect branch, and `pick` at -O1 was the one this
    // form cost us.
    for (fixture, func) in [
        ("em-paths.a64.O1", "pick"),
        ("em-paths.a64.O2", "pick"),
        ("hello.static.a64", "__gettextparse"),
    ] {
        let Some((p, _)) = open(fixture) else {
            continue;
        };
        assert_eq!(
            p.object.arch,
            Arch::AArch64,
            "{fixture} is {}, not AArch64: the corpus was built with a host compiler",
            p.object.arch
        );
        let f = p
            .functions_by_address()
            .find(|f| f.name.as_deref() == Some(func))
            .unwrap_or_else(|| panic!("{fixture}/{func}: no such function"));
        assert!(
            !f.cfg.has_indirect,
            "{fixture}/{func}: an indirect branch nothing resolved"
        );
        assert!(f.is_complete(), "{fixture}/{func}: still incomplete");
    }
}
