//! x86-64 jump table recovery, checked against an external disassembly.
//!
//! The expectations below are transcribed from
//!
//!     llvm-objdump -d fixtures/build/dt-control.x64.O{1,2}
//!     od -A x -t x8 -j 0x1b8 -N 0x110 fixtures/build/dt-control.x64.O{1,2}
//!
//! which is the point: a test that only compared recovery against recovery
//! would have passed just as happily while every one of these switches went
//! unresolved. The table addresses, the entry counts and every target come
//! from outside this codebase.
//!
//! The shape is clang's non-PIE dense switch:
//!
//!     cmp  edi, 0xa
//!     ja   default
//!     mov  eax, edi
//!     jmp  qword ptr [8*rax + 0x2001b8]
//!
//! an absolute table of eight-byte targets addressed with no base register,
//! bounded by a compare that names `edi` where the branch names `rax`.

use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, TableKind, analyze};
use r12e_core::Addr;
use r12e_format::LoadOptions;

/// One switch, as an outside disassembler reports it.
struct Switch {
    fixture: &'static str,
    func: &'static str,
    /// The indirect branch, from the `jmpq` line of the listing.
    branch: u64,
    /// The table, from the branch's displacement.
    table: u64,
    /// Every entry, in table order, read out of `.rodata`.
    targets: &'static [u64],
}

const SWITCHES: &[Switch] = &[
    Switch {
        fixture: "dt-control.x64.O2",
        func: "switchind",
        branch: 0x20161c,
        table: 0x2001b8,
        targets: &[
            0x201623, 0x20168c, 0x20165b, 0x201676, 0x201631, 0x20169a, 0x2016a1, 0x201681,
            0x2016d1, 0x201646, 0x2016ca,
        ],
    },
    Switch {
        fixture: "dt-control.x64.O2",
        func: "switchloop",
        branch: 0x201700,
        table: 0x200210,
        targets: &[
            0x20171f, 0x201707, 0x201710, 0x201715, 0x2016ea, 0x201724, 0x20172b, 0x20171a,
            0x201737, 0x20170b, 0x201732, 0x201707,
        ],
    },
    Switch {
        fixture: "dt-control.x64.O2",
        func: "ifswitch",
        branch: 0x201771,
        table: 0x200270,
        targets: &[
            0x201797, 0x201778, 0x20179e, 0x20177f, 0x2017ac, 0x2017b6, 0x2017a5, 0x2017e3,
            0x201790, 0x2017d2, 0x201778,
        ],
    },
    Switch {
        fixture: "dt-control.x64.O1",
        func: "switchind",
        branch: 0x20163c,
        table: 0x2001b8,
        targets: &[
            0x201643, 0x2016ac, 0x20167b, 0x201696, 0x201651, 0x2016ba, 0x2016c1, 0x2016a1,
            0x2016f1, 0x201666, 0x2016ea,
        ],
    },
    Switch {
        fixture: "dt-control.x64.O1",
        func: "switchloop",
        branch: 0x201720,
        table: 0x200210,
        targets: &[
            0x20173f, 0x201727, 0x201730, 0x201735, 0x20170a, 0x201744, 0x20174b, 0x20173a,
            0x201757, 0x20172b, 0x201752, 0x201727,
        ],
    },
    Switch {
        fixture: "dt-control.x64.O1",
        func: "ifswitch",
        branch: 0x201793,
        table: 0x200270,
        targets: &[
            0x2017b2, 0x20179a, 0x2017b9, 0x2017a1, 0x2017cb, 0x2017d5, 0x2017be, 0x201802,
            0x2017ad, 0x2017f1, 0x20179a,
        ],
    },
];

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

#[test]
fn x86_64_switches_recover_the_table_objdump_shows() {
    let mut checked = 0;
    for s in SWITCHES {
        let Some(p) = open(s.fixture) else { continue };
        let f = p
            .functions_by_address()
            .find(|f| f.name.as_deref() == Some(s.func))
            .unwrap_or_else(|| panic!("{}/{}: no such function", s.fixture, s.func));

        let where_ = format!("{}/{}", s.fixture, s.func);
        assert_eq!(
            f.cfg.tables.len(),
            1,
            "{where_}: {} tables recovered, objdump shows one indirect branch",
            f.cfg.tables.len()
        );
        let t = &f.cfg.tables[0];
        assert_eq!(t.at, Addr(s.branch), "{where_}: wrong branch");
        assert_eq!(t.table, Addr(s.table), "{where_}: wrong table address");
        assert_eq!(t.entry_size, 8, "{where_}: wrong entry width");
        assert_eq!(
            t.kind,
            TableKind::Absolute,
            "{where_}: wrong entry encoding"
        );
        assert!(
            !t.bounded_by_scan,
            "{where_}: sized by scanning, so the count is a guess"
        );

        let got: Vec<u64> = t.targets.iter().map(|a| a.get()).collect();
        assert_eq!(
            got.len(),
            s.targets.len(),
            "{where_}: {} cases recovered, the table holds {}",
            got.len(),
            s.targets.len()
        );
        assert_eq!(got, s.targets, "{where_}: targets differ from the table");
        assert!(f.is_complete(), "{where_}: function still incomplete");
        checked += 1;
    }
    assert!(
        checked == SWITCHES.len() || checked == 0,
        "only {checked} of {} fixtures present",
        SWITCHES.len()
    );
}

#[test]
fn no_x86_64_switch_is_left_unresolved() {
    // Every indirect branch in these two builds is a switch, so an unresolved
    // one is a recovery failure rather than a genuinely unknowable target.
    for fixture in ["dt-control.x64.O1", "dt-control.x64.O2"] {
        let Some(p) = open(fixture) else { continue };
        for f in p.functions_by_address() {
            assert!(
                !f.cfg.has_indirect,
                "{fixture}/{}: an indirect branch nothing resolved",
                f.name.as_deref().unwrap_or("?")
            );
        }
    }
}
