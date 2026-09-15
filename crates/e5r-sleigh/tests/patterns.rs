//! What the front end hands a decode engine, checked against real encodings.
//!
//! Parsing without failing is not the same as parsing correctly: a mask with
//! the bits in the wrong byte parses beautifully and decodes nothing. These
//! tests take instruction words whose encoding is fixed by the published
//! architecture manuals and assert that the constructor the specification
//! means is the one whose reduced pattern matches them.

use e5r_sleigh::model::{DisplayPiece, Endian, Offset, OperandSource, Symbol};
use std::path::{Path, PathBuf};

fn ghidra_root() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("E5R_GHIDRA") {
        let p = PathBuf::from(p);
        return p.is_dir().then_some(p);
    }
    for guess in [
        "../ghidra",
        "../../ghidra",
        concat!(env!("HOME"), "/Ref/ghidra"),
        "/opt/ghidra",
    ] {
        let p = PathBuf::from(guess);
        if p.join("Ghidra/Processors").is_dir() {
            return Some(p);
        }
    }
    None
}

fn toy() -> e5r_sleigh::Spec {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/toy.slaspec");
    e5r_sleigh::parse_file(&path).expect("the toy specification parses")
}

#[test]
fn a_field_constraint_lands_in_the_right_byte() {
    let spec = toy();
    let root = spec.table(spec.root());
    let and = spec.constructor(root.constructors[0]);
    assert_eq!(and.display.mnemonic.as_deref(), Some("and"));
    assert_eq!(and.resolved.alternatives.len(), 1);
    let alt = &and.resolved.alternatives[0];
    // `op` is bits 10 to 15 of a big endian sixteen bit token, so it is the
    // top six bits of the first byte. `op=0x10` is 0b010000 there.
    assert_eq!(alt.instr.mask, vec![0xfc]);
    assert_eq!(alt.instr.value, vec![0x40]);
    assert_eq!(alt.length, 2, "one sixteen bit token");
    assert!(alt.residual.is_empty());
    assert!(!and.resolved.is_approximate());

    assert!(alt.instr.matches(&[0x40, 0x00]));
    assert!(alt.instr.matches(&[0x43, 0xff]));
    assert!(!alt.instr.matches(&[0x44, 0x00]), "op=0x11 is xor, not and");
}

#[test]
fn operands_carry_their_source_and_their_offset() {
    let spec = toy();
    let and = spec.constructor(spec.table(spec.root()).constructors[0]);
    let names: Vec<&str> = and.operands.iter().map(|o| o.name.as_str()).collect();
    assert_eq!(names, ["reg1", "op2"]);
    assert!(matches!(and.operands[0].source, OperandSource::Field(_)));
    assert!(matches!(and.operands[1].source, OperandSource::Table(_)));
    // A single token, so everything reads from the first byte.
    assert_eq!(and.operands[0].offset, Offset::absolute(0));
    assert_eq!(and.operands[1].offset, Offset::absolute(0));
    assert!(!and.operands[0].invisible);
    assert_eq!(
        and.display.pieces,
        vec![
            DisplayPiece::Literal(" ".into()),
            DisplayPiece::Operand(0),
            DisplayPiece::Literal(",".into()),
            DisplayPiece::Operand(1),
        ]
    );
}

#[test]
fn an_attachment_turns_a_field_into_registers() {
    let spec = toy();
    let Some(Symbol::Field(reg1)) = spec.lookup("reg1") else {
        panic!("reg1 should be a field");
    };
    let attach = &spec.field(reg1).attach;
    assert_eq!(attach.len(), 8);
    let e5r_sleigh::model::Attach::Variables(regs) = attach else {
        panic!("reg1 should have registers attached");
    };
    let third = regs[2].expect("r2 is attached at index two");
    assert_eq!(spec.varnode(third).name, "r2");
    assert_eq!(spec.varnode(third).offset, 8);
}

/// A fixed width architecture is the clean case: every root constructor's
/// pattern covers the whole instruction, so a mask test alone decides it.
///
/// The AArch64 specification also shows why the model has to carry context
/// separately. Its root table holds one constructor that matches everything,
/// computes six context flags in its disassembly action, sets
/// `ImmS_ImmR_TestSet`, and recurses into `instruction`; every real
/// instruction sits inside a `with : ImmS_ImmR_TestSet=1` block. So with a
/// cleared context register exactly one constructor matches anything at all,
/// and the encodings below only appear on the second pass.
#[test]
fn aarch64_matches_the_encodings_the_manual_fixes() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set E5R_GHIDRA to run this");
        return;
    };
    let path = root.join("Ghidra/Processors/AARCH64/data/languages/AARCH64.slaspec");
    if !path.is_file() {
        return;
    }
    let spec = e5r_sleigh::parse_file(&path).expect("AARCH64 parses");
    assert_eq!(spec.endian, Endian::Little);
    assert_eq!(spec.alignment, 4);
    assert_eq!(spec.context_bytes(), 4);

    let matches = |bytes: &[u8], context: &[u8]| -> Vec<Option<String>> {
        spec.table(spec.root())
            .constructors
            .iter()
            .map(|id| spec.constructor(*id))
            .filter(|c| c.resolved.may_match(bytes, context))
            .map(|c| c.display.mnemonic.clone())
            .collect()
    };

    let ret = 0xd65f_03c0u32.to_le_bytes();
    let cleared = [0u8; 4];
    let first_pass = matches(&ret, &cleared);
    assert_eq!(
        first_pass,
        vec![None],
        "with a cleared context only the recursive constructor should match"
    );

    // `ImmS_ImmR_TestSet` is context bit zero, which is the most significant
    // bit of the register's first byte.
    let set = [0x80u8, 0, 0, 0];
    let cases = [
        (0xd65f_03c0u32, "ret"),
        (0xd503_201f, "nop"),
        (0x9100_0000, "add"),
        (0xd400_0001, "svc"),
        (0x0000_0000, "udf"),
    ];
    for (word, mnemonic) in cases {
        let bytes = word.to_le_bytes();
        let hits = matches(&bytes, &set);
        assert!(
            hits.iter().any(|m| m.as_deref() == Some(mnemonic)),
            "{word:#010x} should be {mnemonic}, the masks offered {hits:?}"
        );
        // Discrimination, not just coverage: none of the other encodings'
        // mnemonics may be offered for this word.
        for (_, other) in cases {
            if other == mnemonic {
                continue;
            }
            assert!(
                !hits.iter().any(|m| m.as_deref() == Some(other)),
                "{word:#010x} is {mnemonic} but the masks also offered {other}"
            );
        }
    }
}

/// A variable width architecture puts the second token at the offset the first
/// one ends at, which is what `;` in a pattern means.
#[test]
fn a_second_token_lands_after_the_first() {
    let spec = e5r_sleigh::parse_str(
        r#"
        define endian=little;
        define space ram type=ram_space size=4 default;
        define space register type=register_space size=4;
        define register offset=0 size=1 [ a b c d ];
        define token base(8) op=(0,3) mode=(4,4) reg=(5,7);
        define token immtoken(16) imm16=(0,15);
        attach variables [ reg ] [ a b c d ];
        :inc reg       is op=2 & reg        { reg = reg + 1; }
        :add reg,imm16 is op=3 & reg; imm16 { reg = reg + imm16:1; }
        "#,
    )
    .expect("parses");

    let root = spec.table(spec.root());
    let inc = spec.constructor(root.constructors[0]);
    assert_eq!(inc.resolved.alternatives[0].length, 1);

    let add = spec.constructor(root.constructors[1]);
    let alt = &add.resolved.alternatives[0];
    assert_eq!(alt.length, 3, "one byte of base then two of immtoken");
    assert_eq!(alt.instr.mask, vec![0x0f]);
    assert_eq!(alt.instr.value, vec![0x03]);
    let imm = add
        .operands
        .iter()
        .find(|o| o.name == "imm16")
        .expect("imm16 is an operand");
    assert_eq!(
        imm.offset,
        Offset::absolute(1),
        "the immediate follows the opcode byte"
    );
    let reg = add
        .operands
        .iter()
        .find(|o| o.name == "reg")
        .expect("reg is an operand");
    assert_eq!(reg.offset, Offset::absolute(0));
}

/// `|` in a pattern is a disjunction, and the reduction has to keep both sides
/// rather than intersecting them into something that matches too much.
#[test]
fn a_disjunction_keeps_both_alternatives() {
    let spec = e5r_sleigh::parse_str(
        r#"
        define endian=big;
        define space ram type=ram_space size=4 default;
        define token instr(8) opcode=(0,7) mode=(0,3);
        :nop is (opcode=0 & mode=0) | (opcode=15) { }
        "#,
    )
    .expect("parses");
    let nop = spec.constructor(spec.table(spec.root()).constructors[0]);
    assert_eq!(nop.resolved.alternatives.len(), 2);
    assert!(!nop.resolved.is_approximate());
    assert!(nop.resolved.may_match(&[0x00], &[]));
    assert!(nop.resolved.may_match(&[0x0f], &[]));
    assert!(!nop.resolved.may_match(&[0x07], &[]));
}

/// A constraint that is not `field = constant` cannot be a mask test, and has
/// to come back as something the decoder evaluates itself.
#[test]
fn an_unreducible_constraint_survives_as_a_residual() {
    let spec = e5r_sleigh::parse_str(
        r#"
        define endian=big;
        define space ram type=ram_space size=4 default;
        define space register type=register_space size=4;
        define register offset=0 size=1 [ g0 g1 g2 g3 ];
        define token instr(16) opcode=(8,15) ra=(4,7) rb=(0,3);
        attach variables [ ra rb ] [ g0 g1 g2 g3 ];
        :xor ra,rb is opcode=0xcd & ra & rb { ra = ra ^ rb; }
        :clr ra    is opcode=0xcd & ra & ra=rb { ra = 0; }
        "#,
    )
    .expect("parses");
    let clr = spec.constructor(spec.table(spec.root()).constructors[1]);
    let alt = &clr.resolved.alternatives[0];
    assert_eq!(alt.instr.mask, vec![0xff]);
    assert_eq!(alt.residual.len(), 1, "ra = rb is not a bit test");
    // The mask alone still admits every register pair, which is exactly why
    // the residual has to be evaluated.
    assert!(alt.instr.matches(&[0xcd, 0x12]));
}

/// Context is a separate image from the instruction stream, and a constraint
/// on it must not land in the instruction mask.
#[test]
fn context_constraints_go_to_the_context_mask() {
    let spec = e5r_sleigh::parse_str(
        r#"
        define endian=big;
        define space ram type=ram_space size=4 default;
        define space register type=register_space size=4;
        define register offset=0x200 size=4 [ statusreg ];
        define token instr(16) op=(10,15) imm=(0,6);
        define context statusreg mode=(3,3);
        :addi imm is op=1 & mode=1 & imm { }
        "#,
    )
    .expect("parses");
    let addi = spec.constructor(spec.table(spec.root()).constructors[0]);
    let alt = &addi.resolved.alternatives[0];
    assert_eq!(alt.instr.mask, vec![0xfc]);
    // Context bit three counts from the register's most significant end, so it
    // is bit four of the first byte.
    assert_eq!(alt.context.mask, vec![0x10]);
    assert_eq!(alt.context.value, vec![0x10]);
    assert!(addi.resolved.may_match(&[0x04, 0x00], &[0x10, 0, 0, 0]));
    assert!(!addi.resolved.may_match(&[0x04, 0x00], &[0x00, 0, 0, 0]));
}

/// The same thing on a big endian architecture, because a byte order mistake
/// in the field-to-byte mapping is invisible on a little endian one.
///
/// The expected mnemonics are the constructors that actually match, not the
/// names a disassembler prints: `nop` and `mflr` are specialisations of `ori`
/// and `mfspr` that live in other tables, and `li` and `addi` both match, with
/// `li` the contained case that a decoder is required to prefer.
#[test]
fn powerpc_matches_big_endian_encodings() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set E5R_GHIDRA to run this");
        return;
    };
    let path = root.join("Ghidra/Processors/PowerPC/data/languages/ppc_32_be.slaspec");
    if !path.is_file() {
        return;
    }
    let spec = e5r_sleigh::parse_file(&path).expect("ppc_32_be parses");
    assert_eq!(spec.endian, Endian::Big);
    let context = vec![0u8; spec.context_bytes()];

    for (word, wanted, refused) in [
        (0x4e80_0020u32, "blr", "ori"),
        (0x6000_0000, "ori", "blr"),
        (0x7c08_02a6, "mfspr", "ori"),
        (0x3800_0001, "li", "mfspr"),
        (0x3800_0001, "addi", "blr"),
    ] {
        let bytes = word.to_be_bytes();
        let hits: Vec<&str> = spec
            .table(spec.root())
            .constructors
            .iter()
            .map(|id| spec.constructor(*id))
            .filter(|c| c.resolved.may_match(&bytes, &context))
            .filter_map(|c| c.display.mnemonic.as_deref())
            .collect();
        assert!(
            hits.contains(&wanted),
            "{word:#010x} should match {wanted}, the masks offered {hits:?}"
        );
        assert!(
            !hits.contains(&refused),
            "{word:#010x} is not {refused}, but the masks offered it"
        );
    }
}

/// Table widths, which are what let a `;` place the token after a subtable.
#[test]
fn table_widths_settle_even_when_tables_recurse() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set E5R_GHIDRA to run this");
        return;
    };
    let fixed = root.join("Ghidra/Processors/AARCH64/data/languages/AARCH64.slaspec");
    if fixed.is_file() {
        // A64 is fixed width, and its root table recurses into itself, which
        // is the case a fixpoint from below has to survive.
        let spec = e5r_sleigh::parse_file(&fixed).expect("AARCH64 parses");
        let table = spec.table(spec.root());
        assert_eq!(table.min_length, 4);
        assert_eq!(table.max_length, 4);
        assert!(table.is_fixed_length());
        assert_eq!(spec.approximate_constructors().count(), 0);
    }

    let varied = root.join("Ghidra/Processors/x86/data/languages/x86-64.slaspec");
    if varied.is_file() {
        let spec = e5r_sleigh::parse_file(&varied).expect("x86-64 parses");
        let table = spec.table(spec.root());
        assert!(
            !table.is_fixed_length(),
            "x86 instructions are not all one length"
        );
        assert!(table.min_length >= 1);
    }
}

/// The same thing without needing a Ghidra tree: a subtable of fixed width
/// places what follows it, and one of varying width does not.
#[test]
fn a_fixed_width_subtable_places_what_follows_it() {
    let source = r#"
        define endian=little;
        define space ram type=ram_space size=4 default;
        define space register type=register_space size=4;
        define register offset=0 size=1 [ a b c d ];
        define token op(8) code=(0,3) sel=(4,7);
        define token arg(8) v=(0,7);
        define token tail(8) t=(0,7);
        REG: a is sel=0 { export a; }
        REG: b is sel=1 { export b; }
        WIDE: v is sel=2; v { export *[const]:1 v; }
        WIDE: a is sel=3 { export a; }
        :one REG,t is code=1 & REG; t { }
        :two WIDE,t is code=2 & WIDE; t { }
    "#;
    let spec = e5r_sleigh::parse_str(source).expect("parses");

    let reg = match spec.lookup("REG") {
        Some(e5r_sleigh::model::Symbol::Table(id)) => id,
        other => panic!("REG should be a table, found {other:?}"),
    };
    let wide = match spec.lookup("WIDE") {
        Some(e5r_sleigh::model::Symbol::Table(id)) => id,
        other => panic!("WIDE should be a table, found {other:?}"),
    };
    assert!(spec.table(reg).is_fixed_length());
    assert_eq!(spec.table(reg).min_length, 1);
    assert!(!spec.table(wide).is_fixed_length());
    assert_eq!(spec.table(wide).min_length, 1);
    assert_eq!(spec.table(wide).max_length, 2);

    let one = spec.constructor(spec.table(spec.root()).constructors[0]);
    assert!(!one.resolved.is_approximate());
    assert_eq!(one.resolved.alternatives[0].length, 2, "one byte each");
    let t = one.operands.iter().find(|o| o.name == "t").expect("t");
    assert_eq!(t.offset, Offset::absolute(1));

    let two = spec.constructor(spec.table(spec.root()).constructors[1]);
    assert_eq!(
        two.resolved.approximation,
        Some(e5r_sleigh::model::Approximation::UnknownTokenOffset),
        "WIDE is one or two bytes, so where t sits depends on which matched"
    );
    // What the decoder gets instead of a number: t begins where WIDE ends.
    let wide_operand = two
        .operands
        .iter()
        .position(|o| o.name == "WIDE")
        .expect("WIDE is an operand") as u16;
    let t = two.operands.iter().find(|o| o.name == "t").expect("t");
    assert_eq!(
        t.offset,
        Offset {
            base: Some(wide_operand),
            delta: 0
        }
    );
    assert_eq!(
        t.offset.resolve(|i| (i == wide_operand).then_some(3)),
        Some(3),
        "resolving against a WIDE that matched two bytes at offset one"
    );

    // And the mask must not pretend to know where t sits. Byte one is WIDE's
    // first byte, so a mask that constrained it would reject `two` with a
    // two-byte WIDE, which is an encoding the constructor does match.
    for alt in &two.resolved.alternatives {
        assert!(
            alt.instr.mask.len() <= 1,
            "the mask reached past the opcode byte: {:x?}",
            alt.instr.mask
        );
    }
}

/// A field written after a variable width subtable is the x86 case, and the
/// offsets the model gives for it are what a decoder steps by.
#[test]
fn x86_places_an_immediate_after_the_modrm_it_follows() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set E5R_GHIDRA to run this");
        return;
    };
    let path = root.join("Ghidra/Processors/x86/data/languages/x86-64.slaspec");
    if !path.is_file() {
        return;
    }
    let spec = e5r_sleigh::parse_file(&path).expect("x86-64 parses");

    // `:CMP rm8, imm8 is vexMode=0 & byte=0x80; rm8 ... & imm8`: the immediate
    // follows a ModR/M that is one to six bytes long.
    let cmp = spec
        .constructors
        .iter()
        .find(|c| {
            c.display.mnemonic.as_deref() == Some("CMP")
                && c.operands.len() == 2
                && c.operands[0].name == "rm8"
                && c.operands[1].name == "imm8"
        })
        .expect("CMP rm8,imm8 is in the specification");
    assert_eq!(
        cmp.operands[0].offset,
        Offset::absolute(1),
        "the ModR/M follows the one opcode byte"
    );
    assert_eq!(
        cmp.operands[1].offset,
        Offset {
            base: Some(0),
            delta: 0
        },
        "and the immediate follows the ModR/M, wherever it ends"
    );

    // Display order is not pattern order: `CMP^XmmCondPD^"PD" XmmReg,m128`
    // prints XmmCondPD first and matches it last, after the ModR/M. The
    // invariant a decoder needs is over `order`, not over the index.
    let cmppd = spec
        .constructors
        .iter()
        .find(|c| {
            c.display.mnemonic.as_deref() == Some("CMP")
                && c.operands.iter().any(|o| o.name == "XmmCondPD")
                && c.operands.iter().any(|o| o.name == "m128")
        })
        .expect("CMP..PD is in the specification");
    let named = |name: &str| {
        cmppd
            .operands
            .iter()
            .position(|o| o.name == name)
            .expect("operand") as u16
    };
    let (cond, m128) = (named("XmmCondPD"), named("m128"));
    assert!(cond < m128, "XmmCondPD prints before m128");
    assert_eq!(cmppd.operands[cond as usize].offset.base, Some(m128));
    assert!(
        position(cmppd, m128) < position(cmppd, cond),
        "but m128 has to be resolved first"
    );

    // Nothing in the whole specification may place an operand relative to one
    // that is resolved after it, or the decoder cannot resolve them at all.
    // Every operand appears in `order` exactly once, or the walk is not a walk
    // of the operands.
    for c in &spec.constructors {
        let mut counted = vec![0usize; c.operands.len()];
        for &i in &c.order {
            counted[i as usize] += 1;
        }
        assert!(
            counted.iter().all(|&n| n == 1),
            "{}: order is not a permutation of the operands",
            c.location
        );
        for (i, operand) in c.operands.iter().enumerate() {
            if let Some(base) = operand.offset.base {
                assert!(
                    position(c, base) < position(c, i as u16),
                    "{}: {} is placed after {}",
                    c.location,
                    operand.name,
                    c.operands[base as usize].name
                );
            }
        }
    }
}

/// Where an operand sits in the order a decoder resolves them in.
fn position(c: &e5r_sleigh::model::Constructor, operand: u16) -> usize {
    c.order
        .iter()
        .position(|&i| i == operand)
        .unwrap_or(usize::MAX)
}

/// A specification, and the mnemonic and memory bytes of each encoding whose
/// meaning that architecture's manual fixes.
type Encodings = (&'static str, &'static [(&'static str, &'static [u8])]);

/// Real encodings, from the published manuals, land on the constructor the
/// specification names for them.
///
/// This is the measurement that says the bit reduction is right rather than
/// merely finished: a mask assembled into the wrong byte, or with the field's
/// bits reversed, parses perfectly and matches nothing. Ten architectures, of
/// every shape the corpus has, and each word is one whose meaning the
/// architecture manual fixes.
///
/// The test is over the instruction mask alone. Several of these
/// specifications also require context bits, which ARM and AArch64 set from a
/// first pass over the same bytes, and running that pass is the decode
/// engine's job rather than the front end's. `aarch64_matches_the_encodings_
/// the_manual_fixes` is the one that goes through the context as well.
#[test]
fn real_encodings_land_in_the_right_bits() {
    let Some(root) = ghidra_root() else {
        eprintln!("no Ghidra tree found; set E5R_GHIDRA to run this");
        return;
    };
    let cases: &[Encodings] = &[
        (
            "ARM/data/languages/ARM7_le.slaspec",
            &[
                ("bx", &[0x1e, 0xff, 0x2f, 0xe1]),
                ("mov", &[0x00, 0x00, 0xa0, 0xe1]),
                ("b", &[0xfe, 0xff, 0xff, 0xea]),
            ],
        ),
        (
            "MIPS/data/languages/mips32be.slaspec",
            &[
                ("jr", &[0x03, 0xe0, 0x00, 0x08]),
                ("addiu", &[0x24, 0x01, 0x00, 0x01]),
                ("lui", &[0x3c, 0x01, 0x00, 0x02]),
            ],
        ),
        (
            "RISCV/data/languages/riscv.ilp32d.slaspec",
            &[
                ("ret", &[0x67, 0x80, 0x00, 0x00]),
                ("addi", &[0x93, 0x00, 0x10, 0x00]),
                ("lui", &[0xb7, 0x02, 0x00, 0x00]),
            ],
        ),
        (
            "Sparc/data/languages/SparcV9_32.slaspec",
            &[
                ("nop", &[0x01, 0x00, 0x00, 0x00]),
                ("sethi", &[0x03, 0x00, 0x00, 0x01]),
            ],
        ),
        (
            "PowerPC/data/languages/ppc_32_be.slaspec",
            &[
                ("blr", &[0x4e, 0x80, 0x00, 0x20]),
                ("addi", &[0x38, 0x21, 0x00, 0x10]),
            ],
        ),
        (
            "6502/data/languages/6502.slaspec",
            &[
                ("NOP", &[0xea]),
                ("JMP", &[0x4c, 0x00, 0x10]),
                ("RTS", &[0x60]),
            ],
        ),
        (
            "Z80/data/languages/z80.slaspec",
            &[("NOP", &[0x00]), ("RET", &[0xc9])],
        ),
        (
            "Atmel/data/languages/avr8.slaspec",
            &[("ret", &[0x08, 0x95]), ("nop", &[0x00, 0x00])],
        ),
        (
            "TI_MSP430/data/languages/TI_MSP430.slaspec",
            &[("ret", &[0x30, 0x41]), ("jmp", &[0xfe, 0x3f])],
        ),
        (
            "x86/data/languages/x86-64.slaspec",
            &[("RET", &[0xc3]), ("PUSH", &[0x55]), ("HLT", &[0xf4])],
        ),
    ];

    let mut checked = 0usize;
    for (spec_path, words) in cases {
        let path = root.join("Ghidra/Processors").join(spec_path);
        if !path.is_file() {
            continue;
        }
        let spec = e5r_sleigh::parse_file(&path).unwrap_or_else(|e| panic!("{spec_path}: {e}"));
        let constructors = &spec.table(spec.root()).constructors;
        for (mnemonic, bytes) in *words {
            checked += 1;
            let named = spec.constructors.iter().any(|c| {
                c.display
                    .mnemonic
                    .as_deref()
                    .is_some_and(|m| m.eq_ignore_ascii_case(mnemonic))
                    && c.resolved
                        .alternatives
                        .iter()
                        .any(|a| a.instr.matches(bytes))
            });
            assert!(
                named,
                "{spec_path}: no {mnemonic} constructor matches {bytes:02x?}"
            );
            // And the mask discriminates: a reduction that lost its bits would
            // match everything and still pass the assertion above.
            let hits = constructors
                .iter()
                .filter(|id| {
                    spec.constructor(**id)
                        .resolved
                        .alternatives
                        .iter()
                        .any(|a| a.instr.matches(bytes))
                })
                .count();
            assert!(
                hits * 10 < constructors.len(),
                "{spec_path}: {bytes:02x?} matched {hits} of {} root constructors",
                constructors.len()
            );
        }
    }
    assert!(checked > 0, "a Ghidra tree was found but held no encodings");
}
