//! The tree diff (`nocompiler refine`, docs/isa/refine.md item 5) on the
//! committed example binaries (examples/refine/diff/build.sh): an edit that
//! keeps the shape is a straight-line region; an inserted instruction is a
//! straight-line region, the moved branches jump pairs; a function against itself
//! has no region. And the generated Lean is the committed one.

use std::path::PathBuf;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn diff(a: &str, b: &str) -> (String, String) {
    let mut out = String::new();
    let tmp = std::env::temp_dir().join(format!(
        "nocompiler-treediff-{}-{a}-{b}.lean",
        std::process::id()
    ));
    nocompiler::cmd::refine(
        &root()
            .join("examples/elf")
            .join(format!("refine-sum-{a}.elf")),
        &root()
            .join("examples/elf")
            .join(format!("refine-sum-{b}.elf")),
        "sum",
        None,
        Some(&format!(
            "Examples.Refine.Diff.{}{}",
            a.to_uppercase(),
            b.to_uppercase()
        )),
        Some(&tmp),
        Some((
            "Examples.Refine.Diff.ImgA",
            &format!("Examples.Refine.Diff.Img{}", b.to_uppercase()),
        )),
        false,
        &mut out,
    )
    .unwrap();
    let lean = std::fs::read_to_string(&tmp).unwrap();
    let _ = std::fs::remove_file(&tmp);
    (out, lean)
}

#[test]
fn a_commuted_add_is_one_straight_line_region() {
    let (out, lean) = diff("a", "b");
    assert!(
        out.starts_with("8 instructions paired; 1 changed interval(s)"),
        "{out}"
    );
    assert!(
        out.contains("1 instr  <->  B [0x1112c, 0x11130) 1 instr  straight-line"),
        "{out}"
    );
    let want = std::fs::read_to_string(root().join("lean/Examples/Refine/Diff/AB.lean")).unwrap();
    assert_eq!(
        lean, want,
        "lean/Examples/Refine/Diff/AB.lean is not what refine writes"
    );
}

#[test]
fn an_inserted_instruction_is_a_straight_line_region_with_jump_pairs() {
    let (out, lean) = diff("a", "c");
    assert!(
        out.starts_with("8 instructions paired; 1 changed interval(s)"),
        "{out}"
    );
    assert!(
        out.contains(
            "A [0x1112c, 0x11130) 1 instr  <->  B [0x1112c, 0x11134) 2 instr  straight-line"
        ),
        "{out}"
    );
    // The loop's branches are jump pairs: the same branch, each side its own offset.
    assert!(lean.contains("⟨0x11140#64, 0x1113c#64,"), "{lean}");
    assert!(lean.contains("theorem refines"), "{lean}");
    let want = std::fs::read_to_string(root().join("lean/Examples/Refine/Diff/AC.lean")).unwrap();
    assert_eq!(lean, want);
}

#[test]
fn a_region_grows_until_its_sides_agree() {
    // D steps the counter by -2 then +1: `addi a1,-1` against `addi a1,-2`
    // alone differs on a1; with the next pair and D's extra `addi a1,1` it
    // does not.
    let (out, lean) = diff("a", "d");
    assert!(
        out.contains(
            "A [0x11130, 0x11138) 2 instr  <->  B [0x11130, 0x1113c) 3 instr  straight-line "
        ),
        "{out}"
    );
    assert!(lean.contains("theorem region0_ok"), "{lean}");
    let want = std::fs::read_to_string(root().join("lean/Examples/Refine/Diff/AD.lean")).unwrap();
    assert_eq!(lean, want);
}

#[test]
fn a_function_against_itself_has_no_region() {
    let mut out = String::new();
    let a = root().join("examples/elf/refine-sum-a.elf");
    nocompiler::cmd::refine(&a, &a, "sum", None, None, None, None, false, &mut out).unwrap();
    assert!(
        out.starts_with("9 instructions paired; 0 changed interval(s)"),
        "{out}"
    );
}
