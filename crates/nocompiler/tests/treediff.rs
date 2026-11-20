//! The tree diff (`nocompiler refine`, docs/isa/refine.md item 5) on the
//! committed example binaries (examples/refine/diff/build.sh): an edit that
//! keeps the shape is a straight-line region; one that moves the loop's
//! branch offsets is a region covering the block; a function against itself
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
fn a_longer_loop_body_makes_the_block_a_region() {
    let (out, lean) = diff("a", "c");
    assert!(
        out.starts_with("3 instructions paired; 1 changed interval(s)"),
        "{out}"
    );
    assert!(
        out.contains("A [0x11124, 0x1113c) 6 instr  <->  B [0x11124, 0x11140) 7 instr  structured"),
        "{out}"
    );
    let want = std::fs::read_to_string(root().join("lean/Examples/Refine/Diff/AC.lean")).unwrap();
    assert_eq!(lean, want);
}

#[test]
fn a_function_against_itself_has_no_region() {
    let mut out = String::new();
    let a = root().join("examples/elf/refine-sum-a.elf");
    nocompiler::cmd::refine(&a, &a, "sum", None, None, None, &mut out).unwrap();
    assert!(
        out.starts_with("9 instructions paired; 0 changed interval(s)"),
        "{out}"
    );
}
