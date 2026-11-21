//! `nocompiler module --format chunks` writes the committed chunk modules
//! (lean/Examples/Link/{One,Two}Chunks.lean, which lean/Examples/LinkChunks.lean
//! decides decode to the modules), and the default format is unchanged.

use std::process::Command;

#[test]
fn module_format_chunks_writes_the_committed_files() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    for (elf, ns) in [("sum.link1.elf", "One"), ("sum.link2.elf", "Two")] {
        let elf = format!("{root}/examples/elf/{elf}");
        let out = Command::new(exe)
            .args(["module", &elf, "--format", "chunks"])
            .args(["--namespace", &format!("Examples.Link.{ns}Chunks")])
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let committed =
            std::fs::read_to_string(format!("{root}/lean/Examples/Link/{ns}Chunks.lean")).unwrap();
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            committed,
            "{ns}Chunks.lean"
        );

        let out = Command::new(exe)
            .args([
                "module",
                &elf,
                "--namespace",
                &format!("Examples.Link.{ns}"),
            ])
            .output()
            .unwrap();
        assert!(out.status.success());
        let committed =
            std::fs::read_to_string(format!("{root}/lean/Examples/Link/{ns}.lean")).unwrap();
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            committed,
            "{ns}.lean"
        );
    }
}
