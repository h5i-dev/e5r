//! The core commands through the `nocompiler` binary: output, exit codes, and
//! the committed Lean images being what `export` writes. (Moved from
//! crates/nocompiler/tests/profile.rs when the binary moved to this crate.)

use std::process::Command;

#[test]
fn cli_check_annotate_export() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let elf = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");
    let out = Command::new(exe)
        .args(["check", elf, "--json"])
        .output()
        .unwrap();
    assert!(out.status.success());
    let s = String::from_utf8(out.stdout).unwrap();
    assert!(
        s.contains("\"name\":\"sum\",\"entry\":70032,\"level\":\"L2\",\"conforms\":true"),
        "{s}"
    );

    // Export is what each committed Lean image was generated from.
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    for (name, module) in [("sum", "Sum"), ("hello", "Hello")] {
        let out = Command::new(exe)
            .args(["export", "--lean-level-check", &format!("{root}/examples/elf/{name}.elf")])
            .args(["--namespace", &format!("Examples.{module}.Image")])
            .output()
            .unwrap();
        assert!(out.status.success());
        let committed =
            std::fs::read_to_string(format!("{root}/lean/Examples/{module}/Image.lean")).unwrap();
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            committed,
            "lean/Examples/{module}/Image.lean is stale: run examples/build.sh --update"
        );
    }

    // And the images in chunk format (lean/NoCompiler/Image.lean, "Code in chunks").
    for (elf, module) in [
        ("examples/elf/hello.elf", "HelloImage"),
        ("examples/demo/elf/cobs.b.elf", "CobsImage"),
        ("examples/demo/elf/sum.b.elf", "SumBImage"),
    ] {
        let out = Command::new(exe)
            .args(["export", "--lean-level-check", &format!("{root}/{elf}"), "--format", "chunks"])
            .args(["--namespace", &format!("Examples.Chunks.{module}")])
            .output()
            .unwrap();
        assert!(out.status.success());
        let committed =
            std::fs::read_to_string(format!("{root}/lean/Examples/Chunks/{module}.lean")).unwrap();
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            committed,
            "lean/Examples/Chunks/{module}.lean is stale"
        );
    }

    assert_eq!(
        Command::new(exe)
            .args(["check", "/nonexistent"])
            .status()
            .unwrap()
            .code(),
        Some(2)
    );
    assert_eq!(
        Command::new(exe).arg("frobnicate").status().unwrap().code(),
        Some(2)
    );
}

/// A reader that stops early (`nocompiler disasm FILE | head`) must not make the
/// tool panic: the pipe is closed before the tool writes.
#[test]
fn a_closed_pipe_is_not_a_panic() {
    use std::process::Stdio;
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let elf = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");
    for cmd in ["disasm", "check"] {
        let mut child = Command::new(exe)
            .args([cmd, elf])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        drop(child.stdout.take());
        let out = child.wait_with_output().unwrap();
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(!err.contains("panicked"), "{cmd}: {err}");
        assert_eq!(out.status.code(), Some(0), "{cmd}: {err}");
    }
}
