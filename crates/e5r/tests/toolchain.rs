//! `e5r cc` on a corpus of ordinary C (tests/cc): what the profile's flags
//! keep inside the profile, and what stays outside because the source asks
//! for it. Needs clang and ld.lld; skips, loudly, without them.

use std::process::Command;

fn have_tools() -> bool {
    e5r::cc::tools().is_ok()
}

fn cc(name: &str) -> (bool, String) {
    let exe = env!("CARGO_BIN_EXE_e5r");
    let src = format!("{}/tests/cc/{name}.c", env!("CARGO_MANIFEST_DIR"));
    let dir = std::env::temp_dir().join(format!("e5r-cc-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let out = dir.join(format!("{name}.elf"));
    let o = Command::new(exe)
        .args(["cc", &src, "-o"])
        .arg(&out)
        .output()
        .unwrap();
    let text =
        String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
    assert!(out.exists(), "{name}: no output written\n{text}");
    (o.status.success(), text)
}

#[test]
fn ordinary_c_conforms() {
    if !have_tools() {
        eprintln!("SKIPPED ordinary_c_conforms: needs clang and ld.lld");
        return;
    }
    for name in ["loops", "switch", "recur", "structs"] {
        let (ok, text) = cc(name);
        assert!(ok, "{name} should conform under e5r cc:\n{text}");
        assert!(text.contains("all conform"), "{text}");
    }
}

#[test]
fn function_pointers_do_not() {
    if !have_tools() {
        eprintln!("SKIPPED function_pointers_do_not: needs clang and ld.lld");
        return;
    }
    let (ok, text) = cc("fnptr");
    assert!(!ok, "a call through a function pointer conformed:\n{text}");
    assert!(text.contains("[R2 control] indirect jump"), "{text}");
}

/// Without `-mllvm -disable-block-placement`, clang rotates loops so their
/// header is entered by a forward jump into the middle: the reason the flag
/// is in `e5r::cc::CFLAGS`.
#[test]
fn block_placement_is_why_the_flag_is_there() {
    let Ok((clang, lld)) = e5r::cc::tools() else {
        eprintln!("SKIPPED block_placement_is_why_the_flag_is_there: needs clang and ld.lld");
        return;
    };
    let dir = std::env::temp_dir().join(format!("e5r-cc-bp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let flags: Vec<&str> = e5r::cc::CFLAGS
        .iter()
        .copied()
        .filter(|f| *f != "-mllvm" && *f != "-disable-block-placement")
        .collect();
    let obj = dir.join("loops.o");
    let elf = dir.join("loops.elf");
    let src = format!("{}/tests/cc/loops.c", env!("CARGO_MANIFEST_DIR"));
    assert!(
        Command::new(&clang)
            .args(&flags)
            .args(["-O2", "-c", &src, "-o"])
            .arg(&obj)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(&lld)
            .args(["-static", "-e", "_start"])
            .arg(&obj)
            .arg("-o")
            .arg(&elf)
            .status()
            .unwrap()
            .success()
    );
    let bytes = std::fs::read(&elf).unwrap();
    let bin = e5r::load(&bytes).unwrap();
    let r3 = bin
        .check()
        .into_iter()
        .filter(|r| {
            r.result
                .as_ref()
                .is_err_and(|v| v.iter().any(|v| v.rule == "R3 structure"))
        })
        .count();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        r3 > 0,
        "clang's block placement no longer breaks R3 on loops.c; is the flag still needed?"
    );
}
