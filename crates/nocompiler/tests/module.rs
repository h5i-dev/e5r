//! `nocompiler module`: the module recovered from a binary does not depend on
//! where the binary was linked (examples/link/build.sh links one object twice).

use std::path::PathBuf;

fn module(name: &str) -> nocompiler::module::Module {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/elf")
        .join(name);
    let bytes = std::fs::read(p).unwrap();
    nocompiler::module::of_binary(&nocompiler::load(&bytes).unwrap()).unwrap()
}

#[test]
fn the_same_object_at_two_layouts_is_the_same_module() {
    let (a, b) = (module("sum.link1.elf"), module("sum.link2.elf"));
    assert_ne!(a.text_addr, b.text_addr);
    let key = |m: &nocompiler::module::Module| {
        m.funcs
            .iter()
            .map(|f| (f.name.clone(), f.words.clone(), f.relocs.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(key(&a), key(&b));
    // sum2 calls sum twice; _start forms a data address and calls sum twice.
    let sum2 = a.funcs.iter().find(|f| f.name == "sum2").unwrap();
    assert_eq!(sum2.relocs.len(), 2);
    let start = a.funcs.iter().find(|f| f.name == "_start").unwrap();
    assert_eq!(
        start
            .relocs
            .iter()
            .filter(|r| r.kind == nocompiler::module::Kind::PcrelHi)
            .count(),
        1
    );
    // The relocated fields are zero.
    assert!(
        sum2.relocs
            .iter()
            .all(|r| sum2.words[(r.off / 4) as usize] & 0xffff_f000 == 0)
    );
}

#[test]
fn every_committed_binary_has_a_module() {
    for e in ["sum.elf", "hello.elf"] {
        let m = module(e);
        assert!(!m.funcs.is_empty(), "{e}");
    }
}

#[test]
fn both_links_give_the_committed_ledger() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let want = std::fs::read_to_string(root.join("examples/link/ledger.jsonl")).unwrap();
    for e in ["sum.link1.elf", "sum.link2.elf"] {
        let mut out = String::new();
        nocompiler::cmd::ledger(
            &root.join("examples/elf").join(e),
            Some(&root.join("examples/link/proofs.tsv")),
            &mut out,
        )
        .unwrap();
        assert_eq!(out, want, "{e}");
    }
}

/// Criterion 3 with calls: `sum2` is proved at both links by the same text.
#[test]
fn sum2_has_one_proof_text_for_both_links() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean/Examples/LinkCalls.lean");
    let s = std::fs::read_to_string(p).unwrap();
    let blocks: Vec<&str> = s
        .split("-- PROOF\n")
        .skip(1)
        .map(|b| b.split("-- END PROOF").next().unwrap())
        .collect();
    assert_eq!(blocks.len(), 2);
    assert_eq!(blocks[0], blocks[1]);
    assert!(!blocks[0].contains("0x"), "the proof names an address");
}

/// The ledger's `sha256` is what `sha256sum` prints for the function's
/// canonical form (it was once SHA-256 of that digest).
#[test]
fn the_ledger_key_is_sha256sum_of_the_canonical_form() {
    use std::io::Write;
    let m = module("sum.link1.elf");
    let sum = m.funcs.iter().find(|f| f.name == "sum").unwrap();
    let canon = nocompiler::module::canonical(sum);
    let ours = nocompiler::sha256::hex(&nocompiler::sha256::digest(&canon));
    assert_eq!(
        ours,
        "a3944f27b6cece706dcd9e118d7709c7c54b34f52b32fcb3e9800e95a30990ef"
    );
    let want = include_str!("../../../examples/link/ledger.jsonl");
    assert!(want.contains(&format!("\"name\":\"sum\",\"sha256\":\"{ours}\"")));
    let Ok(mut child) = std::process::Command::new("sha256sum")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
    else {
        eprintln!("sha256sum not installed: skipping the live comparison");
        return;
    };
    child.stdin.take().unwrap().write_all(&canon).unwrap();
    let out = child.wait_with_output().unwrap();
    assert_eq!(String::from_utf8(out.stdout).unwrap()[..64], ours);
}
