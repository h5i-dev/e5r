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

/// The modules in chunks are what `module::lean_chunks` writes
/// (lean/Examples/Link/{One,Two}Chunks.lean; lean/Examples/LinkChunks.lean
/// decides they decode to the modules).
#[test]
fn the_committed_chunk_modules_are_what_lean_chunks_writes() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    for (elf, ns) in [("sum.link1.elf", "One"), ("sum.link2.elf", "Two")] {
        let bytes = std::fs::read(root.join("examples/elf").join(elf)).unwrap();
        let m = nocompiler::module::of_binary(&nocompiler::load(&bytes).unwrap()).unwrap();
        let sha = nocompiler::sha256::hex(&nocompiler::sha256::digest(&bytes));
        let got =
            nocompiler::module::lean_chunks(&m, &format!("Examples.Link.{ns}Chunks"), elf, &sha)
                .unwrap();
        let path = root.join(format!("lean/Examples/Link/{ns}Chunks.lean"));
        assert_eq!(
            got,
            std::fs::read_to_string(&path).unwrap(),
            "{} is stale",
            path.display()
        );
    }
}

/// A negative addend, packed: the number lean/Examples/LinkChunks.lean
/// (`reloc_negative`) decodes to this relocation.
#[test]
fn a_negative_addend_packs_as_lean_decodes_it() {
    use nocompiler::module::{Kind, RFunc, Reloc};
    let f = RFunc {
        name: "f".into(),
        entry: 0,
        words: vec![0; 3],
        relocs: vec![Reloc {
            off: 8,
            kind: Kind::PcrelLoI,
            sym: "A".into(),
            addend: -5,
            hi_off: 4,
        }],
    };
    let (bits, syms) = nocompiler::module::pack_relocs(&f).unwrap();
    assert_eq!(bits, "0x00000000000002400002000004000008");
    assert_eq!(syms, ["A"]);
    assert_eq!(nocompiler::module::sym_code("A").unwrap(), "0x00000041");
}

/// The reuse files for the identical rebuild and a one-function edit: every
/// function gets a theorem, except those whose closure holds the edit.
#[test]
fn reuse_lean_states_a_theorem_for_each_unchanged_closure() {
    use nocompiler::module::{ReuseForm, reuse_lean};
    let a = module("sum.link1.elf");
    let (_, t, c) = reuse_lean(
        &a,
        &module("sum.link2.elf"),
        "A",
        "B",
        "R",
        ReuseForm::Verified,
    );
    assert_eq!((t, c), (3, 0));
    let mut e = a.clone();
    let s = e.funcs.iter_mut().find(|f| f.name == "sum").unwrap();
    s.words[0] ^= 1 << 7;
    let (text, t, c) = reuse_lean(&a, &e, "A", "B", "R", ReuseForm::Verified);
    // sum, and _start and sum2 which call it, all changed.
    assert_eq!((t, c), (0, 3));
    assert!(text.contains("theorem c_1 : RChunk.subSeqG [A.f_1] [(1, 1)] [] B.groups = false"));
}

/// Functions in another order in the new module: `_start` comes after
/// `sum`, which it calls, and its theorem still carries (`of_groups_perm`).
#[test]
fn reuse_lean_handles_a_callee_moved_before_its_caller() {
    use nocompiler::module::{ReuseForm, reuse_lean};
    let a = module("sum.link1.elf");
    let mut r = a.clone();
    r.funcs.reverse(); // sum2, sum, _start
    let (text, t, c) = reuse_lean(&a, &r, "A", "B", "R", ReuseForm::Verified);
    assert_eq!((t, c), (3, 0));
    assert!(text.contains("theorem r_0 "), "{text}");
    assert!(
        text.contains("Verified.of_groups_perm (fs' := [A.f_1, A.f_0]) (ks := [(1, 1), (0, 0)])"),
        "{text}"
    );
}

/// Recovery is per function: a function whose code cannot be made
/// relocatable is skipped and reported, and the rest of the module stays
/// (lead 13:42, D's R-D1). Here `sum` starts with an `auipc` nothing uses as
/// a base, as musl's `__cos` does with an `fld` low part.
#[test]
fn an_unrecoverable_function_is_skipped_not_fatal() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let bytes = std::fs::read(root.join("examples/elf/sum.link1.elf")).unwrap();
    let mut bin = nocompiler::load(&bytes).unwrap();
    let f = bin.funcs.iter_mut().find(|f| f.name == "sum").unwrap();
    f.words[0] = 0x0000_0797; // auipc a5, 0
    let entry = f.entry;
    let m = nocompiler::module::of_binary(&bin).unwrap();
    let names: Vec<&str> = m.funcs.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, ["_start", "sum2"]);
    assert_eq!(m.skipped.len(), 1);
    assert_eq!(
        (m.skipped[0].name.as_str(), m.skipped[0].entry),
        ("sum", entry)
    );
    assert!(
        m.skipped[0].reason.contains("has no low part"),
        "{}",
        m.skipped[0].reason
    );
    // The callers keep their calls to `sum`, and the layout still says where it is.
    assert!(m.funcs[0].relocs.iter().any(|r| r.sym == "sum"));
    let text = nocompiler::module::lean(&m, "T", "t", "0");
    assert!(text.contains(&format!(
        "if s = \"sum\" then 0x{entry:x}#64 else -- not in the module"
    )));
    // Unmodified, nothing is skipped.
    assert!(module("sum.link1.elf").skipped.is_empty());
}
