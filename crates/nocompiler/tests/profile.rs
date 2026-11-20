//! The profile checker on functions written to break one rule each, and on
//! ones that must pass; `.nocompiler.struct` round trips; `annotate` and `export`.
//!
//! The functions are assembled with clang and linked with ld.lld; skips,
//! loudly, without them.

use std::path::PathBuf;
use std::process::Command;

fn tool(var: &str, names: &[&str]) -> Option<String> {
    let cands: Vec<String> = match std::env::var(var) {
        Ok(v) => vec![v],
        Err(_) => names.iter().map(|s| s.to_string()).collect(),
    };
    cands.into_iter().find(|c| {
        Command::new(c)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    })
}

struct Tools {
    clang: String,
    lld: String,
    dir: PathBuf,
}

fn tools(test: &str) -> Option<Tools> {
    let clang = tool("CLANG", &["clang"])?;
    let lld = tool("LLD", &["ld.lld", "ld.lld-20", "ld.lld-19", "ld.lld-18"])?;
    let dir =
        std::env::temp_dir().join(format!("nocompiler-profile-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    Some(Tools { clang, lld, dir })
}

/// Assemble and link `body` (functions `f` and `g` plus `_start`).
fn build(t: &Tools, name: &str, body: &str) -> Vec<u8> {
    let src = format!(
        ".text\n.globl _start\n.type _start,@function\n_start:\n  call f\n  li a7, 93\n  ecall\n  ret\n.size _start, .-_start\n{body}"
    );
    let s = t.dir.join(format!("{name}.S"));
    let o = t.dir.join(format!("{name}.o"));
    let e = t.dir.join(format!("{name}.elf"));
    std::fs::write(&s, src).unwrap();
    assert!(
        Command::new(&t.clang)
            .args([
                "--target=riscv64-unknown-elf",
                "-march=rv64im_zba_zbb",
                "-mabi=lp64",
                "-mno-relax",
                "-c"
            ])
            .arg(&s)
            .arg("-o")
            .arg(&o)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(&t.lld)
            .args(["-static", "-e", "_start"])
            .arg(&o)
            .arg("-o")
            .arg(&e)
            .status()
            .unwrap()
            .success()
    );
    std::fs::read(&e).unwrap()
}

fn func(name: &str, code: &str) -> String {
    format!(".globl {name}\n.type {name},@function\n{name}:\n{code}\n.size {name}, .-{name}\n")
}

/// The rules `f` violates.
fn rules(bytes: &[u8]) -> Vec<&'static str> {
    let bin = nocompiler::load(bytes).unwrap();
    let r = bin.check().into_iter().find(|r| r.name == "f").expect("f");
    // What stops it at L1 or below, else why it is not at L2.
    let vs = match r.result {
        Ok(_) => r.missed,
        Err(vs) => vs,
    };
    let mut v: Vec<&'static str> = vs.iter().map(|v| v.rule).collect();
    v.sort();
    v.dedup();
    v
}

const CASES: &[(&str, &str, &[&str])] = &[
    // name, body of f, the rules it violates
    ("leaf", "  add a0, a0, a1\n  ret", &[]),
    (
        "loop",
        "  li a2, 0\n1:\n  beqz a1, 2f\n  ld a3, 0(a0)\n  add a2, a2, a3\n  addi a0, a0, 8\n  addi a1, a1, -1\n  j 1b\n2:\n  mv a0, a2\n  ret",
        &[],
    ),
    (
        "nested-loops",
        "1:\n  beqz a0, 4f\n  mv a2, a1\n2:\n  beqz a2, 3f\n  addi a2, a2, -1\n  j 2b\n3:\n  addi a0, a0, -1\n  j 1b\n4:\n  ret",
        &[],
    ),
    (
        "break-from-loop",
        "1:\n  beqz a0, 2f\n  bltz a1, 2f\n  addi a0, a0, -1\n  j 1b\n2:\n  ret",
        &[],
    ),
    (
        "frame-and-call",
        "  addi sp, sp, -16\n  sd ra, 8(sp)\n  call g\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret",
        &[],
    ),
    ("tail-call", "  addi a0, a0, 1\n  tail g", &[]),
    ("csr", "  csrr a0, cycle\n  ret", &["R1 decode"]),
    ("fence", "  fence\n  ret", &["R1 decode"]),
    ("indirect-jump", "  jr a0", &["R2 control"]),
    (
        "indirect-call",
        "  addi sp, sp, -16\n  sd ra, 8(sp)\n  jalr a0\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret",
        &["R2 control"],
    ),
    ("falls-through", "  addi a0, a0, 1", &["R2 control"]),
    ("link-t0", "  jal t0, 1f\n1:\n  ret", &["R2 control"]),
    (
        "into-a-pair",
        "  beqz a0, 1f\n  auipc t1, 0\n1:\n  jalr zero, 4(t1)",
        &["R2 control"],
    ),
    (
        "into-loop",
        "  beqz a0, 2f\n1:\n  addi a1, a1, 1\n2:\n  addi a0, a0, -1\n  bnez a0, 1b\n  ret",
        &["R3 structure"],
    ),
    ("writes-gp", "  li gp, 0\n  ret", &["R4 registers"]),
    // Writing ra also loses its entry value at the return (6e).
    (
        "writes-ra",
        "  li ra, 0\n  ret",
        &["R4 registers", "R6e save"],
    ),
    // R6 (v1): the frame rule.
    ("sp-in-arithmetic", "  add a0, sp, a1\n  ret", &["R6a sp"]),
    ("sp-stored", "  sd sp, 0(a0)\n  ret", &["R6a sp"]),
    (
        "stack-argument",
        "  ld a0, 0(sp)\n  ret",
        &["R6c sp access"],
    ),
    (
        "slot-half-read",
        "  addi sp, sp, -16\n  sd s0, 8(sp)\n  li s0, 1\n  lw a0, 8(sp)\n  ld s0, 8(sp)\n  addi sp, sp, 16\n  ret",
        &["R6c sp access"],
    ),
    (
        "no-restore",
        "  addi sp, sp, -16\n  sd s0, 8(sp)\n  li s0, 1\n  addi sp, sp, 16\n  ret",
        &["R6e save"],
    ),
    ("no-save", "  li s1, 1\n  ret", &["R6e save"]),
    (
        "saved-and-restored",
        "  addi sp, sp, -16\n  sd s0, 8(sp)\n  li s0, 1\n  ld s0, 8(sp)\n  addi sp, sp, 16\n  ret",
        &[],
    ),
    ("sp-by-add", "  add sp, sp, a0\n  ret", &["R5 stack"]),
    (
        "sp-misaligned",
        "  addi sp, sp, -8\n  addi sp, sp, 8\n  ret",
        &["R5 stack"],
    ),
    ("sp-unbalanced", "  addi sp, sp, -16\n  ret", &["R5 stack"]),
    (
        "sp-paths-differ",
        "  beqz a0, 1f\n  addi sp, sp, -16\n1:\n  ret",
        &["R5 stack"],
    ),
];

#[test]
fn each_rule_is_enforced() {
    let Some(t) = tools("rules") else {
        eprintln!("SKIPPED each_rule_is_enforced: needs clang and ld.lld");
        return;
    };
    let g = func("g", "  ret");
    let mut wrong = Vec::new();
    for (name, body, want) in CASES {
        let bytes = build(&t, name, &format!("{}{g}", func("f", body)));
        let got = rules(&bytes);
        if got != *want {
            wrong.push(format!("{name}: expected {want:?}, got {got:?}"));
        }
    }
    let _ = std::fs::remove_dir_all(&t.dir);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn recovered_structure_of_nested_loops() {
    let Some(t) = tools("nest") else {
        eprintln!("SKIPPED recovered_structure_of_nested_loops: needs clang and ld.lld");
        return;
    };
    let (_, body, _) = CASES.iter().find(|c| c.0 == "nested-loops").unwrap();
    let bytes = build(&t, "nest", &func("f", body));
    let bin = nocompiler::load(&bytes).unwrap();
    let m = bin
        .check()
        .into_iter()
        .find(|r| r.name == "f")
        .unwrap()
        .result
        .unwrap();
    // loop { block { ...; loop { block { ... } } } }: an outer loop whose body
    // is a block (exited at 4:), with the inner loop and its exit block inside.
    use nocompiler::profile::Kind;
    fn shape(ns: &[nocompiler::profile::Node]) -> String {
        ns.iter()
            .map(|n| {
                format!(
                    "{}({})",
                    if n.kind == Kind::Loop { "L" } else { "B" },
                    shape(&n.children)
                )
            })
            .collect()
    }
    assert_eq!(shape(&m.nodes), "B(L(B(L())))");
    let _ = std::fs::remove_dir_all(&t.dir);
}

#[test]
fn metadata_round_trips_and_is_checked() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");
    let bytes = std::fs::read(path).unwrap();
    let bin = nocompiler::load(&bytes).unwrap();
    let recorded = bin.recorded.clone().unwrap();
    let names: std::collections::BTreeMap<u64, String> = bin
        .funcs
        .iter()
        .map(|f| (f.entry, f.name.clone()))
        .collect();
    let entries: std::collections::BTreeMap<String, u64> = bin
        .funcs
        .iter()
        .map(|f| (f.name.clone(), f.entry))
        .collect();
    let enc = nocompiler::meta::encode(&recorded, &names).unwrap();
    let back: Vec<_> = nocompiler::meta::decode(&enc)
        .unwrap()
        .iter()
        .map(|r| r.place(entries[&r.meta.name], &entries).unwrap())
        .collect();
    assert_eq!(back, recorded);
    assert!(
        nocompiler::meta::decode(&enc[..enc.len() - 1]).is_err(),
        "truncation is an error"
    );
    let mut extra = enc.clone();
    extra.push(0);
    assert!(
        nocompiler::meta::decode(&extra).is_err(),
        "trailing bytes are an error"
    );

    // A recorded frame that is not the code's is rule M1.
    let mut lie = recorded.clone();
    lie[0].frame += 16;
    let mut b2 = nocompiler::load(&bytes).unwrap();
    b2.recorded = Some(lie);
    let bad = b2.check();
    assert!(bad.iter().any(|r| {
        r.result
            .as_ref()
            .is_err_and(|v| v.iter().any(|v| v.rule == "M1 metadata"))
    }));

    // A recorded tree that does not explain a branch is rule R3.
    let mut lie = recorded.clone();
    let sum = lie.iter_mut().find(|m| m.name == "sum").unwrap();
    sum.nodes[0].children.clear();
    let mut b3 = nocompiler::load(&bytes).unwrap();
    b3.recorded = Some(lie);
    let r = b3.check().into_iter().find(|r| r.name == "sum").unwrap();
    assert!(
        r.result
            .is_err_and(|v| v.iter().any(|v| v.rule == "R3 structure"))
    );
}

#[test]
fn rejects_what_is_not_the_profile() {
    assert!(nocompiler::load(b"not an elf").is_err());
    // An x86-64 ELF: the test binary itself is one on the usual CI host.
    let me = std::fs::read(std::env::current_exe().unwrap()).unwrap();
    if me.get(18..20) == Some(&[0x3e, 0x00]) {
        assert!(nocompiler::load(&me).err().unwrap().contains("not RISC-V"));
    }
}
