//! `e5r ptx check`: versioned JSON, documented exit statuses, and
//! fail-closed verdicts. The tests that need Lean return early without
//! `lake` (CONTRIBUTING.md: a missing tool skips, it does not pass silently
//! in a way that claims anything).

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_e5r")
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../verification/ptx")
}

fn tmp(name: &str, text: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("e5r-ptx-cli-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    let p = d.join(name);
    std::fs::write(&p, text).unwrap();
    p
}

fn check(ptx: &Path, spec: &Path, extra: &[&str]) -> (i32, Value) {
    let o = Command::new(bin())
        .args(["ptx", "check"])
        .arg(ptx)
        .arg("--spec")
        .arg(spec)
        .arg("--project")
        .arg(root())
        .args(extra)
        .output()
        .unwrap();
    let doc: Value = serde_json::from_slice(&o.stdout)
        .unwrap_or_else(|e| panic!("not JSON ({e}): {}", String::from_utf8_lossy(&o.stdout)));
    assert_eq!(doc["schema"], "e5r.ptx.result.v1");
    (o.status.code().unwrap(), doc)
}

fn vadd_spec() -> String {
    std::fs::read_to_string(root().join("benchmarks/specs/vadd.json")).unwrap()
}

fn vadd() -> PathBuf {
    root().join("benchmarks/correct/vadd_nvcc.ptx")
}

fn has_lake() -> bool {
    Command::new("lake")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

#[test]
fn usage_errors_exit_64() {
    let o = Command::new(bin())
        .args(["ptx", "check", "x.ptx"])
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(64));
    let o = Command::new(bin())
        .args(["ptx", "check", "--bogus"])
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(64));
}

#[test]
fn ptx_outside_the_subset_is_unsupported() {
    let src = std::fs::read_to_string(vadd())
        .unwrap()
        .replace("add.s32", "add.f32");
    let (code, doc) = check(&tmp("f32.ptx", &src), &tmp("v.json", &vadd_spec()), &[]);
    assert_eq!((code, doc["verdict"].as_str()), (2, Some("unsupported")));
    assert_eq!(doc["properties"]["memory_safety"], "unsupported");
}

#[test]
fn spec_outside_the_class_is_unsupported() {
    let s = vadd_spec().replace("\"map32\"", "\"reduce\"");
    let (code, doc) = check(&vadd(), &tmp("c.json", &s), &[]);
    assert_eq!((code, doc["verdict"].as_str()), (2, Some("unsupported")));
    let s = vadd_spec().replace("\"vadd_param_3\"", "\"nope\"");
    let (code, _) = check(&vadd(), &tmp("p.json", &s), &[]);
    assert_eq!(code, 2, "a parameter the spec does not name");
}

#[test]
fn aggregate_abi_requires_a_matching_proof_domain() {
    let src = std::fs::read_to_string(vadd()).unwrap().replace(
        ".param .u64 vadd_param_0",
        ".param .align 8 .b8 vadd_param_0[32]",
    );
    let (code, doc) = check(
        &tmp("aggregate.ptx", &src),
        &tmp("aggregate-spec.json", &vadd_spec()),
        &[],
    );
    assert_eq!((code, doc["verdict"].as_str()), (2, Some("unsupported")));
    assert!(doc["reasons"].as_array().unwrap().iter().any(|r| {
        r.as_str()
            .is_some_and(|s| s.contains("aggregate parameter ABI"))
    }));
}

#[test]
fn malformed_spec_is_an_error() {
    for (name, s) in [
        ("m1.json", "{".to_string()),
        (
            "m2.json",
            vadd_spec().replace("e5r.ptx.spec.v1", "e5r.ptx.spec.v0"),
        ),
        (
            "m3.json",
            vadd_spec().replace("vadd_param_0 + vadd_param_1", "vadd_param_0 +"),
        ),
        (
            "m4.json",
            vadd_spec().replace("vadd_param_0 + vadd_param_1", "q + 1"),
        ),
    ] {
        let (code, doc) = check(&vadd(), &tmp(name, &s), &[]);
        assert_eq!(
            (code, doc["verdict"].as_str()),
            (4, Some("error")),
            "{name}: {doc}"
        );
        assert_ne!(code, 0);
    }
}

#[test]
fn missing_lean_project_is_an_error_not_a_proof() {
    let o = Command::new(bin())
        .args(["ptx", "check"])
        .arg(vadd())
        .arg("--spec")
        .arg(root().join("benchmarks/specs/vadd.json"))
        .args(["--project", "/nonexistent"])
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(4));
}

#[test]
fn a_tiny_timeout_is_unknown_not_proved() {
    if !has_lake() {
        eprintln!("lake not installed: skipped");
        return;
    }
    let (code, doc) = check(
        &vadd(),
        &root().join("benchmarks/specs/vadd.json"),
        &["--timeout", "1", "--no-search"],
    );
    assert_ne!(code, 0, "{doc}");
    assert!(
        matches!(doc["verdict"].as_str(), Some("unknown") | Some("error")),
        "{doc}"
    );
}

#[test]
fn proved_and_refuted_end_to_end() {
    if !has_lake() {
        eprintln!("lake not installed: skipped");
        return;
    }
    let spec = root().join("benchmarks/specs/vadd.json");
    let (code, doc) = check(&vadd(), &spec, &[]);
    assert_eq!(
        (code, doc["verdict"].as_str()),
        (0, Some("proved")),
        "{doc}"
    );
    assert_eq!(doc["properties"]["race_freedom"], "proved");
    let ax: Vec<&str> = doc["theorem"]["axioms"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a.as_str().unwrap())
        .collect();
    assert!(
        ax.iter()
            .all(|a| ["propext", "Classical.choice", "Quot.sound"].contains(a))
    );
    let (code, doc) = check(
        &root().join("benchmarks/buggy/vadd_nobound.ptx"),
        &spec,
        &[],
    );
    assert_eq!(
        (code, doc["verdict"].as_str()),
        (1, Some("refuted")),
        "{doc}"
    );
    assert_eq!(doc["counterexample"]["replayed_in_lean"], true);
    assert_eq!(doc["properties"]["memory_safety"], "refuted");
}

#[test]
fn packing_contract_is_strict_and_needs_proof() {
    let ptx = tmp(
        "packing.ptx",
        ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry pack(.param .u64 input, .param .u64 output, .param .u32 n) { ret; }\n",
    );
    let base = serde_json::json!({"schema":"e5r.ptx.spec.v1", "class":"packing",
        "kernel":"pack", "op":"pack", "input":"input", "output":"output", "length":"n"});
    let run = |tag: &str, v: &Value| {
        let sp = tmp(&format!("packing-{tag}.json"), &v.to_string());
        check(&ptx, &sp, &[])
    };
    let (code, result) = run("no-proof", &base);
    assert_eq!(code, 3);
    assert_eq!(result["verdict"], "unknown");
    assert!(
        result["reasons"]
            .to_string()
            .contains("requires a supplied proof")
    );
    let mut bad = base.clone();
    bad["op"] = "big_endian".into();
    assert_eq!(run("op", &bad).0, 2);
    bad = base.clone();
    bad["output"] = "input".into();
    assert_eq!(run("alias-param", &bad).0, 4);
    bad = base.clone();
    bad["bitorder"] = "big".into();
    assert_eq!(run("unrecognized-field", &bad).0, 4);
    bad = base;
    bad["length"] = "input".into();
    assert_eq!(run("length", &bad).0, 4);
}

#[test]
fn direct_equivalence_requires_bound_original_and_strict_contract() {
    let ptx = tmp(
        "relational.ptx",
        ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k(.param .u64 input, .param .u64 output, .param .u32 n) { ret; }\n",
    );
    let hash = String::from_utf8(Command::new("sha256sum").arg(&ptx).output().unwrap().stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_string();
    let base = serde_json::json!({"schema":"e5r.ptx.spec.v1", "class":"equivalence-unpack4",
        "kernel":"k", "original_ptx":ptx, "original_sha256":hash,
        "input":"input", "output":"output", "length":"n"});
    let run = |tag: &str, v: &Value| {
        let sp = tmp(&format!("relational-{tag}.json"), &v.to_string());
        check(&ptx, &sp, &[])
    };
    for class in [
        "equivalence-unpack4",
        "equivalence-stencil17",
        "equivalence-stencil17-pair2",
    ] {
        let mut base = base.clone();
        base["class"] = class.into();
        let (code, result) = run("no-proof", &base);
        assert_eq!(code, 3, "{result}");
        assert!(
            result["reasons"]
                .to_string()
                .contains("requires a supplied proof")
        );
        let mut bad = base.clone();
        bad["original_sha256"] = "0".repeat(64).into();
        let (code, result) = run("stale-reference", &bad);
        assert_eq!(code, 3, "{result}");
        assert!(result["reasons"].to_string().contains("hash mismatch"));
        bad = base.clone();
        bad["output"] = "input".into();
        assert_eq!(run("alias", &bad).0, 4);
        bad = base.clone();
        bad["input"] = "missing".into();
        assert_eq!(run("param", &bad).0, 2);
        bad = base.clone();
        bad["assume_equal"] = true.into();
        assert_eq!(run("unknown-field", &bad).0, 4);
    }
}

#[test]
fn oss_increment_equivalence_requires_distinct_typed_repeats_parameter() {
    let ptx = tmp(
        "oss-relational.ptx",
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k(.param .u64 input, .param .u64 output, .param .u32 n, .param .u32 repeats) { ret; }\n",
    );
    let hash = String::from_utf8(Command::new("sha256sum").arg(&ptx).output().unwrap().stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_string();
    let base = serde_json::json!({"schema":"e5r.ptx.spec.v1", "class":"equivalence-oss-inc",
        "kernel":"k", "original_ptx":ptx, "original_sha256":hash,
        "input":"input", "output":"output", "length":"n", "repeats":"repeats"});
    let run = |tag: &str, v: &Value| {
        let sp = tmp(&format!("oss-relational-{tag}.json"), &v.to_string());
        check(&ptx, &sp, &[])
    };
    let (code, result) = run("no-proof", &base);
    assert_eq!(code, 3, "{result}");
    assert!(
        result["reasons"]
            .to_string()
            .contains("requires a supplied proof")
    );
    assert!(
        result["lean_spec"]
            .as_str()
            .unwrap()
            .contains("OssInc.Spec")
    );
    assert!(
        result["lean_spec"]
            .as_str()
            .unwrap()
            .contains("\"repeats\"")
    );

    let mut bad = base.clone();
    bad.as_object_mut().unwrap().remove("repeats");
    let (code, result) = run("missing-repeats", &bad);
    assert_eq!(code, 4, "{result}");
    assert!(
        result["reasons"]
            .to_string()
            .contains("requires repeats parameter")
    );
    for alias in ["input", "output", "n"] {
        let mut bad = base.clone();
        bad["repeats"] = alias.into();
        let (code, result) = run(alias, &bad);
        assert_eq!(code, 4, "{result}");
        assert!(
            result["reasons"]
                .to_string()
                .contains("parameter names must differ")
        );
    }
    bad = base.clone();
    bad["repeats"] = "missing".into();
    assert_eq!(run("undeclared-repeats", &bad).0, 2);
    bad = base.clone();
    bad["class"] = "equivalence-unpack4".into();
    let (code, result) = run("unexpected-repeats", &bad);
    assert_eq!(code, 4, "{result}");
    assert!(
        result["reasons"]
            .to_string()
            .contains("unexpected repeats parameter")
    );
    bad = base.clone();
    bad["assume_nonalias"] = true.into();
    assert_eq!(run("unknown-field", &bad).0, 4);
    bad = base;
    bad["original_sha256"] = "0".repeat(64).into();
    let (code, result) = run("stale-original", &bad);
    assert_eq!(code, 3, "{result}");
    assert!(result["reasons"].to_string().contains("hash mismatch"));
}

#[test]
fn scalar_equivalence_rejects_frozen_original_aggregate_abi() {
    let candidate = tmp(
        "scalar-candidate.ptx",
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k(.param .u64 input, .param .u64 output, .param .u32 n) { ret; }\n",
    );
    let original = tmp(
        "aggregate-original.ptx",
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k(.param .u64 input, .param .u64 output, .param .u32 n, .param .align 8 .b8 extra[32]) { ret; }\n",
    );
    let hash = String::from_utf8(
        Command::new("sha256sum")
            .arg(&original)
            .output()
            .unwrap()
            .stdout,
    )
    .unwrap()
    .split_whitespace()
    .next()
    .unwrap()
    .to_string();
    let sp = tmp("aggregate-original-spec.json", &serde_json::json!({"schema":"e5r.ptx.spec.v1", "class":"equivalence-unpack4", "kernel":"k", "original_ptx":original,"original_sha256":hash,"input":"input","output":"output","length":"n"}).to_string());
    let (code, result) = check(&candidate, &sp, &[]);
    assert_eq!(code, 2, "{result}");
    assert!(
        result["reasons"]
            .to_string()
            .contains("aggregate parameter ABI")
    );
}

#[test]
fn zero_segments_equivalence_requires_arbitrary_distinct_typed_scalar() {
    let ptx = tmp(
        "zero-segments-contract.ptx",
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k(.param .u64 input, .param .u64 output, .param .u32 n, .param .u32 mask) { ret; }\n",
    );
    let hash = String::from_utf8(Command::new("sha256sum").arg(&ptx).output().unwrap().stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_string();
    let base = serde_json::json!({"schema":"e5r.ptx.spec.v1", "class":"equivalence-zero-segments", "kernel":"k","original_ptx":ptx,"original_sha256":hash,"input":"input","output":"output","length":"n","scalar":"mask"});
    let run = |tag: &str, v: &Value| {
        check(
            &ptx,
            &tmp(&format!("zero-segments-{tag}.json"), &v.to_string()),
            &[],
        )
    };
    let (code, result) = run("no-proof", &base);
    assert_eq!(code, 3, "{result}");
    assert!(
        result["lean_spec"]
            .as_str()
            .unwrap()
            .contains("ZeroSegments.Spec")
    );
    let mut bad = base.clone();
    bad.as_object_mut().unwrap().remove("scalar");
    assert_eq!(run("missing", &bad).0, 4);
    for alias in ["input", "output", "n"] {
        let mut bad = base.clone();
        bad["scalar"] = alias.into();
        assert_eq!(run(alias, &bad).0, 4);
    }
    bad = base.clone();
    bad["scalar"] = "missing".into();
    assert_eq!(run("undeclared", &bad).0, 2);
    bad = base.clone();
    bad["class"] = "equivalence-unpack4".into();
    assert_eq!(run("other-class", &bad).0, 4);
    bad = base;
    bad["assume_equal"] = true.into();
    assert_eq!(run("unknown-field", &bad).0, 4);
}

#[test]
fn global_symbols_cannot_escape_the_module_initialization_domain() {
    let source = ".version 9.2\n.target sm_86\n.address_size 64\n.global .align 4 .u32 table=1;\n.visible .entry k(){\n.reg .b64 %rd;\nmov.u64 %rd, table;\nret;\n}\n";
    let ptx = tmp("global-domain.ptx", source);
    let spec = tmp(
        "global-domain.json",
        r#"{"schema":"e5r.ptx.spec.v1","class":"map32","kernel":"k"}"#,
    );
    let (_, doc) = check(&ptx, &spec, &[]);
    assert_eq!(doc["verdict"], "unsupported");
    assert!(doc["reasons"].to_string().contains("initialized-module"));
    let exported = Command::new(bin())
        .args(["ptx", "export"])
        .arg(&ptx)
        .output()
        .unwrap();
    assert!(exported.status.success());
    assert!(
        String::from_utf8(exported.stdout)
            .unwrap()
            .contains("globals := [⟨\"table\", 4, [1, 0, 0, 0]⟩]")
    );
    let cases = tmp("global-cases.txt", "");
    let run = Command::new(bin())
        .args(["ptx", "run", "--cases"])
        .arg(cases)
        .arg(ptx)
        .output()
        .unwrap();
    assert!(!run.status.success());
    assert!(
        String::from_utf8(run.stderr)
            .unwrap()
            .contains("module placement")
    );
}
