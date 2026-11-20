//! The supplied-proof route (`nocompiler ptx check --proof PROOF.lean`,
//! experiment/docs/ptx.md, "Supplied proofs").
//!
//! The tool, not the author, writes the statement: module `NoCompilerSpec` with the
//! kernel exported from the PTX, the spec, and `NoCompilerSpec.statement : Prop`,
//! the same class statement the automation proves. The supplied file must
//! be module `NoCompilerProof` proving `theorem NoCompilerProof.correct :
//! NoCompilerSpec.statement`, and must name in a manifest the SHA-256 of the PTX and
//! the spec and the Lean toolchain it was written for:
//!
//! ```text
//! /- nocompiler-proof ptx=<sha256> spec=<sha256> toolchain=leanprover/lean4:v4.35.0 -/
//! ```
//!
//! After both modules compile, the independent checker
//! (`verification/ptx/Checker/ProofCheck.lean`, the `proofcheck` executable)
//! replays every declaration of the proof through the kernel, requires the
//! theorem's type to be exactly `NoCompilerSpec.statement`, refuses declared
//! axioms and allows only `propext`, `Quot.sound` and `Classical.choice`
//! among the theorem's axioms. Only then is the verdict `proved`, recorded
//! as supplied.

use super::{Options, Verdict, first_error, run_lean_env, sha};
use serde_json::{Value, json};
use std::path::Path;

/// The manifest's three fields, if the file has one.
fn manifest(text: &str) -> Option<(String, String, String)> {
    let i = text.find("nocompiler-proof ")? + "nocompiler-proof ".len();
    let line = text[i..].lines().next()?;
    let mut ptx = None;
    let mut spec = None;
    let mut tc = None;
    for w in line.split_whitespace() {
        if let Some(v) = w.strip_prefix("ptx=") {
            ptx = Some(v.to_string());
        } else if let Some(v) = w.strip_prefix("spec=") {
            spec = Some(v.to_string());
        } else if let Some(v) = w.strip_prefix("toolchain=") {
            tc = Some(v.to_string());
        }
    }
    Some((ptx?, spec?, tc?))
}

/// Check a supplied proof of `statement_module`'s `NoCompilerSpec.statement`.
/// Returns the verdict and fills `doc["proof"]` and, when accepted,
/// `doc["theorem"]`.
#[allow(clippy::too_many_arguments)]
pub fn check(
    o: &Options,
    doc: &mut Value,
    proof: &Path,
    statement_module: &str,
    statement: &str,
    definition: &str,
    phash: &str,
    shash: &str,
    toolchain: &str,
    proj: &Path,
    dir: &Path,
) -> (Verdict, Option<String>) {
    doc["proof"] =
        json!({"supplied": true, "path": proof.display().to_string(), "accepted": false});
    let (bytes, prhash) = match sha(proof) {
        Ok(x) => x,
        Err(e) => return (Verdict::Error, Some(e)),
    };
    doc["proof"]["sha256"] = json!(prhash);
    let Ok(text) = String::from_utf8(bytes) else {
        return (Verdict::Error, Some("the proof is not UTF-8".into()));
    };
    let Some((mp, ms, mt)) = manifest(&text) else {
        return (
            Verdict::Unknown,
            Some(
                "supplied proof refused: no `nocompiler-proof ptx=... spec=... toolchain=...` manifest"
                    .into(),
            ),
        );
    };
    doc["proof"]["manifest"] = json!({"ptx": mp, "spec": ms, "toolchain": mt});
    let mut stale = Vec::new();
    if mp != phash {
        stale.push(format!("ptx {mp} (the PTX is {phash})"));
    }
    if ms != shash {
        stale.push(format!("spec {ms} (the spec is {shash})"));
    }
    if mt != toolchain {
        stale.push(format!("toolchain {mt} (the project uses {toolchain})"));
    }
    if !stale.is_empty() {
        return (
            Verdict::Unknown,
            Some(format!(
                "supplied proof refused: written for a different {}",
                stale.join(", ")
            )),
        );
    }
    for (f, t) in [
        ("NoCompilerSpec.lean", statement_module),
        ("NoCompilerProof.lean", text.as_str()),
    ] {
        if let Err(e) = std::fs::write(dir.join(f), t) {
            return (Verdict::Error, Some(e.to_string()));
        }
    }
    for f in ["NoCompilerSpec.olean", "NoCompilerProof.olean"] {
        let _ = std::fs::remove_file(dir.join(f));
    }
    let d = dir.display().to_string();
    let env = [("NOCOMPILER_PROOF_DIR", d.as_str())];
    let compile = |m: &str| {
        run_lean_env(
            proj,
            &[
                "env",
                "sh",
                "-c",
                &format!(
                    "cd \"$NOCOMPILER_PROOF_DIR\" && LEAN_PATH=\"$LEAN_PATH:$NOCOMPILER_PROOF_DIR\" lean -o {m}.olean {m}.lean"
                ),
            ],
            o.timeout,
            o.memory_mb,
            &env,
        )
    };
    let r = compile("NoCompilerSpec");
    if !r.ok {
        return (
            Verdict::Error,
            Some(format!(
                "the generated statement does not compile: {}",
                first_error(&r.output)
            )),
        );
    }
    let r = compile("NoCompilerProof");
    doc["lean"]["proof_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
    if !dir.join("NoCompilerProof.olean").exists() {
        let why = r
            .limit
            .map(|l| format!("stopped: {l}"))
            .unwrap_or_else(|| first_error(&r.output));
        return (
            Verdict::Unknown,
            Some(format!(
                "supplied proof refused: it does not compile: {why}"
            )),
        );
    }
    let checker = proj
        .join(".lake/build/bin/proofcheck")
        .display()
        .to_string();
    let r = run_lean_env(
        proj,
        &[
            "env",
            "sh",
            "-c",
            &format!(
                "cd \"$NOCOMPILER_PROOF_DIR\" && LEAN_PATH=\"$LEAN_PATH:$NOCOMPILER_PROOF_DIR\" \"{checker}\" \
                 NoCompilerSpec NoCompilerProof NoCompilerProof.correct NoCompilerSpec.statement"
            ),
        ],
        o.timeout,
        o.memory_mb,
        &env,
    );
    doc["lean"]["proof_check_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
    let line = r
        .output
        .lines()
        .rev()
        .find(|l| l.trim_start().starts_with('{'))
        .unwrap_or("");
    let res: Value = serde_json::from_str(line).unwrap_or(Value::Null);
    doc["proof"]["check"] = res.clone();
    if res["ok"] != json!(true) {
        let why = res["reason"]
            .as_str()
            .map(str::to_string)
            .or(r.limit.map(|l| format!("stopped: {l}")))
            .unwrap_or_else(|| first_error(&r.output));
        return (
            Verdict::Unknown,
            Some(format!("supplied proof refused: {why}")),
        );
    }
    doc["proof"]["accepted"] = json!(true);
    doc["theorem"] = json!({"name": "NoCompilerProof.correct", "statement": statement,
        "definition": definition, "axioms": res["axioms"], "generated": false,
        "checked_by": "proofcheck: kernel replay of every declaration of the proof"});
    (Verdict::Proved, None)
}

/// The statement module: `prelude` (kernel and spec in namespace
/// `NoCompilerSpec`) and `statement`.
pub fn statement_module(prelude: &str, statement: &str) -> String {
    format!(
        "{prelude}\n/-- The theorem a supplied proof must prove, generated by `nocompiler ptx check`. -/\n\
         def statement : Prop := {statement}\n\nend NoCompilerSpec\n"
    )
}
