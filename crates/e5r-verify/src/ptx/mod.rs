//! `e5r ptx`: export, check and run PTX kernels
//! (docs/verification/ptx.md, "Command line").
//!
//! `check` is fail-closed: the exit status is 0 only when Lean has checked
//! `E5rCheck.correct : spec.Correct K` with nothing but `propext`,
//! `Quot.sound` and `Classical.choice` in its axioms. Anything else is
//! refuted (a counterexample the Lean kernel replayed), unsupported (outside
//! the subset or the class), unknown (no proof and no replayed
//! counterexample, a timeout, the memory cap), or an error.

pub mod accum;
pub mod block;
pub mod blocksearch;
pub mod leangen;
pub mod search;
pub mod spec;
pub mod supplied;

use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

pub const RESULT_SCHEMA: &str = "e5r.ptx.result.v1";
pub use crate::core::proof::{ALLOWED_AXIOMS, axioms_allowed, axioms_of};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Proved,
    Refuted,
    Unsupported,
    Unknown,
    Error,
}

impl Verdict {
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Proved => "proved",
            Verdict::Refuted => "refuted",
            Verdict::Unsupported => "unsupported",
            Verdict::Unknown => "unknown",
            Verdict::Error => "error",
        }
    }
    /// The documented exit status.
    pub fn exit_code(self) -> i32 {
        match self {
            Verdict::Proved => 0,
            Verdict::Refuted => 1,
            Verdict::Unsupported => 2,
            Verdict::Unknown => 3,
            Verdict::Error => 4,
        }
    }
}

/// Exit status for a command line that could not be understood.
pub const EXIT_USAGE: i32 = 64;

pub struct Options {
    pub ptx: PathBuf,
    pub spec: PathBuf,
    pub project: PathBuf,
    pub keep: Option<PathBuf>,
    pub timeout: Duration,
    pub memory_mb: u64,
    pub search: bool,
    /// A supplied Lean proof (`--proof`), checked instead of generating one.
    pub proof: Option<PathBuf>,
}

/// One run of Lean on one file, with the time and memory caps.
pub struct LeanRun {
    pub ok: bool,
    pub axioms: Option<Vec<String>>,
    pub output: String,
    pub seconds: f64,
    pub limit: Option<&'static str>,
    pub execution: Value,
}

/// Run Lake under the shared process-group time, sampled RSS and output limits.
pub fn run_lean(project: &Path, args: &[&str], timeout: Duration, memory_mb: u64) -> LeanRun {
    run_lean_env(project, args, timeout, memory_mb, &[])
}

pub fn run_lean_env(
    project: &Path,
    args: &[&str],
    timeout: Duration,
    memory_mb: u64,
    env: &[(&str, &str)],
) -> LeanRun {
    use crate::core::process::{self, Exhaustion, Limits};
    let mut cmd = Command::new("lake");
    cmd.current_dir(project)
        .args(args)
        .env("LEAN_NUM_THREADS", "1")
        .envs(env.iter().copied());
    match process::run(cmd, Limits::new(timeout, memory_mb)) {
        Err(e) => LeanRun {
            ok: false,
            axioms: None,
            output: e.clone(),
            seconds: 0.0,
            limit: None,
            execution: json!({"error": e}),
        },
        Ok(r) => LeanRun {
            execution: json!({"success": r.success, "cancelled": r.cancelled, "cleanup_complete": r.cleanup_complete, "code": r.code, "exhaustion": r.exhaustion, "seconds": r.seconds, "peak_rss_mib": r.peak_rss_mib, "memory_monitor": r.memory_monitor}),
            ok: r.success
                && !r.output.contains("error:")
                && !r.output.contains("declaration uses `sorry`")
                && !r.output.contains("declaration uses 'sorry'"),
            axioms: axioms_of(&r.output),
            output: r.output,
            seconds: r.seconds,
            limit: r.exhaustion.map(|e| match e {
                Exhaustion::Time => "timeout",
                Exhaustion::Memory => "memory",
                Exhaustion::Output => "output",
            }),
        },
    }
}

/// Generated modules have tool-owned propositions; preserve their transitive
/// axiom report and independently replay every declaration before acceptance.
fn run_generated(o: &Options, project: &Path, file: &Path) -> LeanRun {
    let dependencies = crate::core::artifact::compiled_dependencies(project);
    let compiled = file.with_extension("olean");
    let _ = std::fs::remove_file(&compiled);
    let mut r = run_lean(
        project,
        &[
            "env",
            "lean",
            "--root",
            &file.parent().unwrap().display().to_string(),
            "-o",
            &compiled.display().to_string(),
            &file.display().to_string(),
        ],
        o.timeout,
        o.memory_mb,
    );
    if !r.ok {
        return r;
    }
    let Some(dir) = file.parent().and_then(|p| p.canonicalize().ok()) else {
        r.ok = false;
        r.output.push_str("\nerror: invalid proof directory");
        return r;
    };
    let module = file.file_stem().unwrap().to_string_lossy();
    match crate::core::proof::replay(
        project,
        crate::core::proof::SearchPath::Lake(&dir),
        &module,
        crate::core::process::Limits::new(o.timeout, o.memory_mb),
    ) {
        Err(e) => {
            r.ok = false;
            r.output.push_str(&format!("\nerror: replay: {e}"));
        }
        Ok(replay) => {
            r.execution = json!({"compile": r.execution, "replay": {"success": replay.success, "cancelled": replay.cancelled, "cleanup_complete": replay.cleanup_complete, "exhaustion": replay.exhaustion,
                "seconds": replay.seconds, "peak_rss_mib": replay.peak_rss_mib, "memory_monitor": replay.memory_monitor}});
            r.seconds += replay.seconds;
            r.ok &= replay.success && replay.exhaustion.is_none();
            if replay.exhaustion.is_some() {
                r.limit = Some("kernel replay resource limit");
            }
            r.output.push_str(&replay.output);
        }
    }
    match dependencies {
        Ok(dependencies)
            if crate::core::artifact::compiled_dependencies(project)
                .ok()
                .as_ref()
                == Some(&dependencies) =>
        {
            r.execution["dependencies"] = serde_json::to_value(dependencies).unwrap();
        }
        _ => {
            r.ok = false;
            r.output
                .push_str("\nerror: compiled model dependencies changed during proof acceptance");
        }
    }
    r
}

fn sha(path: &Path) -> Result<(Vec<u8>, String), String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let h = crate::sha256::hex(&b);
    Ok((b, h))
}

fn toolchain(project: &Path) -> String {
    std::fs::read_to_string(project.join("lean-toolchain"))
        .unwrap_or_default()
        .trim()
        .to_string()
}

fn props(v: &str) -> Value {
    json!({"memory_safety": v, "termination": v, "race_freedom": v, "functional_correctness": v})
}

/// Run a whole check and return the `e5r.ptx.result.v1` document.
pub fn check(o: &Options) -> (Verdict, Value) {
    // Capture before reading the program/spec, then compare after acceptance.
    // Lake manifests are build metadata; source inventory excludes them below.
    let _lock = match crate::core::workspace::ProjectLock::acquire(&o.project) {
        Ok(lock) => lock,
        Err(e) => {
            return (
                Verdict::Error,
                json!({"schema": RESULT_SCHEMA, "verdict": "error", "reasons": [e], "properties": props("unknown")}),
            );
        }
    };
    let before = crate::verification::ptx_identity(o);
    let (mut verdict, mut doc) = check_backend(o);
    if crate::core::process::cancellation_requested() {
        doc["verdict"] = json!("error");
        doc["properties"] = props("unknown");
        reason(&mut doc, "verification cancelled".into());
        return (Verdict::Error, doc);
    }
    if let Ok(identity) = before {
        match identity.stale(&o.project) {
            Ok(changed) if changed.is_empty() => {
                if let Err(e) = crate::verification::attach_ptx(&mut doc, o, identity) {
                    verdict = Verdict::Error;
                    reason(&mut doc, format!("provenance: {e}"));
                }
            }
            other => {
                verdict = Verdict::Error;
                reason(
                    &mut doc,
                    format!("inputs changed or unavailable during check: {other:?}"),
                );
            }
        }
    } else if matches!(verdict, Verdict::Proved | Verdict::Refuted) {
        verdict = Verdict::Error;
        reason(&mut doc, "cannot establish input provenance".into());
    }
    doc["verdict"] = json!(verdict.name());
    if verdict == Verdict::Error {
        doc["properties"] = props("unknown");
    }
    (verdict, doc)
}

fn check_backend(o: &Options) -> (Verdict, Value) {
    let started = Instant::now();
    let mut doc = json!({
        "schema": RESULT_SCHEMA,
        "tool": {"name": "e5r", "version": env!("CARGO_PKG_VERSION")},
        "input": {"ptx": {"path": o.ptx.display().to_string()}, "spec": {"path": o.spec.display().to_string()}},
        "kernel": Value::Null,
        "class": "map32",
        "verdict": Value::Null,
        "properties": props("unknown"),
        "theorem": Value::Null,
        "counterexample": Value::Null,
        "reasons": [],
        "lean": {"toolchain": toolchain(&o.project), "memory_cap_mb": o.memory_mb,
                 "timeout_seconds": o.timeout.as_secs()},
    });
    let finish = |mut doc: Value, v: Verdict, reason: Option<String>| {
        doc["verdict"] = json!(v.name());
        if let Some(r) = reason {
            doc["reasons"].as_array_mut().unwrap().push(json!(r));
        }
        match v {
            Verdict::Proved => doc["properties"] = props("proved"),
            Verdict::Unsupported => doc["properties"] = props("unsupported"),
            _ => {}
        }
        doc["seconds"] = json!((started.elapsed().as_secs_f64() * 100.0).round() / 100.0);
        (v, doc)
    };
    let (pbytes, phash) = match sha(&o.ptx) {
        Ok(x) => x,
        Err(e) => return finish(doc, Verdict::Error, Some(e)),
    };
    let (sbytes, shash) = match sha(&o.spec) {
        Ok(x) => x,
        Err(e) => return finish(doc, Verdict::Error, Some(e)),
    };
    doc["input"]["ptx"]["sha256"] = json!(phash);
    doc["input"]["spec"]["sha256"] = json!(shash);
    let src = match String::from_utf8(pbytes) {
        Ok(s) => s,
        Err(_) => return finish(doc, Verdict::Unsupported, Some("PTX is not UTF-8".into())),
    };
    let module = match e5r_ptx::roundtrip(&src) {
        Ok(m) => m,
        Err(e) => {
            return finish(
                doc,
                Verdict::Unsupported,
                Some(format!("PTX outside the subset: {e}")),
            );
        }
    };
    let stext = match String::from_utf8(sbytes) {
        Ok(t) => t,
        Err(e) => return finish(doc, Verdict::Error, Some(format!("spec malformed: {e}"))),
    };
    if let Some(class) = block_class(&stext) {
        return check_block(o, doc, started, &module, &stext, &class, &phash, &shash);
    }
    let sp = match Ok::<String, String>(stext).and_then(|t| {
        spec::parse(&t).map_err(|e| match e {
            spec::SpecError::Malformed(m) => format!("malformed: {m}"),
            spec::SpecError::Unsupported(m) => format!("unsupported: {m}"),
        })
    }) {
        Ok(s) => s,
        Err(e) if e.starts_with("unsupported: ") => {
            return finish(doc, Verdict::Unsupported, Some(e[13..].to_string()));
        }
        Err(e) => return finish(doc, Verdict::Error, Some(format!("spec {e}"))),
    };
    doc["kernel"] = json!(sp.kernel);
    doc["spec"] = json!({"element": sp.element_text, "output": sp.output, "arrays": sp.arrays,
    "schedule": match &sp.sched {
        spec::Sched::Guarded { max_threads } => json!({"kind": "guarded", "max_threads": max_threads.to_string()}),
        spec::Sched::Stride { bound, head, .. } => json!({"kind": "stride", "bound": bound.to_string(), "head": head}),
    }});
    let Some(k) = module.kernels.iter().find(|k| k.name == sp.kernel) else {
        return finish(
            doc,
            Verdict::Error,
            Some(format!("no kernel {} in the PTX", sp.kernel)),
        );
    };
    if let Err(e) = spec::validate(&sp, k) {
        return finish(doc, Verdict::Unsupported, Some(e));
    }
    let header = format!(
        "Generated by `e5r ptx check` from {} (sha256 {phash})\nand {} (sha256 {shash}).",
        o.ptx.display(),
        o.spec.display()
    );
    let workspace = match crate::core::workspace::Workspace::new(o.keep.as_deref()) {
        Ok(w) => w,
        Err(e) => return finish(doc, Verdict::Error, Some(e)),
    };
    let dir = workspace.path().to_path_buf();
    let proj = match o.project.canonicalize() {
        Ok(p) => p,
        Err(e) => {
            return finish(
                doc,
                Verdict::Error,
                Some(format!("{}: {e}", o.project.display())),
            );
        }
    };
    let warm = run_lean(
        &proj,
        &["build", "-q", "Ptx.Auto.FloatMap", "Ptx.Logic.Refute"],
        o.timeout * 4,
        o.memory_mb,
    );
    doc["lean"]["build_execution"] = warm.execution.clone();
    if !warm.ok {
        return finish(
            doc,
            Verdict::Error,
            Some(format!(
                "building the Lean library failed: {}",
                tail(&warm.output)
            )),
        );
    }
    if let Some(pf) = &o.proof {
        let pre = leangen::prelude(k, &sp, &header, "")
            .replace("namespace E5rCheck", "namespace E5rSpec");
        let stmt = format!("spec.Correct {}", leangen::kname(k));
        let module = supplied::statement_module(&pre, &stmt);
        let (v, why) = supplied_route(
            o,
            &mut doc,
            pf,
            &module,
            &stmt,
            "Ptx.Auto.MapSpec.Correct",
            &phash,
            &shash,
            &proj,
            &dir,
        );
        return finish(doc, v, why);
    }
    let proof = dir.join("Proof.lean");
    let text = leangen::proof(k, &sp, &header);
    // What the theorem is about, as Lean reads it: the reviewer checks this
    // against the JSON spec (the translation is part of the trusted base).
    if let (Some(i), Some(j)) = (
        text.find("def spec : MapSpec where"),
        text.find("@[ptx_spec]"),
    ) {
        doc["lean_spec"] = json!(text[i..j].trim_end());
    }
    if let (Some(i), Some(j)) = (
        text.find("def loop : Loop where"),
        text.find("@[ptx_spec] theorem loop_head"),
    ) {
        doc["lean_loop"] = json!(text[i..j].trim_end());
    }
    if let Err(e) = std::fs::write(&proof, &text) {
        return finish(doc, Verdict::Error, Some(e.to_string()));
    }
    let pf = proof.display().to_string();
    let r = run_generated(o, &proj, &proof);
    doc["lean"]["proof_execution"] = r.execution.clone();
    doc["lean"]["proof_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
    if o.keep.is_some() {
        doc["lean"]["proof_file"] = json!(pf);
    }
    if r.ok {
        match &r.axioms {
            Some(ax) if axioms_allowed(ax) => {
                doc["theorem"] = json!({"name": "E5rCheck.correct",
                    "statement": format!("spec.Correct {}", leangen::kname(k)),
                    "definition": "Ptx.Auto.MapSpec.Correct", "axioms": ax});
                return finish(doc, Verdict::Proved, None);
            }
            Some(ax) => {
                doc["reasons"].as_array_mut().unwrap().push(json!(format!(
                    "proof uses axioms outside the allowed set: {ax:?}"
                )));
            }
            None => {
                doc["reasons"]
                    .as_array_mut()
                    .unwrap()
                    .push(json!("no axiom report for the theorem"));
            }
        }
    } else if let Some(l) = r.limit {
        doc["reasons"]
            .as_array_mut()
            .unwrap()
            .push(json!(format!("proof attempt stopped: {l}")));
    } else {
        doc["reasons"].as_array_mut().unwrap().push(json!(format!(
            "proof did not check: {}",
            first_error(&r.output)
        )));
    }
    if !o.search {
        return finish(
            doc,
            Verdict::Unknown,
            Some("counterexample search disabled".into()),
        );
    }
    if crate::core::process::cancellation_requested() {
        return finish(doc, Verdict::Error, Some("verification cancelled".into()));
    }
    let t0 = Instant::now();
    let (found, tried) = search::search(k, &sp);
    doc["search"] =
        json!({"launches": tried, "seconds": (t0.elapsed().as_secs_f64() * 100.0).round() / 100.0});
    let Some((w, wit)) = found else {
        return finish(
            doc,
            Verdict::Unknown,
            Some("no proof, and the search found no counterexample".into()),
        );
    };
    let mut cx = search::describe(&w, &wit);
    let rf = dir.join("Refute.lean");
    let text = leangen::refutation(k, &sp, &header, &w, &wit);
    if let Err(e) = std::fs::write(&rf, &text) {
        return finish(doc, Verdict::Error, Some(e.to_string()));
    }
    let rfs = rf.display().to_string();
    let r = run_generated(o, &proj, &rf);
    doc["lean"]["refutation_execution"] = r.execution.clone();
    doc["lean"]["refutation_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
    if o.keep.is_some() {
        doc["lean"]["refutation_file"] = json!(rfs);
    }
    let replayed = r.ok && r.axioms.as_deref().is_some_and(axioms_allowed);
    cx["replayed_in_lean"] = json!(replayed);
    if replayed {
        cx["theorem"] = json!({"name": "E5rCheck.refuted",
            "statement": format!("¬ spec.Correct {}", leangen::kname(k)), "axioms": r.axioms});
    } else {
        cx["replay_error"] = json!(first_error(&r.output));
    }
    let prop = match wit.kind() {
        "fault" => "memory_safety",
        "race" => "race_freedom",
        _ => "functional_correctness",
    };
    doc["counterexample"] = cx;
    if replayed {
        doc["properties"][prop] = json!("refuted");
        finish(doc, Verdict::Refuted, None)
    } else {
        finish(
            doc,
            Verdict::Unknown,
            Some("the search found a candidate counterexample, but Lean did not replay it".into()),
        )
    }
}

/// The class of a block-class spec, when the text is one.
fn block_class(text: &str) -> Option<String> {
    let v: Value = serde_json::from_str(text).ok()?;
    if v.get("schema")?.as_str()? != spec::SCHEMA {
        return None;
    }
    let c = v.get("class")?.as_str()?;
    matches!(c, "reduce32" | "scan32" | "accum").then(|| c.to_string())
}

fn finish_at(
    started: Instant,
    mut doc: Value,
    v: Verdict,
    reason: Option<String>,
) -> (Verdict, Value) {
    doc["verdict"] = json!(v.name());
    if let Some(r) = reason {
        doc["reasons"].as_array_mut().unwrap().push(json!(r));
    }
    match v {
        Verdict::Proved => doc["properties"] = props("proved"),
        Verdict::Unsupported => doc["properties"] = props("unsupported"),
        _ => {}
    }
    doc["seconds"] = json!((started.elapsed().as_secs_f64() * 100.0).round() / 100.0);
    (v, doc)
}

fn reason(doc: &mut Value, r: String) {
    doc["reasons"].as_array_mut().unwrap().push(json!(r));
}

/// A search result: the candidate counterexample's description, kind and
/// refutation file (if any), and the number of worlds tried.
type Search = (Option<(Value, &'static str, String)>, usize);

/// What a class contributes to a check: the statement, the proof attempt
/// (or why there is none), and the search with its refutation.
struct Plan {
    statement: String,
    definition: &'static str,
    statement_module: String,
    warm: Vec<&'static str>,
    proof: Result<String, String>,
    search: Box<dyn FnOnce() -> Search>,
}

/// `check` for the M4 classes (`reduce32`, `scan32`) and `accum`
/// (docs/verification/ptx.md): the class theorem with the generated phase
/// obligations, and otherwise the barrier-aware search with a replay in Lean.
#[allow(clippy::too_many_arguments)]
fn check_block(
    o: &Options,
    mut doc: Value,
    started: Instant,
    module: &e5r_ptx::ast::Module,
    text: &str,
    class: &str,
    phash: &str,
    shash: &str,
) -> (Verdict, Value) {
    let finish = |doc, v, r| finish_at(started, doc, v, r);
    doc["class"] = json!(class);
    let v: Value = serde_json::from_str(text).unwrap_or(Value::Null);
    let header = format!(
        "Generated by `e5r ptx check` from {} (sha256 {phash})\nand {} (sha256 {shash}).",
        o.ptx.display(),
        o.spec.display()
    );
    let bad = |e: spec::SpecError| match e {
        spec::SpecError::Malformed(m) => (Verdict::Error, format!("spec malformed: {m}")),
        spec::SpecError::Unsupported(m) => (Verdict::Unsupported, m),
    };
    let kernel_named = |name: &str| module.kernels.iter().find(|k| k.name == name).cloned();
    let plan = if class == "accum" {
        let sp = match accum::parse(&v) {
            Ok(s) => s,
            Err(e) => {
                let (vd, r) = bad(e);
                return finish(doc, vd, Some(r));
            }
        };
        doc["kernel"] = json!(sp.kernel);
        doc["spec"] = json!({"op": sp.op, "type": sp.ty, "algebra": sp.alg, "input": sp.input,
            "output": sp.output, "length": sp.length});
        doc["lean_spec"] = json!(accum::lean_spec(&sp));
        let Some(k) = kernel_named(&sp.kernel) else {
            return finish(
                doc,
                Verdict::Error,
                Some(format!("no kernel {} in the PTX", sp.kernel)),
            );
        };
        if let Err(e) = accum::validate(&sp, &k) {
            return finish(doc, Verdict::Unsupported, Some(e));
        }
        let (k2, sp2, h2) = (k.clone(), sp.clone(), header.clone());
        Plan {
            statement: format!("Accum.Correct spec «{}»", k.name),
            definition: "Ptx.Auto.Accum.Correct",
            statement_module: supplied::statement_module(
                &accum::statement_prelude(&k, &sp, &header),
                &format!("Accum.Correct spec «{}»", k.name),
            ),
            warm: vec!["Ptx.Auto.Accum", "Ptx.Logic.Schedule"],
            proof: accum::shape(&sp, &k).map(|()| accum::proof(&k, &sp, &header)),
            search: Box::new(move || {
                let (found, tried) = accum::search(&k2, &sp2);
                (
                    found.map(|(w, wit)| {
                        (
                            accum::describe(&w, &wit),
                            wit.kind(),
                            accum::refutation(&k2, &sp2, &h2, &w, &wit),
                        )
                    }),
                    tried,
                )
            }),
        }
    } else {
        let sp = match block::parse(&v, class) {
            Ok(s) => s,
            Err(e) => {
                let (vd, r) = bad(e);
                return finish(doc, vd, Some(r));
            }
        };
        doc["kernel"] = json!(sp.kernel);
        doc["spec"] = json!({
            "result": match sp.class { block::Class::Reduce => "per_block",
                                       block::Class::ReduceAtomic => "atomic",
                                       block::Class::Scan => "inclusive_scan" },
            "input": sp.input, "output": sp.output, "length": sp.length, "shared": sp.shared,
            "max_block": sp.max_block});
        doc["lean_spec"] = json!(block::lean_spec(&sp));
        let Some(k) = kernel_named(&sp.kernel) else {
            return finish(
                doc,
                Verdict::Error,
                Some(format!("no kernel {} in the PTX", sp.kernel)),
            );
        };
        if let Err(e) = block::validate(&sp, &k) {
            return finish(doc, Verdict::Unsupported, Some(e));
        }
        let statement = format!(
            "{} spec «{}»",
            sp.class.definition().trim_start_matches("Ptx.Auto."),
            k.name
        );
        let (k2, sp2, h2) = (k.clone(), sp.clone(), header.clone());
        Plan {
            statement_module: supplied::statement_module(
                &block::statement_prelude(&k, &sp, &header),
                &statement,
            ),
            statement,
            definition: sp.class.definition(),
            warm: vec!["Ptx.Auto.Reduce32", "Ptx.Auto.Scan32", "Ptx.Logic.Schedule"],
            proof: block::shape(&sp, &k).map(|sh| block::proof(&k, &sp, &sh, &header)),
            search: Box::new(move || {
                let (found, tried) = blocksearch::search(&k2, &sp2);
                (
                    found.map(|(w, wit)| {
                        (
                            blocksearch::describe(&w, &wit),
                            wit.kind(),
                            blocksearch::refutation(&k2, &sp2, &h2, &w, &wit),
                        )
                    }),
                    tried,
                )
            }),
        }
    };
    let workspace = match crate::core::workspace::Workspace::new(o.keep.as_deref()) {
        Ok(w) => w,
        Err(e) => return finish(doc, Verdict::Error, Some(e)),
    };
    let dir = workspace.path().to_path_buf();
    let proj = match o.project.canonicalize() {
        Ok(p) => p,
        Err(e) => {
            return finish(
                doc,
                Verdict::Error,
                Some(format!("{}: {e}", o.project.display())),
            );
        }
    };
    if let Some(pf) = &o.proof {
        let (v, why) = supplied_route(
            o,
            &mut doc,
            pf,
            &plan.statement_module,
            &plan.statement,
            plan.definition,
            phash,
            shash,
            &proj,
            &dir,
        );
        return finish(doc, v, why);
    }
    let mut warm_args = vec!["build", "-q"];
    warm_args.extend(plan.warm.iter().copied());
    let warm = run_lean(&proj, &warm_args, o.timeout * 4, o.memory_mb);
    doc["lean"]["build_execution"] = warm.execution.clone();
    if !warm.ok {
        return finish(
            doc,
            Verdict::Error,
            Some(format!(
                "building the Lean library failed: {}",
                tail(&warm.output)
            )),
        );
    }
    let statement = plan.statement.clone();
    match &plan.proof {
        Err(e) => reason(&mut doc, format!("no proof attempt: {e}")),
        Ok(text) => {
            let proof = dir.join("Proof.lean");
            if let Err(e) = std::fs::write(&proof, text) {
                return finish(doc, Verdict::Error, Some(e.to_string()));
            }
            let pf = proof.display().to_string();
            let r = run_generated(o, &proj, &proof);
            doc["lean"]["proof_execution"] = r.execution.clone();
            doc["lean"]["proof_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
            if o.keep.is_some() {
                doc["lean"]["proof_file"] = json!(pf);
            }
            if r.ok {
                match &r.axioms {
                    Some(ax) if axioms_allowed(ax) => {
                        doc["theorem"] = json!({"name": "E5rCheck.correct", "statement": statement,
                            "definition": plan.definition, "axioms": ax});
                        return finish(doc, Verdict::Proved, None);
                    }
                    Some(ax) => reason(
                        &mut doc,
                        format!("proof uses axioms outside the allowed set: {ax:?}"),
                    ),
                    None => reason(&mut doc, "no axiom report for the theorem".into()),
                }
            } else if let Some(l) = r.limit {
                reason(&mut doc, format!("proof attempt stopped: {l}"));
            } else {
                reason(
                    &mut doc,
                    format!("proof did not check: {}", first_error(&r.output)),
                );
            }
        }
    }
    // Outside the proof's shape, a kernel can still be refuted, but no
    // counterexample does not make it unknown: the class cannot prove it.
    let none = if plan.proof.is_err() {
        Verdict::Unsupported
    } else {
        Verdict::Unknown
    };
    if !o.search {
        return finish(doc, none, Some("counterexample search disabled".into()));
    }
    if crate::core::process::cancellation_requested() {
        return finish(doc, Verdict::Error, Some("verification cancelled".into()));
    }
    let t0 = Instant::now();
    let (found, tried) = (plan.search)();
    doc["search"] =
        json!({"launches": tried, "seconds": (t0.elapsed().as_secs_f64() * 100.0).round() / 100.0});
    let Some((mut cx, kind, rtext)) = found else {
        return finish(
            doc,
            none,
            Some("no proof, and the search found no counterexample".into()),
        );
    };
    let rf = dir.join("Refute.lean");
    if let Err(e) = std::fs::write(&rf, rtext) {
        return finish(doc, Verdict::Error, Some(e.to_string()));
    }
    let rfs = rf.display().to_string();
    let r = run_generated(o, &proj, &rf);
    doc["lean"]["refutation_execution"] = r.execution.clone();
    doc["lean"]["refutation_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
    if o.keep.is_some() {
        doc["lean"]["refutation_file"] = json!(rfs);
    }
    let replayed = r.ok && r.axioms.as_deref().is_some_and(axioms_allowed);
    cx["replayed_in_lean"] = json!(replayed);
    if replayed {
        cx["theorem"] = json!({"name": "E5rCheck.refuted", "statement": format!("¬ {statement}"),
            "axioms": r.axioms});
    } else {
        cx["replay_error"] = json!(
            r.limit
                .map(|l| l.to_string())
                .unwrap_or_else(|| first_error(&r.output))
        );
    }
    let prop = match kind {
        "fault" => "memory_safety",
        "race" => "race_freedom",
        _ => "functional_correctness",
    };
    doc["counterexample"] = cx;
    if replayed {
        doc["properties"][prop] = json!("refuted");
        finish(doc, Verdict::Refuted, None)
    } else {
        finish(
            doc,
            none,
            Some("the search found a candidate counterexample, but Lean did not replay it".into()),
        )
    }
}

/// Build what a supplied proof needs (the whole library and the checker),
/// then check the proof.
#[allow(clippy::too_many_arguments)]
fn supplied_route(
    o: &Options,
    doc: &mut Value,
    pf: &Path,
    module: &str,
    statement: &str,
    definition: &str,
    phash: &str,
    shash: &str,
    proj: &Path,
    dir: &Path,
) -> (Verdict, Option<String>) {
    let warm = run_lean(
        proj,
        &["build", "-q", "Ptx", "proofcheck"],
        o.timeout * 6,
        o.memory_mb,
    );
    doc["lean"]["build_execution"] = warm.execution.clone();
    if !warm.ok {
        return (
            Verdict::Error,
            Some(format!(
                "building the Lean library failed: {}",
                tail(&warm.output)
            )),
        );
    }
    let tc = toolchain(proj);
    supplied::check(
        o, doc, pf, module, statement, definition, phash, shash, &tc, proj, dir,
    )
}

fn tail(s: &str) -> String {
    let t: Vec<&str> = s.lines().rev().take(6).collect();
    t.into_iter().rev().collect::<Vec<_>>().join(" | ")
}

fn first_error(s: &str) -> String {
    match s.find("error:") {
        Some(i) => s[i..]
            .lines()
            .take(3)
            .collect::<Vec<_>>()
            .join(" ")
            .chars()
            .take(400)
            .collect(),
        None => tail(s),
    }
}
