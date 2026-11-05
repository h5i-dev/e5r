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
pub mod equivalence;
pub mod leangen;
pub mod packing;
pub mod search;
pub mod spec;
pub mod supplied;

use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

pub const RESULT_SCHEMA: &str = "e5r.ptx.result.v1";
pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

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
}

fn have_systemd_run() -> bool {
    Command::new("systemd-run")
        .args(["--scope", "--quiet", "-p", "MemoryMax=64M", "true"])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

/// `lake env lean FILE` in `project`, one Lean thread, under a cgroup memory
/// cap when systemd is available (Lean's own `--memory` otherwise) and a
/// wall-clock timeout.
pub fn run_lean(project: &Path, args: &[&str], timeout: Duration, memory_mb: u64) -> LeanRun {
    run_lean_env(project, args, timeout, memory_mb, &[])
}

/// `run_lean` with extra environment variables.
pub fn run_lean_env(
    project: &Path,
    args: &[&str],
    timeout: Duration,
    memory_mb: u64,
    env: &[(&str, &str)],
) -> LeanRun {
    let start = Instant::now();
    let mut cmd = if have_systemd_run() {
        let mut c = Command::new("systemd-run");
        c.args(["--scope", "--quiet", "-p"])
            .arg(format!("MemoryMax={memory_mb}M"))
            .args(["-p", "MemorySwapMax=0", "--", "lake"]);
        c
    } else {
        Command::new("lake")
    };
    cmd.current_dir(project)
        .args(args)
        .env("LEAN_NUM_THREADS", "1")
        .envs(env.iter().copied())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return LeanRun {
                ok: false,
                axioms: None,
                output: format!("cannot run lake: {e}"),
                seconds: 0.0,
                limit: Some("lake missing"),
            };
        }
    };
    let (mut out, mut err) = (child.stdout.take().unwrap(), child.stderr.take().unwrap());
    let ro = std::thread::spawn(move || {
        let mut s = String::new();
        std::io::Read::read_to_string(&mut out, &mut s).ok();
        s
    });
    let re = std::thread::spawn(move || {
        let mut s = String::new();
        std::io::Read::read_to_string(&mut err, &mut s).ok();
        s
    });
    let mut limit = None;
    let status = loop {
        if let Ok(Some(s)) = child.try_wait() {
            break Some(s);
        }
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            limit = Some("timeout");
            break None;
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    let output = ro.join().unwrap_or_default() + &re.join().unwrap_or_default();
    let killed = status.as_ref().is_some_and(|s| {
        use std::os::unix::process::ExitStatusExt;
        s.signal() == Some(9) || s.code() == Some(137)
    });
    if killed {
        limit = Some("memory");
    }
    let clean = status.is_some_and(|s| s.success())
        && !output.contains("error:")
        && !output.contains("declaration uses `sorry`")
        && !output.contains("declaration uses 'sorry'");
    LeanRun {
        ok: clean,
        axioms: axioms_of(&output),
        output,
        seconds: start.elapsed().as_secs_f64(),
        limit,
    }
}

/// The axiom list of the one `#print axioms` in the output.
pub fn axioms_of(out: &str) -> Option<Vec<String>> {
    let flat = out.replace('\n', " ");
    if flat.contains("does not depend on any axioms") {
        return Some(Vec::new());
    }
    let i = flat.find("depends on axioms: [")? + "depends on axioms: [".len();
    let j = flat[i..].find(']')? + i;
    Some(
        flat[i..j]
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect(),
    )
}

fn axioms_allowed(ax: &[String]) -> bool {
    ax.iter().all(|a| ALLOWED_AXIOMS.contains(&a.as_str()))
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
    if serde_json::from_str::<Value>(&stext)
        .ok()
        .is_some_and(|v| v["class"] == "packing")
    {
        return packing::check(o, doc, started, &module, &stext, &phash, &shash);
    }
    if serde_json::from_str::<Value>(&stext).ok().is_some_and(|v| {
        matches!(
            v["class"].as_str(),
            Some("equivalence-unpack4" | "equivalence-stencil17")
        )
    }) {
        return equivalence::check(o, doc, started, &module, &stext, &phash, &shash);
    }
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
    let dir = match &o.keep {
        Some(d) => d.clone(),
        None => {
            std::env::temp_dir().join(format!("e5r-ptx-{}-{}", std::process::id(), &phash[..12]))
        }
    };
    if let Err(e) = std::fs::create_dir_all(&dir) {
        return finish(doc, Verdict::Error, Some(format!("{}: {e}", dir.display())));
    }
    let cleanup = |d: &Path| {
        if o.keep.is_none() {
            let _ = std::fs::remove_dir_all(d);
        }
    };
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
        &["build", "-q", "Ptx.Auto.Tactic", "Ptx.Logic.Refute"],
        o.timeout * 4,
        o.memory_mb,
    );
    if !warm.ok {
        cleanup(&dir);
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
        cleanup(&dir);
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
    let r = run_lean(&proj, &["env", "lean", &pf], o.timeout, o.memory_mb);
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
                cleanup(&dir);
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
        cleanup(&dir);
        return finish(
            doc,
            Verdict::Unknown,
            Some("counterexample search disabled".into()),
        );
    }
    let t0 = Instant::now();
    let (found, tried) = search::search(k, &sp);
    doc["search"] =
        json!({"launches": tried, "seconds": (t0.elapsed().as_secs_f64() * 100.0).round() / 100.0});
    let Some((w, wit)) = found else {
        cleanup(&dir);
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
    let r = run_lean(&proj, &["env", "lean", &rfs], o.timeout, o.memory_mb);
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
    cleanup(&dir);
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
    let dir = match &o.keep {
        Some(d) => d.clone(),
        None => {
            std::env::temp_dir().join(format!("e5r-ptx-{}-{}", std::process::id(), &phash[..12]))
        }
    };
    if let Err(e) = std::fs::create_dir_all(&dir) {
        return finish(doc, Verdict::Error, Some(format!("{}: {e}", dir.display())));
    }
    let cleanup = |d: &Path| {
        if o.keep.is_none() {
            let _ = std::fs::remove_dir_all(d);
        }
    };
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
        cleanup(&dir);
        return finish(doc, v, why);
    }
    let mut warm_args = vec!["build", "-q"];
    warm_args.extend(plan.warm.iter().copied());
    let warm = run_lean(&proj, &warm_args, o.timeout * 4, o.memory_mb);
    if !warm.ok {
        cleanup(&dir);
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
            let r = run_lean(&proj, &["env", "lean", &pf], o.timeout, o.memory_mb);
            doc["lean"]["proof_seconds"] = json!((r.seconds * 100.0).round() / 100.0);
            if o.keep.is_some() {
                doc["lean"]["proof_file"] = json!(pf);
            }
            if r.ok {
                match &r.axioms {
                    Some(ax) if axioms_allowed(ax) => {
                        doc["theorem"] = json!({"name": "E5rCheck.correct", "statement": statement,
                            "definition": plan.definition, "axioms": ax});
                        cleanup(&dir);
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
        cleanup(&dir);
        return finish(doc, none, Some("counterexample search disabled".into()));
    }
    let t0 = Instant::now();
    let (found, tried) = (plan.search)();
    doc["search"] =
        json!({"launches": tried, "seconds": (t0.elapsed().as_secs_f64() * 100.0).round() / 100.0});
    let Some((mut cx, kind, rtext)) = found else {
        cleanup(&dir);
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
    let r = run_lean(&proj, &["env", "lean", &rfs], o.timeout, o.memory_mb);
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
    cleanup(&dir);
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
