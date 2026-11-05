//! Backend adapters for the common evidence/replay API. Core services never
//! depend on this dispatch layer. Legacy result fields and exit codes remain.
use crate::core::artifact::{Binding, Evidence, Identity, Outcome, Request};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Invocation {
    Firmware {
        job: PathBuf,
        resume: bool,
    },
    Ptx {
        program: PathBuf,
        spec: PathBuf,
        project: PathBuf,
        proof: Option<PathBuf>,
        timeout_seconds: u64,
        memory_mib: u64,
        search: bool,
    },
}
impl Invocation {
    pub fn project(&self) -> Result<PathBuf, String> {
        match self {
            Self::Firmware { job, .. } => crate::job::Job::load(job)
                .map(|(_, p)| p.root)
                .map_err(|s| s.message().into()),
            Self::Ptx { project, .. } => Ok(project.clone()),
        }
    }
    pub fn execute(&self) -> Result<Value, String> {
        match self {
            Self::Firmware { job, resume } => Ok(crate::job::run(job, *resume)),
            Self::Ptx {
                program,
                spec,
                project,
                proof,
                timeout_seconds,
                memory_mib,
                search,
            } => {
                let (_, doc) = crate::ptx::check(&crate::ptx::Options {
                    ptx: program.clone(),
                    spec: spec.clone(),
                    project: project.clone(),
                    proof: proof.clone(),
                    keep: None,
                    timeout: Duration::from_secs(*timeout_seconds),
                    memory_mb: *memory_mib,
                    search: *search,
                });
                Ok(doc)
            }
        }
    }
}

fn claim(doc: &Value) -> Value {
    json!({"theorems": doc["theorems"], "theorem": doc["theorem"], "counterexample": doc["counterexample"],
        "spec": doc["spec"], "lean_spec": doc["lean_spec"], "lean_loop": doc["lean_loop"], "properties": doc["properties"]})
}
pub fn evidence(doc: &Value) -> Result<Evidence, String> {
    let e: Evidence = serde_json::from_value(doc["verification"].clone())
        .map_err(|e| format!("common verification evidence missing or invalid: {e}"))?;
    e.validate()?;
    if e.claim != claim(doc) {
        return Err("backend claim differs from common evidence".into());
    }
    let invocation: Invocation =
        serde_json::from_value(e.request.invocation.clone()).map_err(|e| e.to_string())?;
    match invocation {
        Invocation::Firmware { job, .. } => {
            if doc["job_file"] != json!(job)
                || doc["inputs"]["common_identity"]
                    != serde_json::to_value(&e.identity).map_err(|e| e.to_string())?
            {
                return Err("firmware legacy inputs differ from common evidence".into());
            }
        }
        Invocation::Ptx {
            program,
            spec,
            proof,
            ..
        } => {
            for (field, path) in [("ptx", program), ("spec", spec)] {
                let identity = e
                    .identity
                    .files
                    .get(&path)
                    .ok_or("request input absent from identity")?;
                if doc["input"][field]["path"] != json!(path)
                    || doc["input"][field]["sha256"] != identity.sha256
                {
                    return Err(format!(
                        "PTX legacy {field} input differs from common evidence"
                    ));
                }
            }
            if let Some(path) = proof {
                let identity = e
                    .identity
                    .files
                    .get(&path)
                    .ok_or("proof absent from identity")?;
                if doc["proof"]["sha256"] != identity.sha256 {
                    return Err("supplied proof differs from common evidence".into());
                }
            }
        }
    }
    Ok(e)
}
pub fn stale(doc: &Value) -> Result<Vec<String>, String> {
    if doc.get("verification").is_none() {
        return crate::job::stale(doc);
    }
    let e = evidence(doc)?;
    let invocation: Invocation =
        serde_json::from_value(e.request.invocation.clone()).map_err(|e| e.to_string())?;
    let mut changed = e.identity.stale(&invocation.project()?)?;
    if matches!(invocation, Invocation::Firmware { .. }) {
        changed.extend(crate::job::stale(doc)?);
    }

    if !matches!(e.outcome, Outcome::Proved | Outcome::Refuted) {
        changed.push(format!("outcome is {:?}", e.outcome));
    }
    // Consistency is not authentication, but malformed adapters must fail closed.
    let legacy = doc["status"]
        .as_str()
        .or(doc["verdict"].as_str())
        .unwrap_or("");
    if outcome(legacy) != e.outcome && e.outcome != Outcome::ResourceExhausted {
        changed.push("legacy/common outcome mismatch".into());
    }
    Ok(changed)
}
fn outcome(name: &str) -> Outcome {
    match name {
        "proved" => Outcome::Proved,
        "refuted" | "counterexample" => Outcome::Refuted,
        "unsupported" => Outcome::Unsupported,
        "resource_exhausted" => Outcome::ResourceExhausted,
        "failed" | "unknown" => Outcome::Inconclusive,
        _ => Outcome::Error,
    }
}
pub fn attach_firmware(doc: &mut Value, job_path: &Path) -> Result<(), String> {
    let (job, paths) = crate::job::Job::load(job_path).map_err(|s| s.message().to_string())?;
    let identity: Identity = serde_json::from_value(doc["inputs"]["common_identity"].clone())
        .map_err(|e| e.to_string())?;
    doc["job_file"] = json!(job_path.canonicalize().map_err(|e| e.to_string())?);
    let request = Request {
        backend: "rv32-firmware.v1".into(),
        architecture: "rv32imac+zicsr+zifencei".into(),
        platform: json!({"board": paths.root.join(&job.board).canonicalize().map_err(|e| e.to_string())?, "image_placement": job.image.kind}),
        invocation: serde_json::to_value(Invocation::Firmware {
            job: job_path.canonicalize().map_err(|e| e.to_string())?,
            resume: false,
        })
        .unwrap(),
    };
    doc["verification"] = serde_json::to_value(Evidence::new(
        request,
        outcome(doc["status"].as_str().unwrap_or("error")),
        Binding::ReviewedTheoremNames,
        identity,
        claim(doc),
    ))
    .unwrap();
    Ok(())
}
pub fn ptx_identity(o: &crate::ptx::Options) -> Result<Identity, String> {
    let mut files = vec![o.ptx.clone(), o.spec.clone()];
    if let Some(p) = &o.proof {
        files.push(p.clone());
    }
    Identity::capture(
        &[o.project.clone(), o.project.join("../common")],
        &files,
        &o.project,
    )
}
pub fn attach_ptx(
    doc: &mut Value,
    o: &crate::ptx::Options,
    mut identity: Identity,
) -> Result<(), String> {
    fn dependencies(v: &Value, identity: &mut Identity) -> Result<(), String> {
        if let Value::Object(o) = v {
            if let Some(d) = o.get("dependencies") {
                let files: std::collections::BTreeMap<
                    PathBuf,
                    crate::core::artifact::FileIdentity,
                > = serde_json::from_value(d.clone()).map_err(|e| e.to_string())?;
                for (p, h) in files {
                    identity.explicit_files.push(p.clone());
                    identity.files.insert(p, h);
                }
            }
            for (k, v) in o {
                if k != "dependencies" {
                    dependencies(v, identity)?;
                }
            }
        }
        Ok(())
    }
    dependencies(&doc["lean"], &mut identity)?;
    let canonical = |p: &Path| p.canonicalize().map_err(|e| e.to_string());
    if let Some(hash) = doc["proof"]["checker_sha256"].as_str() {
        identity.pin_file(
            &canonical(&o.project)?.join(".lake/build/bin/proofcheck"),
            hash,
        )?;
    }
    let invocation = Invocation::Ptx {
        program: canonical(&o.ptx)?,
        spec: canonical(&o.spec)?,
        project: canonical(&o.project)?,
        proof: o.proof.as_deref().map(canonical).transpose()?,
        timeout_seconds: o.timeout.as_secs(),
        memory_mib: o.memory_mb,
        search: o.search,
    };
    if let Invocation::Ptx { program, spec, .. } = &invocation {
        doc["input"]["ptx"]["path"] = json!(program);
        doc["input"]["spec"]["path"] = json!(spec);
    }
    let request = Request {
        backend: "ptx.v1".into(),
        architecture: "ptx".into(),
        platform: json!({"environment": "PTX operational model", "assumptions": doc["spec"]}),
        invocation: serde_json::to_value(invocation).unwrap(),
    };
    let mut result = outcome(doc["verdict"].as_str().unwrap_or("error"));
    fn exhausted(v: &Value) -> bool {
        match v {
            Value::Object(o) => {
                o.get("exhaustion").is_some_and(|e| !e.is_null()) || o.values().any(exhausted)
            }
            Value::Array(a) => a.iter().any(exhausted),
            _ => false,
        }
    }
    if !matches!(result, Outcome::Proved | Outcome::Refuted) && exhausted(&doc["lean"]) {
        result = Outcome::ResourceExhausted;
    }
    doc["verification"] = serde_json::to_value(Evidence::new(
        request,
        result,
        if o.proof.is_some() {
            Binding::ExactGeneratedStatement
        } else {
            Binding::GeneratedClaim
        },
        identity,
        claim(doc),
    ))
    .unwrap();
    Ok(())
}

const BUNDLE_SCHEMA: &str = "e5r.verification.bundle.v1";
#[derive(Serialize, Deserialize)]
struct Bundle {
    schema: String,
    invocation: Invocation,
    outcome: Outcome,
    identity: Identity,
}
fn relative(path: &Path) -> Result<PathBuf, String> {
    if !path.is_absolute() {
        return Err(format!("expected absolute input: {}", path.display()));
    }
    Ok(Path::new("sources").join(path.strip_prefix("/").map_err(|e| e.to_string())?))
}
fn safe_join(root: &Path, path: &Path) -> Result<PathBuf, String> {
    if path.as_os_str().is_empty()
        || path
            .components()
            .any(|c| !matches!(c, std::path::Component::Normal(_)))
    {
        return Err(format!("invalid bundle path: {}", path.display()));
    }
    Ok(root.join(path))
}
fn map_invocation(
    i: &mut Invocation,
    f: impl Fn(&Path) -> Result<PathBuf, String>,
) -> Result<(), String> {
    match i {
        Invocation::Firmware { job, .. } => *job = f(job)?,
        Invocation::Ptx {
            program,
            spec,
            project,
            proof,
            ..
        } => {
            *program = f(program)?;
            *spec = f(spec)?;
            *project = f(project)?;
            if let Some(p) = proof {
                *p = f(p)?;
            }
        }
    }
    Ok(())
}
fn validate_bundle_invocation(invocation: &Invocation, root: &Path) -> Result<(), String> {
    let project = invocation
        .project()?
        .canonicalize()
        .map_err(|e| e.to_string())?;
    if !project.starts_with(root) {
        return Err("bundle project resolves outside the bundle".into());
    }
    if let Invocation::Firmware { job, .. } = invocation {
        let (job, _) = crate::job::Job::load(job).map_err(|s| s.message().to_string())?;
        // Build argv is intentionally executable job policy, not a sandbox.
        // File fields and working directories must remain inside the snapshot.
        for p in job
            .modules
            .iter()
            .chain([&job.board, &job.elf])
            .chain(job.build.iter().map(|s| &s.cwd))
        {
            let path = project.join(p).canonicalize().map_err(|e| e.to_string())?;
            if !path.starts_with(root) {
                return Err(format!("bundle input resolves outside the bundle: {p}"));
            }
        }
        for module in [&job.image.module, &job.image.namespace] {
            if module
                .split('.')
                .any(|s| s.is_empty() || !s.chars().all(|c| c.is_alphanumeric() || c == '_'))
            {
                return Err("invalid bundle image module/namespace".into());
            }
        }
    }
    Ok(())
}
fn map_identity(
    identity: &Identity,
    f: impl Fn(&Path) -> Result<PathBuf, String>,
) -> Result<Identity, String> {
    Ok(Identity {
        files: identity
            .files
            .iter()
            .map(|(p, h)| f(p).map(|p| (p, h.clone())))
            .collect::<Result<_, _>>()?,
        source_roots: identity
            .source_roots
            .iter()
            .map(|p| f(p))
            .collect::<Result<_, _>>()?,
        explicit_files: identity
            .explicit_files
            .iter()
            .map(|p| f(p))
            .collect::<Result<_, _>>()?,
        toolchain: identity.toolchain.clone(),
    })
}
/// Snapshot a current accepted result into a directory that can be moved and
/// rechecked. Rechecking uses the pinned external tools and the current verifier;
/// this is a source bundle, not an authenticated proof certificate.
pub fn bundle_result(doc: &Value, out: &Path) -> Result<(), String> {
    let changed = stale(doc)?;
    if !changed.is_empty() {
        return Err(format!(
            "cannot bundle stale result: {}",
            changed.join(", ")
        ));
    }
    let e = evidence(doc)?;
    if out.exists() {
        return Err(format!("bundle destination exists: {}", out.display()));
    }
    let mut invocation: Invocation =
        serde_json::from_value(e.request.invocation).map_err(|e| e.to_string())?;
    map_invocation(&mut invocation, relative)?;
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let result = (|| {
        let mut identity = e.identity.clone();
        identity.files.clear();
        for (path, hash) in &e.identity.files {
            let rel = relative(path)?;
            let dst = safe_join(out, &rel)?;
            std::fs::create_dir_all(dst.parent().unwrap()).map_err(|e| e.to_string())?;
            std::fs::copy(path, &dst).map_err(|e| e.to_string())?;
            if crate::sha256::hex(&std::fs::read(&dst).map_err(|e| e.to_string())?) != hash.sha256 {
                return Err(format!("input changed while bundling: {}", path.display()));
            }
            identity.files.insert(rel, hash.clone());
        }
        identity.source_roots = e
            .identity
            .source_roots
            .iter()
            .map(|p| relative(p))
            .collect::<Result<_, _>>()?;
        identity.explicit_files = e
            .identity
            .explicit_files
            .iter()
            .map(|p| relative(p))
            .collect::<Result<_, _>>()?;
        let bundle = Bundle {
            schema: BUNDLE_SCHEMA.into(),
            invocation,
            outcome: e.outcome,
            identity,
        };
        std::fs::write(
            out.join("bundle.json"),
            serde_json::to_vec_pretty(&bundle).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        std::fs::write(
            out.join("result.json"),
            serde_json::to_vec_pretty(doc).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        std::fs::write(out.join("README.txt"), "Recheck with the identical e5r verifier and pinned external tools:\ne5r replay-bundle BUNDLE_DIRECTORY\nThis reruns the backend from bundled sources. See docs/verification/unified-core.md.\n").map_err(|e| e.to_string())?;
        Ok(())
    })();
    if result.is_err() {
        let _ = std::fs::remove_dir_all(out);
    }
    result
}
pub fn replay_bundle(out: &Path) -> Result<Value, String> {
    let root = out.canonicalize().map_err(|e| e.to_string())?;
    let mut bundle: Bundle = serde_json::from_slice(
        &std::fs::read(root.join("bundle.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    if bundle.schema != BUNDLE_SCHEMA {
        return Err("unsupported bundle schema".into());
    }
    let original_doc: Value = serde_json::from_slice(
        &std::fs::read(root.join("result.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let original = evidence(&original_doc)?;
    if !matches!(original.outcome, Outcome::Proved | Outcome::Refuted) {
        return Err("bundle must record a checked proof or refutation".into());
    }
    let mut expected: Invocation =
        serde_json::from_value(original.request.invocation.clone()).map_err(|e| e.to_string())?;
    map_invocation(&mut expected, relative)?;
    if serde_json::to_value(&expected).unwrap() != serde_json::to_value(&bundle.invocation).unwrap()
        || bundle.outcome != original.outcome
        || bundle.identity != map_identity(&original.identity, relative)?
    {
        return Err(
            "bundle manifest differs from its recorded verification request or identity".into(),
        );
    }
    map_invocation(&mut bundle.invocation, |p| safe_join(&root, p))?;
    let identity = Identity {
        files: bundle
            .identity
            .files
            .iter()
            .map(|(p, h)| safe_join(&root, p).map(|p| (p, h.clone())))
            .collect::<Result<_, _>>()?,
        source_roots: bundle
            .identity
            .source_roots
            .iter()
            .map(|p| safe_join(&root, p))
            .collect::<Result<_, _>>()?,
        explicit_files: bundle
            .identity
            .explicit_files
            .iter()
            .map(|p| safe_join(&root, p))
            .collect::<Result<_, _>>()?,
        toolchain: bundle.identity.toolchain,
    };
    validate_bundle_invocation(&bundle.invocation, &root)?;
    let changed = identity.stale(&bundle.invocation.project()?)?;
    if !changed.is_empty() {
        return Err(format!(
            "bundle inputs or tools differ: {}",
            changed.join(", ")
        ));
    }
    let doc = bundle.invocation.execute()?;
    let actual = evidence(&doc)?;
    if actual.outcome != bundle.outcome || actual.claim != original.claim {
        return Err(format!(
            "replay outcome {:?}, expected {:?}: {doc}",
            actual.outcome, bundle.outcome
        ));
    }
    Ok(doc)
}
pub fn replay_result(doc: &Value) -> Result<Value, String> {
    let changed = stale(doc)?;
    if !changed.is_empty() {
        return Err(format!("result is stale: {}", changed.join(", ")));
    }
    let e = evidence(doc)?;
    let invocation: Invocation =
        serde_json::from_value(e.request.invocation).map_err(|e| e.to_string())?;
    let result = invocation.execute()?;
    let replayed = evidence(&result)?;
    if replayed.outcome != e.outcome || replayed.claim != e.claim {
        return Err(format!("replay outcome changed: {result}"));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn proof_failure_is_inconclusive_and_never_refutation() {
        for s in ["failed", "unknown"] {
            assert_eq!(outcome(s), Outcome::Inconclusive);
        }
        assert_eq!(outcome("resource_exhausted"), Outcome::ResourceExhausted);
        assert_eq!(outcome("unsupported"), Outcome::Unsupported);
        assert_eq!(outcome("bogus"), Outcome::Error);
    }
    #[test]
    fn bundle_paths_cannot_escape() {
        for p in ["../escape", "/absolute", "a/../../b", ""] {
            assert!(safe_join(Path::new("/tmp/bundle"), Path::new(p)).is_err());
        }
        assert_eq!(
            safe_join(Path::new("/tmp/bundle"), Path::new("sources/a")).unwrap(),
            Path::new("/tmp/bundle/sources/a")
        );
    }
}
