//! Content identities and relocatable source bundles. These describe evidence;
//! they are not signatures and do not authenticate an untrusted result document.
use super::process::{self, Limits};
use crate::sha256;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

pub const SCHEMA: &str = "e5r.verification.evidence.v1";
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Outcome {
    Proved,
    Refuted,
    Inconclusive,
    ResourceExhausted,
    Unsupported,
    Error,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Binding {
    ExactGeneratedStatement,
    GeneratedClaim,
    ReviewedTheoremNames,
}
/// The backend supplies these identities; the core never interprets ISA or
/// platform-specific fields. Invocation is a versioned backend request.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Request {
    pub backend: String,
    pub architecture: String,
    pub platform: Value,
    pub invocation: Value,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct FileIdentity {
    pub sha256: String,
    pub bytes: u64,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Identity {
    pub files: BTreeMap<PathBuf, FileIdentity>,
    pub source_roots: Vec<PathBuf>,
    pub explicit_files: Vec<PathBuf>,
    pub toolchain: BTreeMap<String, String>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Evidence {
    pub schema: String,
    pub request: Request,
    pub outcome: Outcome,
    pub binding: Binding,
    pub identity: Identity,
    pub allowed_axioms: Vec<String>,
    pub claim: Value,
    pub evidence_id: String,
}
fn digest(path: &Path) -> Result<FileIdentity, String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(FileIdentity {
        sha256: sha256::hex(&b),
        bytes: b.len() as u64,
    })
}
fn sources(root: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    for e in std::fs::read_dir(root).map_err(|e| format!("{}: {e}", root.display()))? {
        let e = e.map_err(|e| e.to_string())?;
        let p = e.path();
        let ty = e.file_type().map_err(|e| e.to_string())?;
        if (ty.is_dir() || ty.is_symlink())
            && [".git", ".lake", "build", "target", "__pycache__"]
                .contains(&e.file_name().to_string_lossy().as_ref())
        {
            continue;
        }
        if ty.is_symlink() {
            return Err(format!(
                "source symlink must be an explicit input: {}",
                p.display()
            ));
        }
        if ty.is_dir() {
            if ![".git", ".lake", "build", "target", "__pycache__"]
                .contains(&e.file_name().to_string_lossy().as_ref())
            {
                sources(&p, out)?;
            }
        } else if ty.is_file() && e.file_name() != ".e5r-verification.lock" {
            out.push(p);
        }
    }
    Ok(())
}
impl Identity {
    pub fn capture(roots: &[PathBuf], files: &[PathBuf], project: &Path) -> Result<Self, String> {
        let canonical = |p: &PathBuf| {
            p.canonicalize()
                .map_err(|e| format!("{}: {e}", p.display()))
        };
        let source_roots: Vec<_> = roots.iter().map(canonical).collect::<Result<_, _>>()?;
        let mut explicit_files = Vec::new();
        for p in files {
            explicit_files.push(canonical(p)?);
            // Retain logical aliases too: a firmware target directory may be
            // a scratch symlink, while a portable job still names target/....
            let absolute = std::path::absolute(p).map_err(|e| e.to_string())?;
            let mut logical = PathBuf::new();
            for component in absolute.components() {
                match component {
                    std::path::Component::ParentDir => {
                        logical.pop();
                    }
                    std::path::Component::CurDir => {}
                    other => logical.push(other.as_os_str()),
                }
            }
            explicit_files.push(logical);
        }
        explicit_files.sort();
        explicit_files.dedup();
        let mut all = explicit_files.clone();
        for r in &source_roots {
            sources(r, &mut all)?;
        }
        let files = all
            .into_iter()
            .map(|p| {
                if p.to_str().is_none() {
                    return Err("verification identities require UTF-8 paths".into());
                }
                digest(&p).map(|h| (p, h))
            })
            .collect::<Result<_, _>>()?;
        let mut toolchain = BTreeMap::new();
        for tool in ["lean", "lake"] {
            let mut cmd = Command::new(tool);
            cmd.current_dir(project).arg("--version");
            let r = process::run(cmd, Limits::new(Duration::from_secs(10), 512))?;
            if !r.success {
                return Err(format!("{tool} version query failed: {}", r.output));
            }
            toolchain.insert(tool.into(), r.output.trim().into());
        }
        for tool in ["lean", "leanchecker", "lake"] {
            let mut cmd = Command::new("elan");
            cmd.current_dir(project).args(["which", tool]);
            let r = process::run(cmd, Limits::new(Duration::from_secs(10), 512))?;
            if !r.success {
                return Err(format!("cannot resolve pinned {tool}: {}", r.output));
            }
            toolchain.insert(
                format!("{tool}_sha256"),
                digest(Path::new(r.output.trim()))?.sha256,
            );
        }
        toolchain.insert(
            "verifier_sha256".into(),
            digest(Path::new("/proc/self/exe"))?.sha256,
        );
        Ok(Self {
            files,
            source_roots,
            explicit_files,
            toolchain,
        })
    }
    /// Add an artifact produced after the initial source snapshot, requiring the
    /// exact bytes used during acceptance and preserving its logical lookup path.
    pub fn pin_file(&mut self, path: &Path, expected_sha256: &str) -> Result<(), String> {
        let file = digest(path)?;
        if file.sha256 != expected_sha256 {
            return Err(format!("acceptance artifact changed: {}", path.display()));
        }
        let canonical = path.canonicalize().map_err(|e| e.to_string())?;
        let absolute = std::path::absolute(path).map_err(|e| e.to_string())?;
        let mut logical = PathBuf::new();
        for component in absolute.components() {
            match component {
                std::path::Component::ParentDir => {
                    logical.pop();
                }
                std::path::Component::CurDir => {}
                other => logical.push(other.as_os_str()),
            }
        }
        for path in [logical, canonical] {
            if path.to_str().is_none() {
                return Err("verification identities require UTF-8 paths".into());
            }
            self.files.insert(path.clone(), file.clone());
            self.explicit_files.push(path);
        }
        self.explicit_files.sort();
        self.explicit_files.dedup();
        Ok(())
    }
    pub fn stale(&self, project: &Path) -> Result<Vec<String>, String> {
        let now = Self::capture(&self.source_roots, &self.explicit_files, project)?;
        let mut changed: Vec<_> = self
            .files
            .keys()
            .chain(now.files.keys())
            .filter(|p| self.files.get(*p) != now.files.get(*p))
            .map(|p| p.display().to_string())
            .collect();
        if self.toolchain != now.toolchain {
            changed.push("toolchain/verifier".into());
        }
        changed.sort();
        changed.dedup();
        Ok(changed)
    }
}
impl Evidence {
    pub fn new(
        request: Request,
        outcome: Outcome,
        binding: Binding,
        identity: Identity,
        claim: Value,
    ) -> Self {
        let mut evidence = Self {
            schema: SCHEMA.into(),
            request,
            outcome,
            binding,
            identity,
            allowed_axioms: super::proof::ALLOWED_AXIOMS
                .iter()
                .map(|s| (*s).into())
                .collect(),
            claim,
            evidence_id: String::new(),
        };
        evidence.evidence_id = evidence.content_id();
        evidence
    }
    fn content_id(&self) -> String {
        sha256::hex(
            &serde_json::to_vec(&serde_json::json!({
                "schema": self.schema, "request": self.request, "outcome": self.outcome,
                "binding": self.binding, "identity": self.identity, "claim": self.claim,
                "allowed_axioms": self.allowed_axioms,
            }))
            .expect("evidence is JSON"),
        )
    }
    pub fn validate(&self) -> Result<(), String> {
        if self.evidence_id != self.content_id() {
            return Err("evidence content identity mismatch".into());
        }
        if self.schema != SCHEMA {
            return Err(format!("unsupported evidence schema {}", self.schema));
        }
        if self.allowed_axioms != super::proof::ALLOWED_AXIOMS {
            return Err("proof policy differs".into());
        }
        Ok(())
    }
}

/// Snapshot the loaded project libraries separately from source freshness. Lake
/// builds these before a proof runs; acceptance requires them to stay unchanged.
/// Core toolchain libraries are identified by the pinned distribution/tool hashes.
pub fn compiled_dependencies(project: &Path) -> Result<BTreeMap<PathBuf, FileIdentity>, String> {
    fn walk(path: &Path, out: &mut BTreeMap<PathBuf, FileIdentity>) -> Result<(), String> {
        for e in std::fs::read_dir(path).map_err(|e| e.to_string())? {
            let e = e.map_err(|e| e.to_string())?;
            let p = e.path();
            if e.file_type().map_err(|e| e.to_string())?.is_dir() {
                walk(&p, out)?;
            } else if p.extension().is_some_and(|e| e == "olean") {
                out.insert(p.canonicalize().map_err(|e| e.to_string())?, digest(&p)?);
            }
        }
        Ok(())
    }
    let mut files = BTreeMap::new();
    walk(&project.join(".lake/build/lib/lean"), &mut files)?;
    Ok(files)
}
