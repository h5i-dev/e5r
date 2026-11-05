//! Verification jobs: one target binary, its board, its proofs, and a result
//! that names every input it depends on.
//!
//! A job file (`e5r.verify.job.v1`) says how to obtain the ELF, which board it
//! runs on, which Lean modules prove what, and the resource limits. `run`
//! rebuilds and rechecks everything and returns an `e5r.verify.result.v1`
//! document. The status vocabulary is fixed:
//!
//! * `proved`: every named theorem checked, with only allowed axioms;
//! * `failed`: a proof did not check. This is *not* a counterexample: it says
//!   nothing about whether the property holds;
//! * `unsupported`: the binary or board is outside the supported scope (the
//!   exporter refused it), so no proof was attempted;
//! * `resource_exhausted`: a time or memory limit stopped a step;
//! * `error`: the job could not run (missing tool, malformed job, stale
//!   generated file).
//!
//! `counterexample` is reserved for a violation that has been replayed in the
//! model; no current job kind produces one, and a failed proof never does.

use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use crate::board::Board;
use crate::sha256;

pub const JOB_SCHEMA: &str = "e5r.verify.job.v1";
pub const RESULT_SCHEMA: &str = "e5r.verify.result.v1";

/// Axioms a checked theorem may depend on: Lean's standard ones.
pub use crate::core::proof::ALLOWED_AXIOMS;

/// The semantic model every job is checked against, in dependency order.
/// Its sources are part of every result's identity.
pub const MODEL: [&str; 4] = [
    "Theories/Hart.lean",
    "Theories/Platform.lean",
    "Theories/Logic.lean",
    "Theories/FlashElf.lean",
];

#[derive(Debug, Deserialize)]
pub struct Job {
    pub schema: String,
    pub id: String,
    /// The Lean root, relative to the job file.
    pub root: String,
    /// Relative to the root.
    pub board: String,
    pub elf: String,
    /// The reviewed identity of the ELF. A mismatch is an error: review the
    /// new bytes and update the job.
    pub elf_sha256: Option<String>,
    #[serde(default)]
    pub build: Vec<BuildStep>,
    pub image: ImageSpec,
    pub modules: Vec<String>,
    pub theorems: Vec<String>,
    /// Addresses the proofs hard-code, each with a substring of the ELF
    /// symbol that must start there (`{"0x200102a0": "duty"}`).
    #[serde(default)]
    pub symbols: BTreeMap<String, String>,
    #[serde(default)]
    pub limits: Limits,
}

#[derive(Debug, Deserialize)]
pub struct BuildStep {
    pub cwd: String,
    pub argv: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub struct ImageSpec {
    pub module: String,
    pub namespace: String,
    /// How the board holds the image. Absent means `flash`, the original
    /// job kind, unchanged.
    #[serde(default)]
    pub kind: ImageKind,
}

/// `flash`: the board boots PT_LOAD file bytes stored at their physical
/// addresses (`flash::export_flash`, `E5R.FlashElf`). `ram`: a loader puts
/// every PT_LOAD into RAM in place (`ram::ram_image`); the image the model
/// runs is defined by the checker's reader `E5R.RamElf.imageOf` applied to
/// the packed file, and the board must say `"image_placement": "ram"`.
#[derive(Clone, Copy, Debug, Default, Deserialize, serde::Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum ImageKind {
    #[default]
    Flash,
    Ram,
}

#[derive(Debug, Deserialize)]
pub struct Limits {
    pub seconds: u64,
    pub rss_mib: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            seconds: 1800,
            rss_mib: 5120,
        }
    }
}

/// Why a job stopped, mapped onto the result status.
#[derive(Debug)]
pub enum Stop {
    Failed(String),
    Unsupported(String),
    Exhausted(String, Value),
    Error(String),
}

impl Stop {
    fn status(&self) -> &'static str {
        match self {
            Stop::Failed(_) => "failed",
            Stop::Unsupported(_) => "unsupported",
            Stop::Exhausted(..) => "resource_exhausted",
            Stop::Error(_) => "error",
        }
    }
    pub(crate) fn message(&self) -> &str {
        match self {
            Stop::Failed(m) | Stop::Unsupported(m) | Stop::Exhausted(m, _) | Stop::Error(m) => m,
        }
    }
}

fn err<E: std::fmt::Display>(what: &str) -> impl FnOnce(E) -> Stop + '_ {
    move |e| Stop::Error(format!("{what}: {e}"))
}

pub struct Paths {
    pub job: PathBuf,
    pub root: PathBuf,
}

impl Job {
    pub fn load(path: &Path) -> Result<(Job, Paths), Stop> {
        let text = std::fs::read_to_string(path).map_err(err("job"))?;
        let job: Job = serde_json::from_str(&text).map_err(err("job"))?;
        if job.schema != JOB_SCHEMA {
            return Err(Stop::Error(format!(
                "job schema {} is not {JOB_SCHEMA}",
                job.schema
            )));
        }
        let dir = path.parent().unwrap_or(Path::new("."));
        let root = dir.join(&job.root);
        Ok((
            job,
            Paths {
                job: path.to_path_buf(),
                root,
            },
        ))
    }

    pub fn module_path(module: &str) -> String {
        module.replace('.', "/") + ".lean"
    }

    /// The model sources this job is checked against, in dependency order.
    pub fn model(&self) -> Vec<String> {
        let mut m: Vec<String> = MODEL.iter().map(|s| s.to_string()).collect();
        if self.image.kind == ImageKind::Ram {
            m.push(RAM_READER.into());
        }
        m
    }

    /// The generated module that binds the image to the model.
    pub fn fidelity_module(&self) -> String {
        format!("{}Fidelity", self.image.module)
    }

    /// Where a RAM job's exporter manifest is kept, relative to the root.
    pub fn ram_manifest(&self) -> String {
        format!("build/jobs/{}/ram-image.json", self.id)
    }
}

/// The checker's independent reader of RAM-resident ELF images.
pub const RAM_READER: &str = "Theories/RamElf.lean";

/// `image_placement` of a board JSON (`null` or absent for flash boards).
fn image_placement(board_text: &str) -> Result<Option<String>, Stop> {
    let v: Value = serde_json::from_str(board_text).map_err(err("board"))?;
    match &v["image_placement"] {
        Value::Null => Ok(None),
        Value::String(s) => Ok(Some(s.clone())),
        other => Err(Stop::Error(format!(
            "board image_placement {other} is not a string"
        ))),
    }
}

/// What happened to one step.
struct Stage {
    name: String,
    seconds: f64,
    peak_rss_mib: u64,
}

fn run_limited(cmd: Command, limits: &Limits, what: &str) -> Result<(String, u64), Stop> {
    let r = crate::core::process::run(
        cmd,
        crate::core::process::Limits::new(Duration::from_secs(limits.seconds), limits.rss_mib),
    )
    .map_err(|e| Stop::Error(format!("{what}: {e}")))?;
    if r.cancelled {
        return Err(Stop::Error(format!("{what}: execution cancelled")));
    }
    if let Some(limit) = r.exhaustion {
        return Err(Stop::Exhausted(
            format!("{what}: {limit:?} limit exceeded\n{}", tail(&r.output)),
            serde_json::to_value(&r).unwrap(),
        ));
    }
    if !r.success {
        return Err(Stop::Failed(format!(
            "{what}: exited {:?}\n{}",
            r.code,
            tail(&r.output)
        )));
    }
    Ok((r.output, r.peak_rss_mib))
}

fn tail(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    lines[lines.len().saturating_sub(40)..].join("\n")
}

pub use crate::core::proof::{FORBIDDEN, declared_theorems, escapes, lean_code, parse_axioms};

fn tool_version(root: &Path, argv: &[&str]) -> Option<String> {
    let mut cmd = Command::new(argv[0]);
    cmd.current_dir(root).args(&argv[1..]);
    let out = crate::core::process::run(
        cmd,
        crate::core::process::Limits::new(Duration::from_secs(10), 512),
    )
    .ok()?;
    if !out.success {
        return None;
    }
    out.output.lines().next().map(|l| l.trim().to_string())
}

/// Everything a result depends on, hashed. `verify-result` recomputes this
/// and compares it, so changing any input makes an old result stale.
pub fn identity(job: &Job, paths: &Paths) -> Result<Value, Stop> {
    let read =
        |p: &Path| std::fs::read(p).map_err(|e| Stop::Error(format!("{}: {e}", p.display())));
    let mut sources = BTreeMap::new();
    let mut files: Vec<String> = job.model();
    files.push(format!(
        "Theories/Board/{}.lean",
        board_module_name(&job.board)?
    ));
    files.extend(job.modules.iter().cloned());
    for f in &files {
        sources.insert(f.clone(), sha256::hex(&read(&paths.root.join(f))?));
    }
    let elf = read(&paths.root.join(&job.elf))?;
    let exe = std::fs::read("/proc/self/exe")
        .ok()
        .map(|b| sha256::hex(&b));
    sources.insert(
        "tools/gen_board.py".into(),
        sha256::hex(&read(&paths.root.join("tools/gen_board.py"))?),
    );
    // A RAM job's generated files are pinned too: the packed module and its
    // binding are regenerated from the ELF every run, and a result is stale
    // if either on disk is not what that run produced.
    let image = if job.image.kind == ImageKind::Ram {
        let hash = |rel: &str| {
            std::fs::read(paths.root.join(rel))
                .ok()
                .map(|b| sha256::hex(&b))
        };
        let module = Job::module_path(&job.image.module);
        let fidelity = Job::module_path(&job.fidelity_module());
        json!({
            "kind": "ram",
            "module": { "path": module, "sha256": hash(&module) },
            "fidelity": { "path": fidelity, "sha256": hash(&fidelity) },
            "manifest": { "path": job.ram_manifest(), "sha256": hash(&job.ram_manifest()) },
        })
    } else {
        Value::Null
    };
    let mut common_files: Vec<PathBuf> = files.iter().map(|f| paths.root.join(f)).collect();
    common_files.extend([
        paths.job.clone(),
        paths.root.join(&job.board),
        paths.root.join(&job.elf),
        paths.root.join("lean-toolchain"),
        paths.root.join("lakefile.lean"),
        paths.root.join("lake-manifest.json"),
        paths.root.join("tools/ProofCheck.lean"),
        paths.root.join(Job::module_path(&job.image.module)),
        paths.root.join(Job::module_path(&job.fidelity_module())),
    ]);
    if job.image.kind == ImageKind::Ram {
        common_files.push(paths.root.join(job.ram_manifest()));
    }
    // Build recipes may invoke arbitrary tools. Capture the reviewed build source
    // inventory as well as the resulting ELF; this does not prove compiler correctness.
    fn build_sources(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), Stop> {
        for entry in std::fs::read_dir(dir).map_err(err("build sources"))? {
            let entry = entry.map_err(err("build source"))?;
            let p = entry.path();
            if entry.file_type().map_err(err("build source"))?.is_dir() {
                if ![".lake", "build", "target", ".git", "__pycache__"]
                    .contains(&entry.file_name().to_string_lossy().as_ref())
                {
                    build_sources(&p, out)?;
                }
            } else if matches!(
                p.extension().and_then(|s| s.to_str()),
                Some("rs" | "ld" | "toml" | "lock" | "py" | "sh" | "json")
            ) {
                out.push(p);
            }
        }
        Ok(())
    }
    build_sources(&paths.root, &mut common_files)?;
    let common = crate::core::artifact::Identity::capture(
        &[paths.root.join("../common")],
        &common_files,
        &paths.root,
    )
    .map_err(Stop::Error)?;
    Ok(json!({
        "common_identity": common,
        "image": image,
        "job_sha256": sha256::hex(&read(&paths.job)?),
        "board_sha256": sha256::hex(&read(&paths.root.join(&job.board))?),
        "elf": { "path": job.elf, "sha256": sha256::hex(&elf), "bytes": elf.len() },
        "sources": sources,
        "lean": tool_version(&paths.root, &["lean", "--version"]),
        "e5r_verify": env!("CARGO_PKG_VERSION"),
        "e5r_verify_sha256": exe,
        "allowed_axioms": ALLOWED_AXIOMS,
    }))
}

fn board_module_name(board: &str) -> Result<String, Stop> {
    let stem = Path::new(board)
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| Stop::Error(format!("board path {board}")))?;
    Ok(stem
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|p| !p.is_empty())
        .map(|p| {
            let mut c = p.chars();
            c.next()
                .map(|f| f.to_ascii_uppercase().to_string() + &c.as_str().to_ascii_lowercase())
                .unwrap_or_default()
        })
        .collect())
}

/// Rebuild, export, check and audit. Returns the result document whatever
/// the outcome.
///
/// With `resume`, a module whose source and every earlier module's source
/// (and the Lean version) are unchanged since it last compiled successfully
/// is not recompiled; its `.olean` from that run is used. The result lists
/// such modules under `resumed`. Without it (the default, and what CI and
/// releases use) every module is checked from source.
pub fn run(job_path: &Path, resume: bool) -> Value {
    let started = Instant::now();
    let mut stages = Vec::new();
    let mut resumed: Vec<String> = Vec::new();
    let mut checked: Vec<String> = Vec::new();
    let outcome = (|| -> Result<(Value, Value), Stop> {
        let (job, paths) = Job::load(job_path)?;
        let _lock =
            crate::core::workspace::ProjectLock::acquire(&paths.root).map_err(Stop::Error)?;
        let limits = &job.limits;
        // Build the ELF from source, if the job says how.
        for (i, step) in job.build.iter().enumerate() {
            let t = Instant::now();
            let program = step
                .argv
                .first()
                .ok_or_else(|| Stop::Error(format!("build step {i} has empty argv")))?;
            let mut cmd = Command::new(program);
            cmd.args(&step.argv[1..])
                .current_dir(paths.root.join(&step.cwd));
            let (_, rss) =
                run_limited(cmd, limits, &format!("build step {i}")).map_err(|s| match s {
                    Stop::Failed(m) => Stop::Error(m),
                    other => other,
                })?;
            stages.push(Stage {
                name: format!("build {}", step.argv.join(" ")),
                seconds: t.elapsed().as_secs_f64(),
                peak_rss_mib: rss,
            });
        }
        let elf_path = paths.root.join(&job.elf);
        let elf = std::fs::read(&elf_path).map_err(err("elf"))?;
        let digest = sha256::hex(&elf);
        if let Some(pin) = &job.elf_sha256
            && *pin != digest
        {
            return Err(Stop::Error(format!(
                "ELF identity changed ({digest}, job pins {pin}); review the new bytes and update elf_sha256"
            )));
        }
        // Addresses the proofs hard-code must be where the named symbols are.
        if !job.symbols.is_empty() {
            let obj = e5r_format::load(&elf, &e5r_format::LoadOptions::default())
                .map_err(|e| Stop::Error(format!("symbols: {e}")))?;
            for (addr, name) in &job.symbols {
                let a = u64::from_str_radix(addr.trim_start_matches("0x"), 16)
                    .map_err(|e| Stop::Error(format!("symbol address {addr}: {e}")))?;
                if !obj
                    .symbols
                    .iter()
                    .any(|s| s.addr.get() == a && s.name.contains(name.as_str()))
                {
                    return Err(Stop::Error(format!(
                        "no symbol containing {name:?} at {addr}: the proof's addresses are stale"
                    )));
                }
            }
        }
        // The generated board must match its JSON source.
        let board_text =
            std::fs::read_to_string(paths.root.join(&job.board)).map_err(err("board"))?;
        let board = Board::parse(&board_text).map_err(Stop::Error)?;
        let board_mod = board_module_name(&job.board)?;
        let mut regen = Command::new("python3");
        regen
            .arg(paths.root.join("tools/gen_board.py"))
            .arg("--check")
            .arg(paths.root.join(&job.board));
        run_limited(regen, limits, "board generation").map_err(|s| match s {
            Stop::Failed(m) => {
                Stop::Error(format!("Theories/Board/{board_mod}.lean is stale: {m}"))
            }
            other => other,
        })?;
        // Export the image. Refusal means the binary is out of scope. The
        // board must hold images the way the job says.
        let placement = image_placement(&board_text)?;
        let fidelity_mod = job.fidelity_module();
        let image_path = paths.root.join(Job::module_path(&job.image.module));
        let fidelity_path = paths.root.join(Job::module_path(&fidelity_mod));
        // Never leave a previous run's generated files to be checked.
        for p in [&image_path, &fidelity_path] {
            match std::fs::remove_file(p) {
                Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
                    return Err(Stop::Error(format!("{}: {e}", p.display())));
                }
                _ => {}
            }
        }
        let (image, fidelity, binding) = match job.image.kind {
            ImageKind::Flash => {
                if placement.is_some() {
                    return Err(Stop::Error(format!(
                        "board {} places images in {}; this job's image.kind is flash",
                        board.id,
                        placement.unwrap_or_default()
                    )));
                }
                let windows = board.windows().map_err(Stop::Error)?;
                let image = crate::flash::export_flash(&elf, windows, &job.image.namespace)
                    .map_err(Stop::Unsupported)?;
                // The independent Lean reader must reconstruct exactly this image.
                let fidelity = format!(
                    "-- Generated by e5r check; regenerate, do not edit.\n\
                     import Theories.FlashElf\nimport {img}\nset_option maxRecDepth 100000\n\
                     theorem {ns}.image_fidelity : E5R.FlashElf.loadFlash ⟨{fb}, {fs}, {rb}, {rs}⟩ {ns}.elfBytes = \
                     .ok ({ns}.entry, {ns}.segments) := by decide +kernel\n",
                    img = job.image.module,
                    ns = job.image.namespace,
                    fb = windows.flash_base,
                    fs = windows.flash_size,
                    rb = windows.ram_base,
                    rs = windows.ram_size,
                );
                (
                    image,
                    fidelity,
                    vec![format!("{}.image_fidelity", job.image.namespace)],
                )
            }
            ImageKind::Ram => {
                if placement.as_deref() != Some("ram") {
                    return Err(Stop::Error(format!(
                        "board {} does not place images in RAM; this job's image.kind is ram",
                        board.id
                    )));
                }
                let (base, size) = crate::ram::board_window(&board).map_err(Stop::Error)?;
                let policy = crate::ram::Policy::new(base, size);
                let img = crate::ram::ram_image(&elf, policy).map_err(Stop::Unsupported)?;
                let ns = &job.image.namespace;
                let manifest = crate::ram::manifest(&elf, &img, policy);
                let manifest_path = paths.root.join(job.ram_manifest());
                if let Some(dir) = manifest_path.parent() {
                    std::fs::create_dir_all(dir).map_err(err("manifest"))?;
                }
                std::fs::write(
                    &manifest_path,
                    serde_json::to_string_pretty(&manifest).unwrap() + "\n",
                )
                .map_err(err("manifest"))?;
                (
                    crate::ram::lean(&elf, ns),
                    crate::ram::fidelity_source(&img, &job.image.module, ns, base, size),
                    crate::ram::fidelity_theorems(ns),
                )
            }
        };
        std::fs::write(&image_path, &image).map_err(err("image"))?;
        std::fs::write(&fidelity_path, fidelity).map_err(err("fidelity"))?;
        // Check every module, model first, each from source.
        let mut order: Vec<String> = job.model();
        order.push(format!("Theories/Board/{board_mod}.lean"));
        order.push(Job::module_path(&job.image.module));
        order.push(Job::module_path(&fidelity_mod));
        order.extend(job.modules.iter().cloned());
        checked = order.clone();
        for (i, m) in order.iter().enumerate() {
            let src = std::fs::read_to_string(paths.root.join(m)).map_err(err(m))?;
            let code = lean_code(&src);
            let found = escapes(&code);
            if !found.is_empty() {
                return Err(Stop::Error(format!("{m}: forbidden {}", found.join(", "))));
            }
            // Every import must be a module checked earlier in this job, so
            // nothing is loaded from an olean this run did not produce.
            let earlier: Vec<String> = order[..i]
                .iter()
                .map(|e| e.trim_end_matches(".lean").replace('/', "."))
                .collect();
            for line in code.lines() {
                if let Some(rest) = line.trim_start().strip_prefix("import ") {
                    for module in rest.split_whitespace() {
                        if !earlier.iter().any(|e| e == module) {
                            return Err(Stop::Error(format!(
                                "{m} imports {module}, which this job does not check before it"
                            )));
                        }
                    }
                }
            }
        }
        let mut checker_build = Command::new("lake");
        checker_build
            .current_dir(&paths.root)
            .env("LEAN_NUM_THREADS", "1")
            .args(["build", "-q", "proofcheck"]);
        run_limited(checker_build, limits, "shared proof checker build")?;
        let before = identity(&job, &paths)?;
        let manifest_path = paths
            .root
            .join(format!("build/jobs/{}/stages.json", job.id));
        let mut manifest: BTreeMap<String, String> = std::fs::read_to_string(&manifest_path)
            .ok()
            .and_then(|t| serde_json::from_str(&t).ok())
            .unwrap_or_default();
        let mut chain = sha256::hex(
            tool_version(&paths.root, &["lean", "--version"])
                .unwrap_or_default()
                .as_bytes(),
        );
        for m in &order {
            let src = std::fs::read(paths.root.join(m)).map_err(err(m))?;
            chain = sha256::hex(format!("{chain} {m} {}", sha256::hex(&src)).as_bytes());
            let t = Instant::now();
            let olean = Path::new(m).with_extension("olean");
            if resume
                && manifest.get(m)
                    == std::fs::read(paths.root.join(&olean))
                        .ok()
                        .map(|b| format!("{chain}:{}", sha256::hex(&b)))
                        .as_ref()
            {
                resumed.push(m.clone());
                continue;
            }
            manifest.remove(m);
            let mut cmd = Command::new("lean");
            cmd.current_dir(&paths.root)
                .env("LEAN_PATH", ".")
                .args([
                    "-j1",
                    &format!("-M{}", limits.rss_mib.saturating_sub(512).max(512)),
                ])
                .arg("-o")
                .arg(&olean)
                .arg(m);
            let (_, rss) = run_limited(cmd, limits, m)?;
            stages.push(Stage {
                name: format!("lean {m}"),
                seconds: t.elapsed().as_secs_f64(),
                peak_rss_mib: rss,
            });
            let compiled =
                std::fs::read(paths.root.join(&olean)).map_err(err("compiled module"))?;
            manifest.insert(m.clone(), format!("{chain}:{}", sha256::hex(&compiled)));
            if let Some(dir) = manifest_path.parent() {
                let _ = std::fs::create_dir_all(dir);
            }
            let _ = std::fs::write(
                &manifest_path,
                serde_json::to_string_pretty(&manifest).unwrap(),
            );
        }
        // Replay every module's declarations through a fresh kernel. This is
        // what catches declarations added without kernel checking, whatever
        // the source looked like.
        for m in &order {
            let t = Instant::now();
            let replay = crate::core::proof::replay(
                &paths.root,
                crate::core::proof::SearchPath::Direct("."),
                &m.trim_end_matches(".lean").replace('/', "."),
                crate::core::process::Limits::new(
                    Duration::from_secs(limits.seconds),
                    limits.rss_mib,
                ),
            )
            .map_err(Stop::Error)?;
            if replay.cancelled {
                return Err(Stop::Error("kernel replay cancelled".into()));
            }
            if let Some(e) = replay.exhaustion {
                return Err(Stop::Exhausted(
                    format!("leanchecker {m}: {e:?}"),
                    serde_json::to_value(&replay).unwrap(),
                ));
            }
            if !replay.success {
                return Err(Stop::Failed(format!("leanchecker {m}: {}", replay.output)));
            }
            let rss = replay.peak_rss_mib;
            stages.push(Stage {
                name: format!("leanchecker {m}"),
                seconds: t.elapsed().as_secs_f64(),
                peak_rss_mib: rss,
            });
        }
        // Audit every named theorem plus the image binding. `Ns.*` names
        // every theorem the job's modules declare in namespace `Ns`.
        let mut names = Vec::new();
        for t in &job.theorems {
            match t.strip_suffix(".*") {
                Some(ns) => {
                    let mut found = false;
                    for m in &job.modules {
                        let src = std::fs::read_to_string(paths.root.join(m)).map_err(err(m))?;
                        for n in declared_theorems(&lean_code(&src)) {
                            if n.starts_with(&format!("{ns}.")) {
                                names.push(n);
                                found = true;
                            }
                        }
                    }
                    if !found {
                        return Err(Stop::Error(format!("no theorems in {ns}")));
                    }
                }
                None => names.push(t.clone()),
            }
        }
        names.extend(binding);
        let mut cmd = Command::new(
            paths
                .root
                .join(".lake/build/bin/proofcheck")
                .canonicalize()
                .map_err(err("proof checker"))?,
        );
        cmd.current_dir(&paths.root)
            .env("LEAN_PATH", ".")
            .arg("named");
        for m in &order {
            cmd.arg(m.trim_end_matches(".lean").replace('/', "."));
        }
        cmd.arg("--").args(&names);
        let audited = crate::core::process::run(
            cmd,
            crate::core::process::Limits::new(Duration::from_secs(limits.seconds), limits.rss_mib),
        )
        .map_err(Stop::Error)?;
        if audited.cancelled {
            return Err(Stop::Error("axiom audit cancelled".into()));
        }
        if let Some(e) = audited.exhaustion {
            return Err(Stop::Exhausted(
                format!("axiom audit: {e:?}"),
                serde_json::to_value(&audited).unwrap(),
            ));
        }
        // Missing names are job errors; disallowed axioms are proof failures.
        let report = crate::core::proof::checker_report(&audited).map_err(|e| {
            if e.contains("axioms outside") {
                Stop::Failed(e)
            } else {
                Stop::Error(e)
            }
        })?;
        let theorems = report["theorems"]
            .as_array()
            .ok_or_else(|| Stop::Error("checker missing theorem reports".into()))?
            .clone();
        let after = identity(&job, &paths)?;
        if after != before {
            return Err(Stop::Error("inputs changed while the job ran".into()));
        }
        Ok((after, Value::Array(theorems)))
    })();
    let stages_json: Vec<Value> = stages
        .iter()
        .map(|s| json!({ "name": s.name, "seconds": s.seconds, "peak_rss_mib": s.peak_rss_mib }))
        .collect();
    let job_id = Job::load(job_path).map(|(j, _)| j.id).unwrap_or_default();
    let mut result = json!({
        "schema": RESULT_SCHEMA,
        "job": job_id,
        "job_file": job_path.display().to_string(),
        "seconds": started.elapsed().as_secs_f64(),
        "stages": stages_json,
        "resumed": resumed,
        "modules": checked,
    });
    match outcome {
        Ok((ident, theorems)) => {
            result["status"] = json!("proved");
            result["inputs"] = ident;
            result["theorems"] = theorems;
        }
        Err(stop) => {
            if let Stop::Exhausted(_, detail) = &stop {
                result["execution"] = detail.clone();
            }
            result["status"] = json!(stop.status());
            result["message"] = json!(stop.message());
            if let Ok((job, paths)) = Job::load(job_path)
                && let Ok(ident) = identity(&job, &paths)
            {
                result["inputs"] = ident;
            }
        }
    }
    if let Err(e) = crate::verification::attach_firmware(&mut result, job_path)
        && result["status"] == "proved"
    {
        result["status"] = json!("error");
        result["message"] = json!(format!("provenance: {e}"));
    }
    result
}

/// Is a stored result still about the current inputs? Returns the list of
/// inputs that changed; empty means current.
pub fn stale(result: &Value) -> Result<Vec<String>, String> {
    if result["schema"] != RESULT_SCHEMA {
        return Err("not an e5r.verify.result.v1 document".into());
    }
    let job_file = result["job_file"]
        .as_str()
        .ok_or("result has no job_file")?;
    let (job, paths) = Job::load(Path::new(job_file)).map_err(|s| s.message().to_string())?;
    let now = identity(&job, &paths).map_err(|s| s.message().to_string())?;
    let then = &result["inputs"];
    let mut changed = Vec::new();
    for key in [
        "job_sha256",
        "board_sha256",
        "lean",
        "e5r_verify",
        "e5r_verify_sha256",
    ] {
        if now[key] != then[key] {
            changed.push(key.to_string());
        }
    }
    if now["image"] != then["image"] {
        changed.push("generated image".to_string());
    }
    if now["elf"]["sha256"] != then["elf"]["sha256"] {
        changed.push(format!("elf {}", job.elf));
    }
    let empty = serde_json::Map::new();
    let (a, b) = (
        now["sources"].as_object().unwrap_or(&empty),
        then["sources"].as_object().unwrap_or(&empty),
    );
    for (k, v) in a {
        if b.get(k) != Some(v) {
            changed.push(k.clone());
        }
    }
    for k in b.keys() {
        if !a.contains_key(k) {
            changed.push(k.clone());
        }
    }
    if result["status"] != "proved" {
        changed.push(format!("status is {}", result["status"]));
    }
    if now["common_identity"] != then["common_identity"] {
        changed.push("common provenance".into());
    }
    if let Some(common) = then.get("common_identity") {
        let identity: crate::core::artifact::Identity =
            serde_json::from_value(common.clone()).map_err(|e| e.to_string())?;
        changed.extend(identity.stale(&paths.root)?);
    }
    Ok(changed)
}

/// Bundled with RAM-image jobs: unpack the `E5R.RamElf.File` literal and
/// compare every byte with the ELF (independent of the Rust packer).
const PACKING_CHECK: &str = r#"import re, sys
src = open(sys.argv[1], encoding="utf-8").read()
elf = open(sys.argv[2], "rb").read()
m = re.search(r"def elf : E5R\.RamElf\.File := ⟨(\d+), \[([0-9,\s]*)\]⟩", src)
assert m, "no File literal"
n, words = int(m.group(1)), [int(w) for w in m.group(2).split(",") if w.strip()]
assert n == len(elf) and len(words) == (n + 63) // 64, "length"
assert all(w < 256 ** 64 for w in words), "word too large"
data = b"".join(w.to_bytes(64, "little") for w in words)
assert data[:n] == elf and not any(data[n:]), "bytes differ"
print(f"packing: all {n} ELF bytes equal the Lean File literal")
"#;

/// After a fresh `proved` run, write everything needed to recheck the
/// proofs with nothing but the pinned Lean: the sources and generated
/// modules in their layout, the ELF, the result, a `recheck.sh` that
/// recompiles every module and compares the axiom report with the recorded
/// one, and SHA-256 sums of every file.
pub fn bundle(job_path: &Path, out: &Path) -> Result<Value, String> {
    let result = run(job_path, false);
    if result["status"] != "proved" {
        return Err(format!(
            "not bundling: status {} ({})",
            result["status"],
            result["message"].as_str().unwrap_or("")
        ));
    }
    let (job, paths) = Job::load(job_path).map_err(|s| s.message().to_string())?;
    let modules: Vec<String> = result["modules"]
        .as_array()
        .map(|a| {
            a.iter()
                .filter_map(|m| m.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    let mut files: Vec<String> = modules.clone();
    files.push("lean-toolchain".into());
    files.push(job.elf.clone());
    files.push(job.board.clone());
    if job.image.kind == ImageKind::Ram {
        files.push(job.ram_manifest());
    }
    let mut sums = String::new();
    for f in &files {
        let src = paths.root.join(f);
        let dst = out.join(f);
        std::fs::create_dir_all(dst.parent().unwrap()).map_err(|e| e.to_string())?;
        let bytes = std::fs::read(&src).map_err(|e| format!("{f}: {e}"))?;
        std::fs::write(&dst, &bytes).map_err(|e| format!("{f}: {e}"))?;
        sums.push_str(&format!("{}  {f}\n", sha256::hex(&bytes)));
    }
    let mut expected = String::new();
    let mut audit = String::new();
    for m in &modules {
        audit.push_str(&format!(
            "import {}\n",
            m.trim_end_matches(".lean").replace('/', ".")
        ));
    }
    for t in result["theorems"].as_array().into_iter().flatten() {
        let name = t["name"].as_str().unwrap_or("");
        let axioms: Vec<&str> = t["axioms"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|a| a.as_str())
            .collect();
        audit.push_str(&format!("#print axioms {name}\n"));
        expected.push_str(&if axioms.is_empty() {
            format!("'{name}' does not depend on any axioms\n")
        } else {
            format!("'{name}' depends on axioms: [{}]\n", axioms.join(", "))
        });
    }
    // A RAM image's Lean file is the ELF packed by the exporter; the bundle
    // re-derives the bytes from it, without the exporter, and compares.
    let packing = if job.image.kind == ImageKind::Ram {
        std::fs::write(out.join("check-packing.py"), PACKING_CHECK).map_err(|e| e.to_string())?;
        sums.push_str(&format!(
            "{}  check-packing.py\n",
            sha256::hex(PACKING_CHECK.as_bytes())
        ));
        format!(
            "python3 -I check-packing.py {} {}\n",
            Job::module_path(&job.image.module),
            job.elf
        )
    } else {
        String::new()
    };
    let script = format!(
        "#!/usr/bin/env bash\n\
         # Recheck this bundle with only Lean (the version in lean-toolchain).\n\
         set -euo pipefail\ncd \"$(dirname \"$0\")\"\n\
         sha256sum -c --quiet SHA256SUMS\n{packing}\
         for m in {mods}; do\n  LEAN_PATH=. lean -j1 -o \"${{m%.lean}}.olean\" \"$m\"\n  mod=${{m%.lean}}\n  LEAN_PATH=. leanchecker \"${{mod//\\//.}}\"\ndone\n\
         LEAN_PATH=. lean -j1 Audit.lean > axioms.actual\n\
         awk -f normalize-axioms.awk axioms.expected | LC_ALL=C sort > axioms.expected.sorted\n\
         awk -f normalize-axioms.awk axioms.actual | LC_ALL=C sort > axioms.actual.sorted\n\
         diff axioms.expected.sorted axioms.actual.sorted\n\
         echo \"recheck: every theorem checked, with exactly the recorded axioms\"\n",
        mods = modules.join(" ")
    );
    let normalize = r#"{
  marker = "' depends on axioms: ["
  i = index($0, marker)
  if (i) {
    name = substr($0, 1, i - 1)
    list = substr($0, i + length(marker))
    sub(/\]$/, "", list)
    n = split(list, ax, ", ")
    for (j = 1; j <= n; j++) print name "|" ax[j]
  } else print $0
}
"#;
    for (name, text) in [
        ("Audit.lean", audit),
        ("axioms.expected", expected),
        ("recheck.sh", script),
        ("normalize-axioms.awk", normalize.into()),
        (
            "result.json",
            serde_json::to_string_pretty(&result).unwrap() + "\n",
        ),
    ] {
        sums.push_str(&format!("{}  {name}\n", sha256::hex(text.as_bytes())));
        std::fs::write(out.join(name), text).map_err(|e| format!("{name}: {e}"))?;
    }
    std::fs::write(out.join("SHA256SUMS"), sums).map_err(|e| e.to_string())?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(
            out.join("recheck.sh"),
            std::fs::Permissions::from_mode(0o755),
        );
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_escape_scan_sees_code_not_comments() {
        let src = "-- sorry in a comment\n/- admit /- nested native_decide -/ -/\n\
                   def s := \"axiom\"\ntheorem t : True := by trivial\n";
        assert!(escapes(&lean_code(src)).is_empty());
        let quote = "def q := '\"'\ntheorem t : False := by sorry";
        assert!(escapes(&lean_code(quote)).contains(&"sorry"));
        for bad in [
            "theorem t : False := by sorry",
            "axiom bad : False",
            "theorem t : 1 = 1 := by native_decide",
            "@[implemented_by f] def g := 1",
            "set_option debug.skipKernelTC true",
            "unsafe def f := 1",
            "theorem t := Lean.ofReduceBool _ _ rfl",
            "run_cmd liftCoreM do pure ()",
            "#eval 1",
            "elab \"x\" : term => pure default",
        ] {
            assert!(!escapes(&lean_code(bad)).is_empty(), "missed {bad}");
        }
    }

    #[test]
    fn axiom_reports_are_parsed_strictly() {
        let ok =
            "'A.b' depends on axioms: [propext, Quot.sound]\n'C' does not depend on any axioms\n";
        let m = parse_axioms(ok).unwrap();
        assert_eq!(m["A.b"], ["propext", "Quot.sound"]);
        assert!(m["C"].is_empty());
        assert!(parse_axioms("error: unknown constant 'X'").is_err());
        assert!(parse_axioms("'A' depends on axioms: [sorryAx]\nwarning: x").is_err());
        let primes = "'A.f'' depends on axioms: [propext]\n'A.g''' does not depend on any axioms\n";
        let m = parse_axioms(primes).unwrap();
        assert_eq!(m["A.f'"], ["propext"]);
        assert!(m["A.g''"].is_empty());
    }

    #[test]
    fn theorem_names_follow_namespaces() {
        let src = "namespace A.B\ntheorem x : True := trivial\n\
                   @[simp] private theorem z : True := trivial\nend A.B\ntheorem y : True := trivial\n";
        assert_eq!(declared_theorems(src), ["A.B.x", "A.B.z", "y"]);
    }

    #[test]
    fn board_module_names_match_the_generator() {
        assert_eq!(
            board_module_name("boards/hifive1-revb.json").unwrap(),
            "Hifive1Revb"
        );
    }

    fn job_with_image(image: &str) -> Result<Job, serde_json::Error> {
        serde_json::from_str(&format!(
            r#"{{"schema": "{JOB_SCHEMA}", "id": "t", "root": ".", "board": "b.json",
                "elf": "x.elf", "image": {image}, "modules": [], "theorems": []}}"#
        ))
    }

    #[test]
    fn image_kind_defaults_to_flash_and_rejects_unknown_kinds() {
        let flash = job_with_image(r#"{"module": "A.Image", "namespace": "A"}"#).unwrap();
        assert_eq!(flash.image.kind, ImageKind::Flash);
        assert_eq!(flash.model(), MODEL);
        let ram =
            job_with_image(r#"{"kind": "ram", "module": "A.Image", "namespace": "A"}"#).unwrap();
        assert_eq!(ram.image.kind, ImageKind::Ram);
        assert_eq!(ram.model().last().unwrap(), RAM_READER);
        assert_eq!(ram.fidelity_module(), "A.ImageFidelity");
        assert_eq!(ram.ram_manifest(), "build/jobs/t/ram-image.json");
        for bad in ["rom", "RAM", ""] {
            let spec = format!(r#"{{"kind": "{bad}", "module": "A.Image", "namespace": "A"}}"#);
            assert!(job_with_image(&spec).is_err(), "accepted kind {bad:?}");
        }
    }

    #[test]
    fn boards_say_where_images_live() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../verification/rv32/boards");
        let virt = std::fs::read_to_string(dir.join("qemu-virt-rv32.json")).unwrap();
        let hifive = std::fs::read_to_string(dir.join("hifive1-revb.json")).unwrap();
        assert_eq!(image_placement(&virt).unwrap().as_deref(), Some("ram"));
        assert_eq!(image_placement(&hifive).unwrap(), None);
        assert!(image_placement(r#"{"image_placement": 1}"#).is_err());
        let window = |t: &str| crate::ram::board_window(&Board::parse(t).unwrap());
        assert_eq!(window(&virt).unwrap(), (0x8000_0000, 0x100_0000));
        assert!(window(&hifive).unwrap_err().contains("flash image region"));
    }
}
