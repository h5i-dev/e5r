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
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::board::Board;
use crate::sha256;

pub const JOB_SCHEMA: &str = "e5r.verify.job.v1";
pub const RESULT_SCHEMA: &str = "e5r.verify.result.v1";

/// Axioms a checked theorem may depend on: Lean's standard ones.
pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

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
#[derive(Clone, Copy, Debug, Default, Deserialize, PartialEq, Eq)]
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
    Exhausted(String),
    Error(String),
}

impl Stop {
    fn status(&self) -> &'static str {
        match self {
            Stop::Failed(_) => "failed",
            Stop::Unsupported(_) => "unsupported",
            Stop::Exhausted(_) => "resource_exhausted",
            Stop::Error(_) => "error",
        }
    }
    fn message(&self) -> &str {
        match self {
            Stop::Failed(m) | Stop::Unsupported(m) | Stop::Exhausted(m) | Stop::Error(m) => m,
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

/// A child process under the job's limits. The memory limit is enforced by
/// sampling resident memory through /proc, because Lean reserves far more
/// virtual memory than it uses, which rules out RLIMIT_AS.
fn run_limited(mut cmd: Command, limits: &Limits, what: &str) -> Result<(String, u64), Stop> {
    let out_path = std::env::temp_dir().join(format!(
        "e5r-verify-{}-{}.log",
        std::process::id(),
        what.replace(['/', ' '], "_")
    ));
    let out = std::fs::File::create(&out_path).map_err(err("log file"))?;
    let child = cmd
        .stdout(Stdio::from(out.try_clone().map_err(err("log file"))?))
        .stderr(Stdio::from(out))
        .spawn();
    let mut child = child.map_err(|e| Stop::Error(format!("{what}: cannot start: {e}")))?;
    let start = Instant::now();
    let mut peak = 0u64;
    let status = loop {
        if let Some(status) = child.try_wait().map_err(err(what))? {
            break status;
        }
        if let Ok(s) = std::fs::read_to_string(format!("/proc/{}/status", child.id())) {
            if let Some(kb) = s
                .lines()
                .find_map(|l| l.strip_prefix("VmRSS:"))
                .and_then(|v| v.trim().trim_end_matches(" kB").trim().parse::<u64>().ok())
            {
                peak = peak.max(kb / 1024);
            }
        }
        let over_time = start.elapsed() > Duration::from_secs(limits.seconds);
        if peak > limits.rss_mib || over_time {
            let _ = child.kill();
            let _ = child.wait();
            let _ = std::fs::remove_file(&out_path);
            return Err(Stop::Exhausted(if over_time {
                format!("{what}: exceeded {} s", limits.seconds)
            } else {
                format!("{what}: exceeded {} MiB resident", limits.rss_mib)
            }));
        }
        std::thread::sleep(Duration::from_millis(100));
    };
    let text = std::fs::read_to_string(&out_path).unwrap_or_default();
    let _ = std::fs::remove_file(&out_path);
    if !status.success() {
        return Err(Stop::Failed(format!(
            "{what}: exited with {status}\n{}",
            tail(&text)
        )));
    }
    Ok((text, peak))
}

fn tail(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    lines[lines.len().saturating_sub(40)..].join("\n")
}

/// Strip Lean comments and string literals, so a scan for forbidden
/// commands only sees code.
pub fn lean_code(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    let mut depth = 0usize;
    while i < b.len() {
        if depth > 0 {
            if b[i..].starts_with(b"/-") {
                depth += 1;
                i += 2;
            } else if b[i..].starts_with(b"-/") {
                depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        if b[i..].starts_with(b"/-") {
            depth = 1;
            i += 2;
        } else if b[i..].starts_with(b"--") {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else if b[i] == b'\''
            && (i == 0
                || !(b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_' || b[i - 1] == b'\''))
            && (b.get(i + 2) == Some(&b'\'')
                || (b.get(i + 1) == Some(&b'\\') && b.get(i + 3) == Some(&b'\'')))
        {
            // A character literal such as '"' or '\n': skip it whole.
            i += if b[i + 1] == b'\\' { 4 } else { 3 };
            out.push_str("' '");
        } else if b[i] == b'"' {
            i += 1;
            while i < b.len() && b[i] != b'"' {
                if b[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            i += 1;
            out.push_str("\"\"");
        } else {
            out.push(b[i] as char);
            i += 1;
        }
    }
    out
}

/// Commands and attributes that would let a proof bypass the kernel or add
/// assumptions. Their presence anywhere in a checked module is an error.
///
/// Metaprogramming is banned outright: a `run_cmd` can call the
/// environment's `addDecl` with kernel checking switched off through an
/// option name assembled from strings, which no word scan can see. The
/// kernel replay stage (`leanchecker`) is the check that does not depend on
/// this list.
pub const FORBIDDEN: [&str; 23] = [
    "sorry",
    "admit",
    "axiom",
    "native_decide",
    "ofReduceBool",
    "implemented_by",
    "extern",
    "unsafe",
    "opaque",
    "skipKernelTC",
    "trustCompiler",
    "run_cmd",
    "run_elab",
    "run_meta",
    "#eval",
    "elab",
    "elab_rules",
    "macro",
    "macro_rules",
    "syntax",
    "initialize",
    "builtin_initialize",
    "addDecl",
];

pub fn escapes(code: &str) -> Vec<&'static str> {
    let words: Vec<&str> = code
        .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '#'))
        .flat_map(|w| w.split('.'))
        .collect();
    FORBIDDEN
        .iter()
        .copied()
        .filter(|f| words.contains(f))
        .collect()
}

/// Parse `#print axioms` output: every theorem's axioms, or an error naming
/// the line that could not be understood.
pub fn parse_axioms(out: &str) -> Result<BTreeMap<String, Vec<String>>, String> {
    let mut map = BTreeMap::new();
    for line in out.lines().filter(|l| !l.trim().is_empty()) {
        // Split at the whole marker, not at the first quote: Lean names may
        // end in apostrophes (`recv_step'`).
        if let Some(rest) = line.strip_prefix('\'') {
            if let Some(name) = rest.strip_suffix("' does not depend on any axioms") {
                map.insert(name.to_string(), vec![]);
                continue;
            }
            if let Some((name, list)) = rest
                .split_once("' depends on axioms: [")
                .and_then(|(n, t)| Some((n, t.strip_suffix(']')?)))
            {
                map.insert(
                    name.to_string(),
                    list.split(", ").map(str::to_string).collect(),
                );
                continue;
            }
        }
        return Err(format!("unexpected Lean output: {line}"));
    }
    Ok(map)
}

/// Fully qualified names of the theorems a module declares, following
/// `namespace`/`end` (enough for this project's sources, which do not use
/// `section` names or nested `namespace` blocks with the same name).
pub fn declared_theorems(code: &str) -> Vec<String> {
    let mut stack: Vec<String> = Vec::new();
    let mut out = Vec::new();
    for line in code.lines() {
        // Attributes and modifiers may precede `theorem` on its line.
        let mut rest = line.trim_start();
        while let Some(r) = rest.strip_prefix("@[") {
            rest = r.split_once(']').map_or("", |(_, t)| t).trim_start();
        }
        for m in ["private ", "protected ", "noncomputable ", "nonrec "] {
            rest = rest.strip_prefix(m).unwrap_or(rest).trim_start();
        }
        let mut words = rest.split_whitespace();
        match (words.next(), words.next()) {
            (Some("namespace"), Some(ns)) => stack.push(ns.to_string()),
            (Some("end"), Some(ns)) if stack.last().is_some_and(|l| l == ns) => {
                stack.pop();
            }
            (Some("theorem"), Some(name)) => {
                let mut full = stack.clone();
                full.push(name.to_string());
                out.push(full.join("."));
            }
            _ => {}
        }
    }
    out
}

fn tool_version(argv: &[&str]) -> Option<String> {
    let out = Command::new(argv[0]).args(&argv[1..]).output().ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    s.lines().next().map(|l| l.trim().to_string())
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
    let exe = std::env::current_exe()
        .ok()
        .and_then(|p| std::fs::read(p).ok())
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
    Ok(json!({
        "image": image,
        "job_sha256": sha256::hex(&read(&paths.job)?),
        "board_sha256": sha256::hex(&read(&paths.root.join(&job.board))?),
        "elf": { "path": job.elf, "sha256": sha256::hex(&elf), "bytes": elf.len() },
        "sources": sources,
        "lean": tool_version(&["lean", "--version"]),
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
        let limits = &job.limits;
        // Build the ELF from source, if the job says how.
        for (i, step) in job.build.iter().enumerate() {
            let t = Instant::now();
            let mut cmd = Command::new(&step.argv[0]);
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
        if let Some(pin) = &job.elf_sha256 {
            if *pin != digest {
                return Err(Stop::Error(format!(
                    "ELF identity changed ({digest}, job pins {pin}); review the new bytes and update elf_sha256"
                )));
            }
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
        let regen = Command::new("python3")
            .arg(paths.root.join("tools/gen_board.py"))
            .arg("--check")
            .arg(paths.root.join(&job.board))
            .output()
            .map_err(err("gen_board"))?;
        if !regen.status.success() {
            return Err(Stop::Error(format!(
                "Theories/Board/{board_mod}.lean is stale: {}",
                String::from_utf8_lossy(&regen.stderr).trim()
            )));
        }
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
                    "-- Generated by e5r-verify check; regenerate, do not edit.\n\
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
        let before = identity(&job, &paths)?;
        let manifest_path = paths
            .root
            .join(format!("build/jobs/{}/stages.json", job.id));
        let mut manifest: BTreeMap<String, String> = std::fs::read_to_string(&manifest_path)
            .ok()
            .and_then(|t| serde_json::from_str(&t).ok())
            .unwrap_or_default();
        let mut chain = sha256::hex(
            tool_version(&["lean", "--version"])
                .unwrap_or_default()
                .as_bytes(),
        );
        for m in &order {
            let src = std::fs::read(paths.root.join(m)).map_err(err(m))?;
            chain = sha256::hex(format!("{chain} {m} {}", sha256::hex(&src)).as_bytes());
            let t = Instant::now();
            let olean = Path::new(m).with_extension("olean");
            if resume && manifest.get(m) == Some(&chain) && paths.root.join(&olean).exists() {
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
            manifest.insert(m.clone(), chain.clone());
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
            let mut cmd = Command::new("leanchecker");
            cmd.current_dir(&paths.root)
                .env("LEAN_PATH", ".")
                .arg(m.trim_end_matches(".lean").replace('/', "."));
            let (_, rss) = run_limited(cmd, limits, &format!("leanchecker {m}"))?;
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
        let imports: Vec<String> = order
            .iter()
            .map(|m| format!("import {}", m.trim_end_matches(".lean").replace('/', ".")))
            .collect();
        let audit = format!(
            "{}\n{}\n",
            imports.join("\n"),
            names
                .iter()
                .map(|n| format!("#print axioms {n}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        let audit_path = format!("Audit_{}.lean", job.id.replace('-', "_"));
        std::fs::write(paths.root.join(&audit_path), audit).map_err(err("audit"))?;
        let mut cmd = Command::new("lean");
        cmd.current_dir(&paths.root)
            .env("LEAN_PATH", ".")
            .arg("-j1")
            .arg(&audit_path);
        let audited = run_limited(cmd, limits, "axiom audit");
        let _ = std::fs::remove_file(paths.root.join(&audit_path));
        // The audit only prints; if it fails, a named theorem does not exist.
        let (out, _) = audited.map_err(|s| match s {
            Stop::Failed(m) => Stop::Error(m),
            other => other,
        })?;
        let axioms = parse_axioms(&out).map_err(Stop::Error)?;
        let mut theorems = Vec::new();
        for n in &names {
            let used = axioms
                .get(n)
                .ok_or_else(|| Stop::Error(format!("no axiom report for {n}")))?;
            let bad: Vec<&String> = used
                .iter()
                .filter(|a| !ALLOWED_AXIOMS.contains(&a.as_str()))
                .collect();
            if !bad.is_empty() {
                return Err(Stop::Failed(format!(
                    "{n} depends on disallowed axioms {bad:?}"
                )));
            }
            theorems.push(json!({ "name": n, "axioms": used }));
        }
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
            result["status"] = json!(stop.status());
            result["message"] = json!(stop.message());
            if let Ok((job, paths)) = Job::load(job_path) {
                if let Ok(ident) = identity(&job, &paths) {
                    result["inputs"] = ident;
                }
            }
        }
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
         for m in {mods}; do\n  LEAN_PATH=. lean -j1 -o \"${{m%.lean}}.olean\" \"$m\"\ndone\n\
         LEAN_PATH=. lean -j1 Audit.lean > axioms.actual\n\
         diff axioms.expected axioms.actual\n\
         echo \"recheck: every theorem checked, with exactly the recorded axioms\"\n",
        mods = modules.join(" ")
    );
    for (name, text) in [
        ("Audit.lean", audit),
        ("axioms.expected", expected),
        ("recheck.sh", script),
        ("SHA256SUMS", sums),
        (
            "result.json",
            serde_json::to_string_pretty(&result).unwrap() + "\n",
        ),
    ] {
        std::fs::write(out.join(name), text).map_err(|e| format!("{name}: {e}"))?;
    }
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
