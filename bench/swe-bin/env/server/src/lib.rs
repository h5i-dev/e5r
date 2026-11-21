//! swe-bin as a senv environment: SWE-bench Multilingual C/Rust tasks where the agent fixes the
//! issue by editing the binary.
//!
//! Every reward and `done` is decided by `swe-bin-kernel` (pure, extracted to Lean, proved in
//! `../proofs`). This crate is the trusted shell around it:
//! - it sets up an episode directory with the starting binary (`reset`);
//! - it runs the tools on files in that directory: nocompiler commands, `link`, and file
//!   reading and writing (text only);
//! - it runs the tests (the converter's harness, under qemu) and reports them to the kernel
//!   (`RecordTests`) before `Submit`.
//!
//! No tool runs a compiler, a shell or an interpreter that the agent controls. Commands are
//! fixed argument vectors over file names that must be plain names inside the episode directory.
//! Every tool has a time limit and an output limit.

pub mod elf;
pub mod tools;

use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use senv::{
    Environment, Kernel, Metadata, Observation, Phase, Reward, TenantId, Tool, ToolError, WireError,
};
use serde_json::{Map, Value, json};
use swe_bin_kernel as k;

/// Server configuration, set once in `main` (the h5i-app `Kernel` trait has no `self`).
pub struct Config {
    pub swb: PathBuf,
    pub tasks_dir: PathBuf,
    pub dataset: PathBuf,
    pub episodes: PathBuf,
    pub nocompiler: PathBuf,
    pub python: PathBuf,
    pub harness: PathBuf,
    pub mode: k::Mode,
    pub tool_timeout: Duration,
    pub test_timeout: Duration,
    pub max_output: usize,
    pub tasks: Vec<TaskInfo>,
}

#[derive(Clone, Debug)]
pub struct TaskInfo {
    pub id: String,
    pub subjects: Vec<String>,
    /// The base ELFs (patch mode starts from them), absolute.
    pub base: Vec<PathBuf>,
    pub f2p: u32,
    pub p2p: u32,
    pub issue: String,
    /// Scratch mode: the functions each subject has removed.
    pub removes: Vec<Vec<String>>,
    /// Scratch mode: what the agent is told about them (FUNCTIONS.md) and the tests (TESTS.patch).
    pub functions_md: String,
    pub test_patch: String,
}

static CONFIG: OnceLock<Arc<Config>> = OnceLock::new();

pub fn configure(c: Config) -> Result<(), String> {
    CONFIG
        .set(Arc::new(c))
        .map_err(|_| "configured twice".to_string())
}

pub fn config() -> Option<Arc<Config>> {
    CONFIG.get().cloned()
}

/// Load the kept tasks (`tasks/*.json` with "status": "kept"), in name order.
pub fn load_tasks(tasks_dir: &Path, swb: &Path, dataset: &Path) -> Result<Vec<TaskInfo>, String> {
    let mut issues = std::collections::HashMap::new();
    let mut test_patches = std::collections::HashMap::new();
    let ds = std::fs::read_to_string(dataset).map_err(|e| format!("{}: {e}", dataset.display()))?;
    for line in ds.lines() {
        let Ok(v) = serde_json::from_str::<Value>(line) else {
            continue;
        };
        if let (Some(i), Some(p)) = (v["instance_id"].as_str(), v["problem_statement"].as_str()) {
            issues.insert(i.to_string(), p.to_string());
            test_patches.insert(
                i.to_string(),
                v["test_patch"].as_str().unwrap_or_default().to_string(),
            );
        }
    }
    let mut names: Vec<PathBuf> = std::fs::read_dir(tasks_dir)
        .map_err(|e| format!("{}: {e}", tasks_dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    names.sort();
    let mut out = Vec::new();
    for p in names {
        let v: Value =
            serde_json::from_str(&std::fs::read_to_string(&p).map_err(|e| e.to_string())?)
                .map_err(|e| format!("{}: {e}", p.display()))?;
        if v["status"] != "kept" {
            continue;
        }
        let id = v["instance_id"].as_str().unwrap_or_default().to_string();
        let tests = v["tests"].as_array().cloned().unwrap_or_default();
        let count = |kind: &str| tests.iter().filter(|t| t["kind"] == kind).count() as u32;
        let bins = v["binaries"].as_array().cloned().unwrap_or_default();
        let mut md = String::from(
            "# The functions to write\n\nScratch mode (SWE-bench-derived, function-level from-scratch): each function below was removed from the binary (it now exits with status 127). Write it as nocompiler structured text, `asm` it, and `link` it into the binary. The source of these functions is not given.\n",
        );
        for b in &bins {
            md.push_str(&format!(
                "\n## {}\n",
                subject_file(b["subject"].as_str().unwrap_or_default())
            ));
            for f in b["scratch"]["functions"]
                .as_array()
                .cloned()
                .unwrap_or_default()
            {
                md.push_str(&format!(
                    "\n- `{}`: {} instructions in the original build\n  - signature: {}\n  - called by: {}\n",
                    f["name"].as_str().unwrap_or_default(),
                    f["instructions"].as_u64().map_or("?".into(), |n| n.to_string()),
                    f["signature"].as_str().unwrap_or("(no debug information)"),
                    f["callers"].as_array().map(|c| c.iter().filter_map(|x| x.as_str()).collect::<Vec<_>>().join(", ")).unwrap_or_default(),
                ));
            }
            let data = b["scratch"]["data_to_write"]
                .as_array()
                .cloned()
                .unwrap_or_default();
            if !data.is_empty() {
                md.push_str(&format!(
                    "\nData the fixed program also changes: {}\n",
                    data.iter()
                        .filter_map(|x| x.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }
        out.push(TaskInfo {
            functions_md: md,
            test_patch: test_patches.get(&id).cloned().unwrap_or_default(),
            issue: issues.get(&id).cloned().unwrap_or_default(),
            id,
            subjects: bins
                .iter()
                .map(|b| b["subject"].as_str().unwrap_or_default().to_string())
                .collect(),
            base: bins
                .iter()
                .map(|b| swb.join(b["base"]["path"].as_str().unwrap_or_default()))
                .collect(),
            f2p: count("FAIL_TO_PASS"),
            p2p: count("PASS_TO_PASS"),
            removes: bins
                .iter()
                .map(|b| {
                    b["scratch"]["removes"]
                        .as_array()
                        .cloned()
                        .unwrap_or_default()
                        .iter()
                        .filter_map(|x| x.as_str().map(String::from))
                        .collect()
                })
                .collect(),
        });
    }
    Ok(out)
}

/// The file name a subject has in the episode directory: `src/redis-server` -> `redis-server.elf`.
pub fn subject_file(subject: &str) -> String {
    format!("{}.elf", subject.rsplit('/').next().unwrap_or(subject))
}

// ---- the shell's kernel ------------------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Episode {
    pub episode_id: String,
    pub dir: String,
    pub task: Option<usize>,
    pub step_count: u64,
    pub last_tests: Option<Value>,
    pub message: String,
    pub core: k::Snapshot,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    Reset {
        seed: Option<i64>,
        episode_id: String,
    },
    Tool {
        name: String,
        args: Map<String, Value>,
    },
    Submit {
        files: Vec<String>,
    },
    ListTools,
    State,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Reply {
    Step,
    Tool {
        name: String,
        result: Result<Value, String>,
    },
    Tools,
    State,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Kernel(k::Error),
    Setup(String),
    NotReset,
}

pub struct SweBin;

fn core(s: &k::Snapshot, c: k::Command) -> Result<k::Snapshot, Error> {
    let (w, _) = k::transition(&(), s, &c).map_err(Error::Kernel)?;
    Ok(k::apply(s, &w))
}

fn hash_of(bytes: &[&[u8]]) -> ([u8; 32], k::Hash) {
    use sha2::{Digest, Sha256};
    let digest: [u8; 32] = if bytes.len() == 1 {
        Sha256::digest(bytes[0]).into()
    } else {
        // several subjects: the SHA-256 of their SHA-256s, in subject order
        let mut h = Sha256::new();
        for b in bytes {
            h.update(Sha256::digest(b));
        }
        h.finalize().into()
    };
    let mut w = [0u64; 4];
    for (i, x) in w.iter_mut().enumerate() {
        let mut b = [0u8; 8];
        b.copy_from_slice(&digest[8 * i..8 * i + 8]);
        *x = u64::from_be_bytes(b);
    }
    (digest, k::Hash { w })
}

pub fn hex(d: &[u8]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

fn safe_id(id: &str) -> String {
    let ok = !id.is_empty()
        && id.len() <= 64
        && id
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
    if ok {
        id.to_string()
    } else {
        let (d, _) = hash_of(&[id.as_bytes()]);
        hex(&d[..16])
    }
}

fn reset(cfg: &Config, seed: Option<i64>, episode_id: &str) -> Result<Episode, Error> {
    if cfg.tasks.is_empty() {
        return Err(Error::Setup("no kept tasks".into()));
    }
    let idx = seed.unwrap_or(0).rem_euclid(cfg.tasks.len() as i64) as usize;
    let t = &cfg.tasks[idx];
    let dir = cfg.episodes.join(safe_id(episode_id));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).map_err(|e| Error::Setup(format!("{}: {e}", dir.display())))?;
    for (i, s) in t.subjects.iter().enumerate() {
        let bin = std::fs::read(&t.base[i])
            .map_err(|e| Error::Setup(format!("{}: {e}", t.base[i].display())))?;
        let start = match cfg.mode {
            k::Mode::Patch => bin,
            k::Mode::Scratch if t.removes[i].is_empty() => bin,
            k::Mode::Scratch => {
                elf::stub(&bin, &t.removes[i])
                    .map_err(|e| Error::Setup(e.to_string()))?
                    .0
            }
        };
        tools::write_exe(&dir.join(subject_file(s)), &start).map_err(Error::Setup)?;
    }
    std::fs::write(dir.join("ISSUE.md"), &t.issue).map_err(|e| Error::Setup(e.to_string()))?;
    if cfg.mode == k::Mode::Scratch {
        // scratch mode gives the tests and the removed functions' interfaces
        std::fs::write(dir.join("TESTS.patch"), &t.test_patch)
            .map_err(|e| Error::Setup(e.to_string()))?;
        std::fs::write(dir.join("FUNCTIONS.md"), &t.functions_md)
            .map_err(|e| Error::Setup(e.to_string()))?;
    }
    let task = k::Task {
        id: idx as u32,
        mode: cfg.mode,
        f2p: t.f2p,
        p2p: t.p2p,
    };
    let core = core(&k::initial(), k::Command::Reset { task })?;
    Ok(Episode {
        episode_id: episode_id.to_string(),
        dir: dir.to_string_lossy().into_owned(),
        task: Some(idx),
        step_count: 0,
        last_tests: None,
        message: format!(
            "task {} ({:?} mode): fix the issue in ISSUE.md by editing {}",
            t.id,
            cfg.mode,
            t.subjects
                .iter()
                .map(|s| subject_file(s))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        core,
    })
}

fn submit(cfg: &Config, s: &Episode, files: &[String]) -> Result<Episode, Error> {
    let Some(idx) = s.task else {
        return Err(Error::NotReset);
    };
    let t = &cfg.tasks[idx];
    let dir = PathBuf::from(&s.dir);
    let files: Vec<String> = if files.is_empty() {
        t.subjects.iter().map(|x| subject_file(x)).collect()
    } else {
        files.to_vec()
    };
    let mut next = s.clone();
    next.step_count += 1;
    let mut bins = Vec::new();
    let mut problem = None;
    if files.len() != t.subjects.len() {
        problem = Some(format!(
            "submit {} files, one per subject ({})",
            t.subjects.len(),
            t.subjects.join(", ")
        ));
    }
    for f in &files {
        match tools::episode_path(&dir, f)
            .and_then(|p| std::fs::read(&p).map_err(|e| format!("{f}: {e}")))
        {
            Ok(b) => {
                if let Err(e) = elf::check_submission(&b) {
                    problem.get_or_insert(format!("{f}: {e}"));
                }
                bins.push(b);
            }
            Err(e) => {
                problem.get_or_insert(e);
            }
        }
    }
    let refs: Vec<&[u8]> = bins.iter().map(|b| b.as_slice()).collect();
    let (digest, h) = hash_of(&refs);
    // a submission that is not a set of RV64 executables runs no test: it is reported as
    // nothing passing, for its hash
    let (f2p_passed, p2p_passed, report) = match problem {
        Some(p) => (0, 0, json!({ "error": p })),
        None => {
            // freeze the submitted bytes: the tests run on these copies
            let sub = dir.join(".submitted");
            let _ = std::fs::create_dir_all(&sub);
            let mut paths = Vec::new();
            for (i, b) in bins.iter().enumerate() {
                let p = sub.join(format!("{i}.elf"));
                let _ = tools::write_exe(&p, b);
                paths.push(p);
            }
            let r = tools::harness(cfg, &t.id, &paths, "all");
            let get = |k: &str| r.get(k).and_then(Value::as_u64).unwrap_or(0) as u32;
            (
                get("f2p_passed").min(t.f2p),
                get("p2p_passed").min(t.p2p),
                r,
            )
        }
    };
    let core1 = core(
        &s.core,
        k::Command::RecordTests {
            tests: k::Tests {
                binary: h,
                f2p_passed,
                p2p_passed,
            },
        },
    )?;
    next.core = core(&core1, k::Command::Submit { binary: h })?;
    next.message = format!(
        "submitted {} (sha256 {}): FAIL_TO_PASS {f2p_passed}/{}, PASS_TO_PASS {p2p_passed}/{}",
        files.join(", "),
        hex(&digest),
        t.f2p,
        t.p2p
    );
    next.last_tests = Some(report);
    Ok(next)
}

impl Kernel for SweBin {
    type Principal = ();
    type Snapshot = Episode;
    type Command = Command;
    type WriteSet = Option<Episode>;
    type Reply = Reply;
    type Error = Error;

    fn tenant(_: &()) -> TenantId {
        TenantId(1)
    }

    fn transition(_: &(), s: &Episode, c: &Command) -> Result<(Option<Episode>, Reply), Error> {
        let Some(cfg) = config() else {
            return Err(Error::Setup("not configured".into()));
        };
        match c {
            Command::Reset { seed, episode_id } => {
                Ok((Some(reset(&cfg, *seed, episode_id)?), Reply::Step))
            }
            Command::Submit { files } => {
                if s.core.done {
                    return Err(Error::Kernel(k::Error::Done));
                }
                Ok((Some(submit(&cfg, s, files)?), Reply::Step))
            }
            Command::Tool { name, args } => {
                let Some(idx) = s.task else {
                    return Err(Error::NotReset);
                };
                if s.core.done {
                    return Err(Error::Kernel(k::Error::Done));
                }
                let r = tools::call(&cfg, &cfg.tasks[idx], Path::new(&s.dir), name, args);
                Ok((
                    None,
                    Reply::Tool {
                        name: name.clone(),
                        result: r,
                    },
                ))
            }
            Command::ListTools => Ok((None, Reply::Tools)),
            Command::State => Ok((None, Reply::State)),
        }
    }

    fn apply(s: &Episode, w: &Option<Episode>) -> Episode {
        match w {
            Some(n) => n.clone(),
            None => s.clone(),
        }
    }

    fn read_only(c: &Command) -> bool {
        matches!(c, Command::State | Command::ListTools)
    }
}

// ---- the OpenEnv surface -----------------------------------------------------------------------

pub struct SweBinEnv;

impl Environment for SweBinEnv {
    type Kernel = SweBin;

    fn metadata(&self) -> Metadata {
        Metadata::new(
            "swe-bin",
            "SWE-bench Multilingual (C, Rust) on static riscv64 binaries: fix the issue by editing the \
             binary with nocompiler's tools; reward 1000 when every FAIL_TO_PASS and PASS_TO_PASS test \
             passes against the submitted binary under qemu. Scratch mode is SWE-bench-derived \
             (function-level from-scratch), not SWE-bench.",
        )
        .version(env!("CARGO_PKG_VERSION"))
    }

    fn principal(&self) {}

    fn initial(&self, episode_id: &str) -> Episode {
        Episode {
            episode_id: episode_id.to_string(),
            ..Episode::default()
        }
    }

    fn reset(&self, seed: Option<i64>, episode_id: String) -> Command {
        Command::Reset { seed, episode_id }
    }

    /// Step actions: `{"submit": ["jq.elf"]}` (or a single name, or `[]` for the starting file
    /// names), which ends the episode; and OpenEnv's `call_tool` / `list_tools` payloads, which
    /// is how `MCPToolClient` reaches the tools over the WebSocket.
    fn step(&self, action: &Map<String, Value>) -> Result<Command, WireError> {
        match action.get("type").and_then(Value::as_str) {
            Some("call_tool") => {
                senv::wire::reject_unknown(
                    action,
                    &["type", "tool_name", "arguments", "metadata"],
                )?;
                let name = action
                    .get("tool_name")
                    .and_then(Value::as_str)
                    .ok_or_else(|| WireError::validation("tool_name must be a string"))?;
                let args = match action.get("arguments") {
                    None => Map::new(),
                    Some(Value::Object(m)) => m.clone(),
                    Some(_) => return Err(WireError::validation("arguments must be an object")),
                };
                return Ok(Command::Tool {
                    name: name.to_string(),
                    args,
                });
            }
            Some("list_tools") => return Ok(Command::ListTools),
            _ => {}
        }
        senv::wire::reject_unknown(action, &["submit", "metadata"])?;
        match action.get("submit") {
            Some(Value::String(f)) => Ok(Command::Submit {
                files: vec![f.clone()],
            }),
            Some(Value::Array(a)) => Ok(Command::Submit {
                files: a
                    .iter()
                    .filter_map(|x| x.as_str().map(String::from))
                    .collect(),
            }),
            _ => Err(WireError::validation(
                "the step action is {\"submit\": [FILE, ...]}; everything else is an MCP tool",
            )),
        }
    }

    fn state(&self) -> Command {
        Command::State
    }

    fn observe(&self, _: Phase, s: &Episode, reply: &Reply) -> Observation {
        let reward = Reward::Milli(s.core.reward_milli as i64);
        match reply {
            Reply::Tool {
                name,
                result: Ok(v),
            } => {
                let text = match v {
                    Value::String(t) => t.clone(),
                    o => o.to_string(),
                };
                return Observation::new(
                    json!({
                        "metadata": {}, "tool_name": name, "error": null,
                        "result": { "content": [{ "type": "text", "text": text }],
                                    "structured_content": { "result": v }, "meta": null, "data": v, "is_error": false },
                    }),
                    reward,
                    s.core.done,
                );
            }
            Reply::Tool {
                name,
                result: Err(m),
            } => {
                return Observation::new(
                    json!({
                        "metadata": {}, "tool_name": name, "result": null,
                        "error": { "error_type": "execution_error", "message": m },
                    }),
                    reward,
                    s.core.done,
                );
            }
            Reply::Tools => {
                let ts: Vec<Value> = tools::specs()
                    .into_iter()
                    .map(|(n, d, sc)| json!({ "name": n, "description": d, "input_schema": sc }))
                    .collect();
                return Observation::new(
                    json!({ "metadata": {}, "tools": ts }),
                    reward,
                    s.core.done,
                );
            }
            _ => {}
        }
        Observation::new(
            json!({
                "message": s.message,
                "task": s.task.and_then(|i| config().map(|c| c.tasks[i].id.clone())),
                "mode": format!("{:?}", s.core.task.mode),
                "files": tools::list(Path::new(&s.dir)),
                "tests": s.last_tests,
            }),
            reward,
            s.core.done,
        )
    }

    fn render_state(&self, s: &Episode, _: &Reply) -> Value {
        json!({ "episode_id": s.episode_id, "step_count": s.step_count })
    }

    fn refuse(&self, e: &Error) -> WireError {
        match e {
            Error::Kernel(k::Error::Done) => WireError::execution("the episode has ended"),
            Error::Kernel(x) => WireError::execution(format!("refused: {x:?}")),
            Error::Setup(m) => WireError::execution(m.clone()),
            Error::NotReset => WireError::execution("reset first"),
        }
    }

    fn tools(&self) -> Vec<Tool> {
        tools::specs()
            .into_iter()
            .map(|(n, d, schema)| Tool::new(n, d, schema))
            .collect()
    }

    fn call_tool(&self, name: &str, arguments: &Map<String, Value>) -> Option<Command> {
        if tools::specs().iter().any(|(n, _, _)| *n == name) {
            Some(Command::Tool {
                name: name.to_string(),
                args: arguments.clone(),
            })
        } else {
            None
        }
    }

    fn tool_result(&self, _: &Episode, reply: &Reply) -> Result<Value, ToolError> {
        match reply {
            Reply::Tool { result: Ok(v), .. } => Ok(v.clone()),
            Reply::Tool { result: Err(e), .. } => Err(ToolError::Execution(e.clone())),
            _ => Err(ToolError::Execution("not a tool call".into())),
        }
    }
}
