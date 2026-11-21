//! The MCP tools. Each runs a fixed program with a fixed argument vector on files of the
//! episode directory, with a time limit and an output limit:
//! - nocompiler commands (no `cc`, no `repl`, no `ui`, no `batch`, no `project`);
//! - `link` (src/elf.rs), the file tools (text only, plain names), `run_tests` (the harness);
//! - `check_proof`, not available yet (see STATUS-D R-D1).
//!
//! No tool runs a compiler, a shell or an interpreter on input the agent controls.

use std::io::Read;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{Map, Value, json};
use swe_bin_kernel as k;

use crate::{Config, TaskInfo, elf, subject_file};

/// Text files the agent may write: structured text, Lean, notes, patch sets.
const WRITABLE: &[&str] = &["s", "lean", "txt", "md", "json", "patch"];
const MAX_WRITE: usize = 4 << 20;

pub fn write_exe(p: &Path, b: &[u8]) -> Result<(), String> {
    std::fs::write(p, b).map_err(|e| format!("{}: {e}", p.display()))?;
    std::fs::set_permissions(p, std::fs::Permissions::from_mode(0o755)).map_err(|e| e.to_string())
}

/// A plain file name inside the episode directory: no `/`, no `..`, no leading `.`.
pub fn episode_path(dir: &Path, name: &str) -> Result<PathBuf, String> {
    let ok = !name.is_empty()
        && name.len() <= 128
        && !name.starts_with('.')
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "._-+".contains(c));
    if ok {
        Ok(dir.join(name))
    } else {
        Err(format!(
            "{name:?}: file names are plain names in the episode directory"
        ))
    }
}

pub fn list(dir: &Path) -> Value {
    let mut v: Vec<Value> = Vec::new();
    if let Ok(rd) = std::fs::read_dir(dir) {
        let mut es: Vec<_> = rd.filter_map(|e| e.ok()).collect();
        es.sort_by_key(|e| e.file_name());
        for e in es {
            let n = e.file_name().to_string_lossy().into_owned();
            if n.starts_with('.') {
                continue;
            }
            let len = e.metadata().map(|m| m.len()).unwrap_or(0);
            v.push(json!({ "name": n, "bytes": len }));
        }
    }
    Value::Array(v)
}

/// Run `prog args` in `cwd` with a time limit; stdout and stderr, each cut at `max` bytes.
pub fn run(
    prog: &Path,
    args: &[String],
    cwd: &Path,
    timeout: Duration,
    max: usize,
) -> Result<(i32, String), String> {
    let mut child = Command::new(prog)
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env_remove("LD_PRELOAD")
        .spawn()
        .map_err(|e| format!("{}: {e}", prog.display()))?;
    let take = |r: Option<Box<dyn Read + Send>>| {
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            if let Some(mut r) = r {
                let mut chunk = [0u8; 65536];
                loop {
                    match r.read(&mut chunk) {
                        Ok(0) | Err(_) => break,
                        Ok(n) => {
                            if buf.len() < max {
                                buf.extend_from_slice(&chunk[..n.min(max - buf.len())]);
                            }
                        }
                    }
                }
            }
            buf
        })
    };
    let out = take(
        child
            .stdout
            .take()
            .map(|x| Box::new(x) as Box<dyn Read + Send>),
    );
    let err = take(
        child
            .stderr
            .take()
            .map(|x| Box::new(x) as Box<dyn Read + Send>),
    );
    let start = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(s)) => break Some(s),
            Ok(None) if start.elapsed() > timeout => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(e) => return Err(e.to_string()),
        }
    };
    let mut text = String::from_utf8_lossy(&out.join().unwrap_or_default()).into_owned();
    let e = String::from_utf8_lossy(&err.join().unwrap_or_default()).into_owned();
    if !e.is_empty() {
        text.push_str("\n[stderr]\n");
        text.push_str(&e);
    }
    if text.len() >= max {
        text.push_str(&format!("\n[output cut at {max} bytes]"));
    }
    match status {
        Some(s) => Ok((s.code().unwrap_or(-1), text)),
        None => Err(format!("timed out after {}s\n{text}", timeout.as_secs())),
    }
}

/// The converter's harness (convert/harness.py): JSON with the test results.
pub fn harness(cfg: &Config, task: &str, elfs: &[PathBuf], which: &str) -> Value {
    let mut args = vec![
        cfg.harness.to_string_lossy().into_owned(),
        "run".into(),
        task.into(),
    ];
    args.extend(elfs.iter().map(|p| p.to_string_lossy().into_owned()));
    args.push(format!("--which={which}"));
    match run(&cfg.python, &args, &cfg.swb, cfg.test_timeout, 1 << 22) {
        Ok((_, out)) => {
            let line = out.lines().find(|l| l.starts_with('{')).unwrap_or("");
            serde_json::from_str(line)
                .unwrap_or_else(|_| json!({ "error": out.chars().take(2000).collect::<String>() }))
        }
        Err(e) => json!({ "error": e }),
    }
}

fn s(args: &Map<String, Value>, k: &str) -> Result<String, String> {
    args.get(k)
        .and_then(Value::as_str)
        .map(String::from)
        .ok_or(format!("missing string argument {k:?}"))
}

fn opt(args: &Map<String, Value>, k: &str) -> Option<String> {
    args.get(k).and_then(Value::as_str).map(String::from)
}

fn schema(props: &[(&str, &str)], required: &[&str]) -> Value {
    let mut p = Map::new();
    for (n, d) in props {
        p.insert((*n).into(), json!({ "type": "string", "description": d }));
    }
    json!({ "type": "object", "properties": p, "required": required })
}

/// (name, description, input schema) of every tool.
pub fn specs() -> Vec<(&'static str, &'static str, Value)> {
    let file = ("file", "a file in the episode directory");
    vec![
        (
            "list_files",
            "The files of the episode directory.",
            schema(&[], &[]),
        ),
        (
            "read_file",
            "Read a text file (ISSUE.md, structured text, notes).",
            schema(&[file], &["file"]),
        ),
        (
            "write_file",
            "Write a text file (.s .lean .txt .md .json .patch).",
            schema(&[file, ("content", "the text")], &["file", "content"]),
        ),
        (
            "copy_file",
            "Copy a file (for example a binary before editing it).",
            schema(
                &[("from", "source"), ("to", "destination")],
                &["from", "to"],
            ),
        ),
        (
            "disasm",
            "nocompiler disasm: a function (or `all`) as structured text, which `asm` reads back.",
            schema(
                &[file, ("target", "a symbol, an address, or `all`")],
                &["file"],
            ),
        ),
        (
            "asm",
            "nocompiler asm: structured text to a relocatable object.",
            schema(
                &[file, ("out", "the object to write (.o)")],
                &["file", "out"],
            ),
        ),
        (
            "link",
            "Link an object from `asm` into a binary: its functions replace the binary's functions of the same name (calls go to the new code); new functions are added.",
            schema(
                &[
                    ("binary", "the binary"),
                    ("object", "the object"),
                    ("out", "the binary to write"),
                ],
                &["binary", "object", "out"],
            ),
        ),
        (
            "check",
            "nocompiler check: every function against the profile.",
            schema(&[file], &["file"]),
        ),
        (
            "funcs",
            "nocompiler funcs: the recovered functions.",
            schema(&[file], &["file"]),
        ),
        ("symbols", "nocompiler symbols.", schema(&[file], &["file"])),
        (
            "sections",
            "nocompiler sections.",
            schema(&[file], &["file"]),
        ),
        ("info", "nocompiler info.", schema(&[file], &["file"])),
        ("strings", "nocompiler strings.", schema(&[file], &["file"])),
        ("stats", "nocompiler stats.", schema(&[file], &["file"])),
        (
            "xrefs",
            "nocompiler xrefs: references to or from an address or symbol.",
            schema(
                &[file, ("target", "address or symbol")],
                &["file", "target"],
            ),
        ),
        (
            "decompile",
            "nocompiler decompile: a function as pseudo-C (read only; nothing compiles it).",
            schema(&[file, ("target", "the function")], &["file", "target"]),
        ),
        (
            "diff",
            "nocompiler diff: which functions changed between two binaries.",
            schema(&[file, ("other", "the other binary")], &["file", "other"]),
        ),
        (
            "refine",
            "nocompiler refine: block/loop tree diff of a function in two binaries.",
            schema(
                &[
                    file,
                    ("other", "the other binary"),
                    ("target", "the function"),
                ],
                &["file", "other", "target"],
            ),
        ),
        (
            "emulate",
            "nocompiler emulate: run a function in the interpreter.",
            schema(&[file, ("target", "the function")], &["file", "target"]),
        ),
        (
            "run_tests",
            "Run the tests against the current binaries under qemu. Patch mode: the PASS_TO_PASS tests only (the issue's tests are hidden, as in SWE-bench). Scratch mode: all of them.",
            schema(
                &[(
                    "files",
                    "comma-separated binaries, one per subject (default: the starting names)",
                )],
                &[],
            ),
        ),
        (
            "check_proof",
            "Check a Lean proof for the bonus.",
            schema(&[file], &["file"]),
        ),
    ]
}

fn nc(cfg: &Config, dir: &Path, args: Vec<String>) -> Result<Value, String> {
    let (code, out) = run(
        &cfg.nocompiler,
        &args,
        dir,
        cfg.tool_timeout,
        cfg.max_output,
    )?;
    Ok(json!({ "exit": code, "output": out }))
}

pub fn call(
    cfg: &Config,
    task: &TaskInfo,
    dir: &Path,
    name: &str,
    a: &Map<String, Value>,
) -> Result<Value, String> {
    let f = |k: &str| -> Result<String, String> {
        let n = s(a, k)?;
        episode_path(dir, &n)?;
        Ok(n)
    };
    match name {
        "list_files" => Ok(list(dir)),
        "read_file" => {
            let p = episode_path(dir, &f("file")?)?;
            let b = std::fs::read(&p).map_err(|e| e.to_string())?;
            if b.contains(&0) {
                return Err("a binary file: use the nocompiler tools on it".into());
            }
            let mut t = String::from_utf8_lossy(&b).into_owned();
            if t.len() > cfg.max_output {
                let mut cut = cfg.max_output;
                while !t.is_char_boundary(cut) {
                    cut -= 1;
                }
                t.truncate(cut);
                t.push_str("\n[cut]");
            }
            Ok(Value::String(t))
        }
        "write_file" => {
            let n = f("file")?;
            let ext = n.rsplit('.').next().unwrap_or("");
            if !WRITABLE.contains(&ext) || !n.contains('.') {
                return Err(format!("only text files may be written ({})", WRITABLE.join(" ")));
            }
            let c = s(a, "content")?;
            if c.len() > MAX_WRITE {
                return Err(format!("at most {MAX_WRITE} bytes"));
            }
            std::fs::write(episode_path(dir, &n)?, c).map_err(|e| e.to_string())?;
            Ok(json!({ "written": n }))
        }
        "copy_file" => {
            let (from, to) = (episode_path(dir, &f("from")?)?, episode_path(dir, &f("to")?)?);
            let b = std::fs::read(&from).map_err(|e| e.to_string())?;
            write_exe(&to, &b)?;
            Ok(json!({ "copied": b.len() }))
        }
        "asm" => nc(cfg, dir, vec!["asm".into(), "-o".into(), f("out")?, f("file")?]),
        "link" => {
            let bin = std::fs::read(episode_path(dir, &f("binary")?)?).map_err(|e| e.to_string())?;
            let obj = std::fs::read(episode_path(dir, &f("object")?)?).map_err(|e| e.to_string())?;
            let (img, r) = elf::link(&bin, &obj).map_err(|e| e.to_string())?;
            write_exe(&episode_path(dir, &f("out")?)?, &img)?;
            Ok(json!({ "segment": format!("{:#x}", r.segment.0), "bytes": r.segment.1, "replaced": r.replaced, "added": r.added }))
        }
        "disasm" => {
            let file = f("file")?;
            let target = opt(a, "target").unwrap_or_else(|| "all".into());
            let r = nc(cfg, dir, vec!["disasm".into(), file.clone(), target.clone()])?;
            let listing = r["output"].as_str().is_some_and(|o| o.starts_with("; no structured text"));
            if !listing || target == "all" {
                return Ok(r);
            }
            // nocompiler gives up on the whole binary (R-D1): print the function from a copy in
            // which every other function is `ret`
            let bin = std::fs::read(episode_path(dir, &file)?).map_err(|e| e.to_string())?;
            let Ok(iso) = elf::isolate(&bin, &target) else { return Ok(r) };
            let tmp = dir.join(".isolated.elf");
            write_exe(&tmp, &iso)?;
            let r2 = nc(cfg, dir, vec!["disasm".into(), ".isolated.elf".into(), target])?;
            let _ = std::fs::remove_file(&tmp);
            Ok(r2)
        }
        "check" | "funcs" | "symbols" | "sections" | "info" | "strings" | "stats" => {
            nc(cfg, dir, vec![name.into(), f("file")?])
        }
        "xrefs" | "decompile" | "emulate" => nc(cfg, dir, vec![name.into(), f("file")?, s(a, "target")?]),
        "diff" => nc(cfg, dir, vec!["diff".into(), f("file")?, f("other")?]),
        "refine" => nc(cfg, dir, vec!["refine".into(), f("file")?, f("other")?, s(a, "target")?]),
        "run_tests" => {
            let names: Vec<String> = match opt(a, "files") {
                Some(l) => l.split(',').map(|x| x.trim().to_string()).collect(),
                None => task.subjects.iter().map(|x| subject_file(x)).collect(),
            };
            if names.len() != task.subjects.len() {
                return Err(format!("one binary per subject ({})", task.subjects.join(", ")));
            }
            let mut paths = Vec::new();
            for n in &names {
                let p = episode_path(dir, n)?;
                let b = std::fs::read(&p).map_err(|e| format!("{n}: {e}"))?;
                elf::check_submission(&b).map_err(|e| format!("{n}: {e}"))?;
                paths.push(p);
            }
            let which = match cfg.mode { k::Mode::Patch => "p2p", k::Mode::Scratch => "all" };
            Ok(harness(cfg, &task.id, &paths, which))
        }
        "check_proof" => Err("check_proof is not available yet: nocompiler cannot export these whole Linux \
                              binaries to Lean modules (STATUS-D R-D1), so there is no goal to prove".into()),
        _ => Err(format!("unknown tool {name}")),
    }
}
