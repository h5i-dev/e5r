//! Shared fail-closed proof policy and replay, independent of any ISA.
use super::process::{self, Limits, Run};
use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
pub fn axioms_allowed(axioms: &[String]) -> bool {
    axioms.iter().all(|a| ALLOWED_AXIOMS.contains(&a.as_str()))
}
/// Recheck all declarations in a compiled module using Lean's independent kernel.
/// Import and proposition policy are separate obligations of the caller.
pub enum SearchPath<'a> {
    Direct(&'a str),
    Lake(&'a Path),
}
pub fn replay(
    root: &Path,
    search_path: SearchPath<'_>,
    module: &str,
    limits: Limits,
) -> Result<Run, String> {
    let mut cmd;
    match search_path {
        SearchPath::Direct(path) => {
            cmd = Command::new("leanchecker");
            cmd.current_dir(root).env("LEAN_PATH", path).arg(module);
        }
        SearchPath::Lake(extra) => {
            cmd = Command::new("lake");
            cmd.current_dir(root).env("E5R_REPLAY_DIR", extra).env("E5R_REPLAY_MODULE", module)
                .args(["env", "sh", "-c", "cd \"$E5R_REPLAY_DIR\" && LEAN_PATH=\"$LEAN_PATH:$E5R_REPLAY_DIR\" leanchecker \"$E5R_REPLAY_MODULE\""]);
        }
    }
    process::run(cmd, limits)
}

/// Parse an executable checker's final report only after successful execution.
pub fn checker_report(run: &Run) -> Result<serde_json::Value, String> {
    if !run.success || run.exhaustion.is_some() {
        return Err(format!(
            "checker execution failed: {:?}: {}",
            run.exhaustion, run.output
        ));
    }
    let line = run
        .output
        .lines()
        .last()
        .ok_or("checker emitted no report")?;
    let report: serde_json::Value =
        serde_json::from_str(line).map_err(|e| format!("invalid checker report: {e}"))?;
    if report["ok"] != true {
        return Err(format!("checker refused: {report}"));
    }
    Ok(report)
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

/// One report, used by generated PTX proof/refutation modules.
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn success_json_cannot_override_failed_process() {
        let r = Run {
            success: false,
            cancelled: false,
            cleanup_complete: true,
            code: Some(1),
            exhaustion: None,
            output: "{\"ok\":true}".into(),
            seconds: 0.0,
            peak_rss_mib: 0,
            memory_monitor: "test",
        };
        assert!(checker_report(&r).is_err());
    }
    #[test]
    fn only_standard_axioms_are_accepted() {
        assert!(axioms_allowed(&ALLOWED_AXIOMS.map(String::from)));
        for a in [
            "sorryAx",
            "Lean.ofReduceBool",
            "Lean.trustCompiler",
            "cheat",
        ] {
            assert!(!axioms_allowed(&[a.into()]));
        }
    }
}
