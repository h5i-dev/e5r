//! The annotation command: writing to the log and reading it back.
//!
//! This is where the analysis side and the storage side meet. Anchors are
//! built from a fresh analysis, so a log written against one build applies to
//! the next one without anything being rewritten.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use e5r_analysis::Program;
use e5r_core::Addr;
use e5r_db::{Anchor, AnchorIndex, Field, Log, Resolution};

use crate::addr;
use crate::exit;
use crate::out::{Out, outln};

/// Where the log for a binary lives by default.
pub fn default_path(binary: &Path) -> PathBuf {
    let mut p = binary.to_path_buf();
    let name = p
        .file_name()
        .map(|n| format!("{}.e5r", n.to_string_lossy()))
        .unwrap_or_else(|| "e5r".into());
    p.set_file_name(name);
    p
}

/// Read a log, treating a missing file as an empty one.
pub fn load(path: &Path) -> Result<Log, String> {
    match std::fs::read_to_string(path) {
        Ok(text) => Log::from_text(&text).map_err(|e| format!("{}: {e}", path.display())),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Log::new()),
        Err(e) => Err(format!("{}: {e}", path.display())),
    }
}

/// Write a log, atomically, so an interrupted write cannot lose the file.
pub fn save(path: &Path, log: &Log) -> Result<(), String> {
    let tmp = path.with_extension("e5r.tmp");
    std::fs::write(&tmp, log.to_text()).map_err(|e| format!("{}: {e}", tmp.display()))?;
    std::fs::rename(&tmp, path).map_err(|e| format!("{}: {e}", path.display()))?;
    warn_if_git_lacks_union(path);
    Ok(())
}

/// Say once if the log is in a git repo with no union merge rule.
///
/// Without it two branches conflict on adjacent insertions. The rule is one
/// line, and it is the difference between "merges by itself" and "resolve this
/// by hand". Printed rather than written, because editing someone's
/// `.gitattributes` unasked is not ours to do.
fn warn_if_git_lacks_union(path: &Path) {
    let dir = path.parent().unwrap_or(Path::new("."));
    let out = std::process::Command::new("git")
        .args(["check-attr", "merge", "--"])
        .arg(path)
        .current_dir(dir)
        .output();
    let Ok(out) = out else { return };
    if !out.status.success() {
        return; // not a repo, or no git
    }
    if String::from_utf8_lossy(&out.stdout).contains("merge: union") {
        return;
    }
    eprintln!(
        "note: add `*.e5r merge=union` to .gitattributes so two branches of \n\
         annotations merge without conflicts"
    );
}

/// One anchor per recovered function, plus the index over them.
pub fn index(p: &Program) -> AnchorIndex {
    AnchorIndex::build(p.functions_by_address().map(|f| anchor_of(p, f)))
}

/// Anchor one function.
pub fn anchor_of(p: &Program, f: &e5r_analysis::Function) -> Anchor {
    let insns = p.instructions(f);
    // The body is the bytes the blocks actually cover, not the hull, so a
    // split function does not fold in whatever sits between its parts.
    let mut body = Vec::with_capacity(f.cfg.covered_bytes() as usize);
    for b in f.cfg.blocks.values() {
        if let Some(bytes) = p.object.memory.slice(b.range.start(), b.range.len()) {
            body.extend_from_slice(bytes);
        }
    }
    Anchor::function(f.entry, &insns, &body)
}

/// The anchor covering an address, with the offset into it.
pub fn anchor_for(p: &Program, at: Addr) -> Option<Anchor> {
    let f = p.function(at).or_else(|| p.function_at(at))?;
    let offset = at.get().saturating_sub(f.entry.get()) as u32;
    Some(anchor_of(p, f).at_offset(offset))
}

/// Set a field on a location.
pub fn set(
    w: &mut Out,
    p: &Program,
    db: &Path,
    field: Field,
    target: &str,
    value: Option<String>,
    who: &str,
) -> Result<u8, String> {
    let Some(at) = addr::resolve(p, target) else {
        return Err(format!("{target:?} is not an address or a symbol"));
    };
    let Some(anchor) = anchor_for(p, at) else {
        return Err(format!("no function covers {at}"));
    };
    let mut log = load(db)?;
    // Checked rather than bare, so a typo in a type is refused at the moment
    // it is typed. An assertion that cannot be read is worse than no
    // assertion: it sits in the log looking like work that was done.
    log.assert_checked(anchor, field, value.clone(), who)
        .map_err(|e| e.to_string())?;
    save(db, &log)?;
    match value {
        Some(v) => outln!(w, "{at} {field} = {v:?}"),
        None => outln!(w, "{at} {field} cleared"),
    }
    Ok(exit::OK)
}

/// Show the current state, resolved against this binary.
pub fn list(w: &mut Out, p: &Program, db: &Path, as_json: bool) -> Result<u8, String> {
    let log = load(db)?;
    let applied = log.apply(&index(p));
    if as_json {
        #[derive(serde::Serialize)]
        struct Row {
            addr: String,
            field: String,
            value: String,
            resolution: String,
            confident: bool,
            by: String,
        }
        let rows: Vec<Row> = applied
            .iter()
            .map(|a| Row {
                addr: format!("{:#x}", a.addr.get()),
                field: a.field.to_string(),
                value: a.value.clone(),
                resolution: a.resolution.to_string(),
                confident: a.resolution.is_confident(),
                by: a.who.clone(),
            })
            .collect();
        return crate::json::emit(w, &rows);
    }
    if applied.is_empty() {
        eprintln!("no annotations in {}", db.display());
        return Ok(exit::NOT_FOUND);
    }
    for a in &applied {
        // An unconfident match is flagged: the annotation landed somewhere, but
        // only the address agreed, and the address is the weakest layer.
        let flag = if a.resolution.is_confident() {
            String::new()
        } else {
            format!("  [{} match]", a.resolution)
        };
        outln!(
            w,
            "{:<20}{:<9}{:?}{}",
            a.addr.to_string(),
            a.field.to_string(),
            a.value,
            flag
        );
    }
    Ok(exit::OK)
}

/// Undo or redo the most recent assertion.
pub fn step(w: &mut Out, db: &Path, forward: bool) -> Result<u8, String> {
    let mut log = load(db)?;
    let done = if forward { log.redo() } else { log.undo() };
    match done {
        Some(a) => {
            save(db, &log)?;
            outln!(
                w,
                "{} {} {} = {:?}",
                if forward { "redid" } else { "undid" },
                a.target.abs,
                a.field,
                a.value.unwrap_or_default()
            );
            Ok(exit::OK)
        }
        None => {
            eprintln!("nothing to {}", if forward { "redo" } else { "undo" });
            Ok(exit::NOT_FOUND)
        }
    }
}

/// Names from the log, by address, for a listing to show.
pub fn names(p: &Program, db: &Path) -> Vec<(Addr, String, Resolution)> {
    of_kind(p, db, Field::Name)
}

/// Type assertions from the log, by the address each one resolved to.
///
/// The text as it was written, not a parsed type: the log is reviewed in a
/// diff, so what a person typed is what is stored, and it is parsed where it
/// is used, against the types that program already knows about.
pub fn declarations(p: &Program, db: &Path) -> BTreeMap<Addr, String> {
    of_kind(p, db, Field::Type)
        .into_iter()
        .map(|(a, v, _)| (a, v))
        .collect()
}

/// Comments from the log, by the address each one resolved to.
///
/// A comment is the cheapest thing an analyst writes and the one they most
/// expect to see again. Storing it and never rendering it makes the log
/// write-only, which is the opposite of the point.
pub fn comments(p: &Program, db: &Path) -> BTreeMap<Addr, String> {
    of_kind(p, db, Field::Comment)
        .into_iter()
        .map(|(a, v, _)| (a, v))
        .collect()
}

/// Assertions of one kind, resolved against this build.
fn of_kind(p: &Program, db: &Path, want: Field) -> Vec<(Addr, String, Resolution)> {
    let Ok(log) = load(db) else {
        return Vec::new();
    };
    log.apply(&index(p))
        .into_iter()
        .filter(|a| a.field == want)
        .map(|a| (a.addr, a.value, a.resolution))
        .collect()
}

/// Load the program database a PE names, if it is there and it matches.
///
/// Symbols from the wrong build are worse than no symbols, because they are
/// confidently wrong, so the identity is checked before anything is believed.
/// The path in the image is where the linker wrote it, which is rarely where
/// the file is now, so the database is also looked for beside the binary.
pub fn load_pdb(obj: &mut e5r_format::Object, binary: &Path) -> Option<String> {
    let named = obj.metadata.get("pe.pdb")?.clone();
    let stem = Path::new(&named).file_name()?;
    let beside = binary.parent().unwrap_or(Path::new(".")).join(stem);
    let (data, from) = [Path::new(&named), beside.as_path()]
        .into_iter()
        .find_map(|p| std::fs::read(p).ok().map(|d| (d, p.display().to_string())))?;

    let want = obj.metadata.get("pe.pdb.key").cloned();
    let db = e5r_format::pdb::read(&data, &obj.sections)?;
    if want.is_some_and(|k| k != db.identity.key()) {
        eprintln!(
            "note: {from} is not the database {} was built with",
            binary.display()
        );
        return None;
    }
    let hints = db.hints();
    let found = hints.len();
    obj.function_hints.extend(hints);
    obj.debug = Some(db.debug);
    for w in &db.warnings {
        eprintln!("note: {from}: {w}");
    }
    Some(format!("{from}: {found} function(s)"))
}
