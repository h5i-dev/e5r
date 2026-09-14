//! The patch and project commands.
//!
//! Patching writes to a file, so everything here is arranged so that the
//! answer to "what would this do" comes before anything is written, and so
//! that a patch which no longer fits the binary says so rather than landing
//! somewhere approximate.

use std::path::{Path, PathBuf};

use r12e_analysis::Program;
use r12e_core::Addr;
use r12e_db::patch::{Applied, Change, Conflict, Edit, Patch};
use r12e_db::project::{Project, Verdict};
use r12e_format::Object;

use crate::addr;
use crate::annotate;
use crate::exit;
use crate::out::{Out, outln};

type R = Result<u8, String>;

/// The binary a patch command is about: the analysis, the bytes on disk, and
/// where they came from.
pub struct Subject<'a> {
    /// What the analyzer recovered, which is where the anchors come from.
    pub program: &'a Program,
    /// The file's bytes, exactly as they are on disk.
    pub file: &'a [u8],
    /// Where they were read from.
    pub binary: &'a Path,
}

/// Read a patch set, or fail with the path in the message.
pub fn read(path: &Path) -> Result<Patch, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Patch::from_text(&text).map_err(|e| format!("{}: {e}", path.display()))
}

/// Write a patch set.
fn write(path: &Path, p: &Patch) -> Result<(), String> {
    std::fs::write(path, p.to_text()).map_err(|e| format!("{}: {e}", path.display()))
}

/// Parse `de ad be ef` or `deadbeef` into bytes.
pub fn hex(s: &str) -> Result<Vec<u8>, String> {
    let digits: String = s
        .chars()
        .filter(|c| !c.is_whitespace() && *c != '_')
        .collect();
    if digits.is_empty() || digits.len() % 2 != 0 {
        return Err(format!("{s:?} is not a whole number of hex bytes"));
    }
    (0..digits.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).map_err(|_| format!("{s:?} is not hex")))
        .collect()
}

/// The constant that turns an address into a file offset, for the section the
/// address is in.
///
/// A patch is written to the file, and an address only becomes a file offset
/// through whichever section maps it. Sections rarely share one constant, so
/// this is checked per change rather than assumed.
fn file_base(o: &Object, at: Addr) -> Option<u64> {
    o.sections
        .iter()
        .find(|s| s.file_size > 0 && !s.range.is_empty() && s.range.contains(at))
        .map(|s| s.range.start().get().wrapping_sub(s.file_offset))
}

/// Every change agrees on that constant, so the whole set can be applied to
/// the file as one image.
fn one_window(o: &Object, changes: &[Change], base: u64) -> Result<(), String> {
    for c in changes {
        match file_base(o, c.addr) {
            Some(b) if b == base => {}
            Some(b) => {
                return Err(format!(
                    "{} is in a section mapped at a different file offset ({:#x} against {:#x}); \
                     split the patch set by section",
                    c.addr, b, base
                ));
            }
            None => return Err(format!("{} is not in any section with file bytes", c.addr)),
        }
    }
    Ok(())
}

/// Where a patch set lands and what it holds.
fn placement(
    p: &Patch,
    o: &Object,
    file: &[u8],
    index: &r12e_db::AnchorIndex,
) -> Result<(u64, Vec<Change>), String> {
    let first = p
        .edits()
        .first()
        .ok_or_else(|| "the patch set is empty".to_string())?;
    let base = file_base(o, first.addr())
        .ok_or_else(|| format!("{} is not in any section with file bytes", first.addr()))?;
    let changes = p
        .preview(file, Addr(base), Some(index))
        .map_err(|c| conflict(&c))?;
    one_window(o, &changes, base)?;
    Ok((base, changes))
}

/// A conflict, spelled for a terminal.
fn conflict(c: &Conflict) -> String {
    format!("{c}")
}

/// Print one change per line.
fn show_changes(w: &mut Out, changes: &[Change]) {
    outln!(
        w,
        "{:<20}{:<20}{:<20}{}",
        "address",
        "before",
        "after",
        "found by"
    );
    for c in changes {
        outln!(
            w,
            "{:<20}{:<20}{:<20}{}",
            c.addr.to_string(),
            bytes(&c.before),
            bytes(&c.after),
            c.resolution.as_str()
        );
    }
}

fn bytes(b: &[u8]) -> String {
    b.iter()
        .map(|x| format!("{x:02x}"))
        .collect::<Vec<_>>()
        .join("")
}

/// Write the patched file, or the original path when asked to work in place.
fn emit(
    out: Option<&Path>,
    original: &Path,
    image: &[u8],
    in_place: bool,
) -> Result<PathBuf, String> {
    let dest = match (out, in_place) {
        (Some(p), _) => p.to_path_buf(),
        (None, true) => original.to_path_buf(),
        (None, false) => {
            return Err("give -o, or --in-place to overwrite the binary".to_string());
        }
    };
    // Written beside the destination and renamed, so an interrupted write
    // cannot leave a half-patched binary behind.
    let tmp = dest.with_extension("r12e-patching");
    std::fs::write(&tmp, image).map_err(|e| format!("{}: {e}", tmp.display()))?;
    if let Ok(meta) = std::fs::metadata(original) {
        let _ = std::fs::set_permissions(&tmp, meta.permissions());
    }
    std::fs::rename(&tmp, &dest).map_err(|e| format!("{}: {e}", dest.display()))?;
    Ok(dest)
}

/// Report what was written.
fn report(w: &mut Out, applied: &Applied, dest: &Path) {
    show_changes(w, &applied.changes);
    outln!(
        w,
        "{} byte(s) in {} change(s) written to {}",
        applied.bytes,
        applied.changes.len(),
        dest.display()
    );
}

/// `record`: capture an edit from the binary as it is now.
/// How the replacement was written.
///
/// Assembly cannot be turned into bytes until the address is known: a branch
/// or a pc-relative operand encodes a displacement from where it sits, so
/// assembling at zero and relocating afterwards would be wrong.
pub enum Source<'a> {
    /// Bytes, already given as hex.
    Bytes(Vec<u8>),
    /// Instructions, to assemble at the target address.
    Asm(&'a str),
}

/// What to write, and how long it has to be.
pub struct Replacement<'a> {
    /// The replacement as the analyst wrote it.
    pub source: Source<'a>,
    /// Pad with no-ops to this length. An instruction that encodes shorter
    /// than the one it replaces leaves the bytes after it meaning something
    /// they did not mean before.
    pub pad_to: Option<usize>,
}

pub fn record(
    w: &mut Out,
    s: &Subject,
    target: &str,
    replace: Replacement<'_>,
    who: &str,
    note: &str,
    out: &Path,
) -> R {
    let (p, file, binary) = (s.program, s.file, s.binary);
    let at = addr::resolve(p, target).ok_or_else(|| format!("{target}: no such address"))?;
    let mut bytes = match replace.source {
        Source::Bytes(b) => b,
        Source::Asm(text) => r12e_asm::assemble_all(&p.object.arch, text, at)
            .map_err(|e| format!("{target}: {e}"))?,
    };
    if let Some(n) = replace.pad_to {
        if bytes.len() > n {
            return Err(format!(
                "the replacement is {} bytes, which does not fit in {n}",
                bytes.len()
            ));
        }
        bytes.extend(r12e_asm::pad(&p.object.arch, n - bytes.len()).map_err(|e| e.to_string())?);
    }
    let replace = &bytes[..];
    let base = file_base(&p.object, at)
        .ok_or_else(|| format!("{at} is not in any section with file bytes"))?;
    let mut set = match std::fs::read_to_string(out) {
        Ok(text) => Patch::from_text(&text).map_err(|e| format!("{}: {e}", out.display()))?,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            Patch::new(&out.file_stem().unwrap_or_default().to_string_lossy())
        }
        Err(e) => return Err(format!("{}: {e}", out.display())),
    };
    // Anchored to the function it lands in when there is one, so the edit
    // survives a rebuild that moves the code. Without a function the address
    // is all there is, and the resolution reported on apply says so.
    let anchor = match p.function_at(at) {
        Some(f) => {
            let off = at.get().wrapping_sub(f.entry.get());
            let off = u32::try_from(off).map_err(|_| "the offset is too large".to_string())?;
            annotate::anchor_of(p, f).at_offset(off)
        }
        None => r12e_db::Anchor {
            shape: 0,
            bytes: 0,
            insns: 0,
            abs: at,
            offset: 0,
        },
    };
    if set.binary.is_none() {
        set.binary = Some(
            binary
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .into(),
        );
    }
    let off = usize::try_from(at.get().wrapping_sub(base))
        .ok()
        .filter(|o| o + replace.len() <= file.len())
        .ok_or_else(|| format!("{at} plus {} bytes is past the file", replace.len()))?;
    let expect = file[off..off + replace.len()].to_vec();
    let before = set.len();
    set.push(
        Edit::new(anchor, expect, replace.to_vec())
            .map_err(|e| e.to_string())?
            .by(who)
            .noted(note),
    );

    write(out, &set)?;
    outln!(
        w,
        "{} edit(s) in {}, {} new",
        set.len(),
        out.display(),
        set.len().saturating_sub(before)
    );
    Ok(exit::OK)
}

/// `show`: what a patch set says, without touching the binary.
pub fn show(w: &mut Out, set: &Patch) -> R {
    outln!(
        w,
        "{}: {} edit(s){}",
        set.name,
        set.len(),
        set.binary
            .as_ref()
            .map(|b| format!(", for {b}"))
            .unwrap_or_default()
    );
    for (n, e) in set.edits().iter().enumerate() {
        outln!(
            w,
            "{n:>3}  {:<20}{:<20}{:<20}{}{}",
            e.addr().to_string(),
            bytes(&e.expect),
            bytes(&e.replace),
            if e.who.is_empty() {
                String::new()
            } else {
                format!("{} ", e.who)
            },
            e.note
        );
    }
    if set.is_empty() {
        return Ok(exit::NOT_FOUND);
    }
    Ok(exit::OK)
}

/// `preview`: where it would land, and what it would overwrite.
pub fn preview(w: &mut Out, s: &Subject, set: &Patch) -> R {
    let index = annotate::index(s.program);
    let (_, changes) = placement(set, &s.program.object, s.file, &index)?;
    show_changes(w, &changes);
    Ok(exit::OK)
}

/// `apply` and `revert`, which differ only in which set is used.
pub fn apply(
    w: &mut Out,
    s: &Subject,
    set: &Patch,
    out: Option<&Path>,
    in_place: bool,
    allow_address_only: bool,
) -> R {
    let index = annotate::index(s.program);
    let (base, _) = placement(set, &s.program.object, s.file, &index)?;
    let mut image = s.file.to_vec();
    let applied = set
        .apply(&mut image, Addr(base), Some(&index))
        .map_err(|c| conflict(&c))?;
    if !applied.is_confident() && !allow_address_only {
        return Err(
            "some edits matched on the address alone, which means the code they were written \
             against is not there; pass --allow-address-only to write anyway"
                .to_string(),
        );
    }
    let dest = emit(out, s.binary, &image, in_place)?;
    report(w, &applied, &dest);
    Ok(exit::OK)
}

/// `invert`: write the set that undoes this one.
pub fn invert(w: &mut Out, set: &Patch, out: &Path) -> R {
    let back = set.revert();
    write(out, &back)?;
    outln!(w, "{} edit(s) written to {}", back.len(), out.display());
    Ok(exit::OK)
}

/// `merge`: one set from several, with the later ones taking precedence.
pub fn merge(w: &mut Out, sets: &[PathBuf], out: &Path) -> R {
    let mut all = Patch::new(&out.file_stem().unwrap_or_default().to_string_lossy());
    for path in sets {
        let s = read(path)?;
        if all.binary.is_none() {
            all.binary = s.binary.clone();
        }
        all.merge(&s);
    }
    write(out, &all)?;
    outln!(w, "{} edit(s) written to {}", all.len(), out.display());
    Ok(exit::OK)
}

/// `project new`: record what it takes to reopen this session.
pub fn project_new(
    w: &mut Out,
    binary: &Path,
    o: &Object,
    data: &[u8],
    settings: &[String],
    log: Option<&Path>,
    out: &Path,
) -> R {
    let mut proj = Project::for_binary(&binary.display().to_string(), data);
    proj.load.base = Some(o.image_base);
    proj.load.arch = Some(o.arch.clone());
    proj.load.readers.insert(o.format.to_string());
    for s in settings {
        let (k, v) = s
            .split_once('=')
            .ok_or_else(|| format!("{s:?} is not key=value"))?;
        proj.analysis.insert(k.to_string(), v.to_string());
    }
    proj.log = log
        .map(|p| p.display().to_string())
        .or_else(|| Some(annotate::default_path(binary).display().to_string()));
    std::fs::write(out, proj.to_text()).map_err(|e| format!("{}: {e}", out.display()))?;
    outln!(w, "{} written", out.display());
    Ok(exit::OK)
}

/// Read a project file.
pub fn project_read(path: &Path) -> Result<Project, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Project::from_text(&text).map_err(|e| format!("{}: {e}", path.display()))
}

/// `project show`.
pub fn project_show(w: &mut Out, proj: &Project) -> R {
    for line in proj.to_text().lines() {
        outln!(w, "{line}");
    }
    Ok(exit::OK)
}

/// `project verify`: are these the bytes the session was made for.
pub fn project_verify(w: &mut Out, proj: &Project, binary: &Path, data: &[u8]) -> R {
    let verdict = proj.verify_at(&binary.display().to_string(), data);
    outln!(w, "{verdict}");
    // A moved binary is still the right one, so it is not a failure.
    Ok(match verdict {
        Verdict::Different { .. } => exit::NOT_FOUND,
        _ => exit::OK,
    })
}

/// `project add`: attach a signature library, a patch set or a log.
pub fn project_add(
    w: &mut Out,
    path: &Path,
    signatures: &[PathBuf],
    patches: &[PathBuf],
    log: Option<&Path>,
) -> R {
    let mut proj = project_read(path)?;
    for s in signatures {
        let s = s.display().to_string();
        if !proj.signatures.contains(&s) {
            proj.signatures.push(s);
        }
    }
    for p in patches {
        let p = p.display().to_string();
        if !proj.patches.contains(&p) {
            proj.patches.push(p);
        }
    }
    if let Some(l) = log {
        proj.log = Some(l.display().to_string());
    }
    std::fs::write(path, proj.to_text()).map_err(|e| format!("{}: {e}", path.display()))?;
    outln!(
        w,
        "{}: {} signature file(s), {} patch set(s)",
        path.display(),
        proj.signatures.len(),
        proj.patches.len()
    );
    Ok(exit::OK)
}
