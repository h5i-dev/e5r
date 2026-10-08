//! Global project CLI: registration, name resolution and live summaries.
use crate::{
    out::{Out, outln},
    patch,
};
use e5r_db::project::Project;
use e5r_db::registry::{self, Registry};
use std::path::{Path, PathBuf};

pub fn registry() -> Result<Registry, String> {
    Ok(Registry::new(registry::root()?))
}

pub fn resolve(reference: &Path) -> Result<PathBuf, String> {
    if reference.is_file() {
        return std::fs::canonicalize(reference).map_err(|e| e.to_string());
    }
    if reference.is_absolute() || reference.components().count() > 1 {
        return Err(format!("project {} not found", reference.display()));
    }
    let name = reference.to_str().ok_or("project name must be UTF-8")?;
    let path = registry()?.path(name)?;
    if !path.is_file() {
        return Err(format!("project {name:?} not found; use e5r project list"));
    }
    Ok(path)
}

pub fn list(w: &mut Out, json: bool) -> Result<u8, String> {
    let registry = registry()?;
    let projects = registry.list()?;
    if json {
        return crate::json::emit(
            w,
            &serde_json::json!({"schema":"e5r.projects.v1", "root":registry.root().display().to_string(), "projects":projects}),
        );
    }
    outln!(w, "Projects: {}", registry.root().display());
    for p in projects {
        outln!(
            w,
            "{}  {} open · {} active · {} blocked · {} review  [{}]",
            p.name,
            p.counts.open,
            p.counts.active,
            p.counts.blocked,
            p.counts.review,
            p.availability
        );
        if let Some(error) = p.error {
            outln!(w, "  error: {error}");
        }
        if let Some(binary) = p.binary {
            outln!(w, "  binary: {binary}");
        }
    }
    Ok(0)
}

pub fn create(w: &mut Out, name: &str, project: &Project) -> Result<u8, String> {
    let path = registry()?.create(name, project, None)?;
    outln!(w, "{} registered: {}", name, path.display());
    Ok(0)
}

pub fn import(w: &mut Out, source: &Path, name: &str, base: Option<&Path>) -> Result<u8, String> {
    let path = registry()?.import(source, name, base)?;
    outln!(w, "{} imported: {}", name, path.display());
    Ok(0)
}

pub fn relocate(w: &mut Out, path: &Path, binary: &Path) -> Result<u8, String> {
    let mut project = patch::project_read(path)?;
    let binary = std::fs::canonicalize(binary).map_err(|e| e.to_string())?;
    let file = std::fs::File::open(&binary).map_err(|e| e.to_string())?;
    let data = crate::map_file(&file).map_err(|e| e.to_string())?;
    let verdict = project.verify_at(&binary.to_string_lossy(), &data);
    if !verdict.is_usable() {
        return Err(verdict.to_string());
    }
    project.binary.path = binary.to_string_lossy().into_owned();
    let temporary = path.with_extension(format!("{}.tmp", std::process::id()));
    std::fs::write(&temporary, project.to_text()).map_err(|e| e.to_string())?;
    std::fs::rename(temporary, path).map_err(|e| e.to_string())?;
    outln!(w, "{} now opens {}", path.display(), binary.display());
    Ok(0)
}
