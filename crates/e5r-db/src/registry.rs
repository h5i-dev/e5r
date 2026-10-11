//! Named projects in a global directory, independent of the working directory.
//!
//! Project manifests and task files are ordinary text. Binaries stay where the
//! user put them; absolute references make the registry usable from any cwd.
use crate::{
    project::Project,
    work::{self, Store},
};
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};

/// Global storage directory, following h5i's data-directory convention.
pub fn root() -> Result<PathBuf, String> {
    root_from(
        std::env::var_os("E5R_PROJECT_HOME").map(PathBuf::from),
        std::env::var_os("XDG_DATA_HOME").map(PathBuf::from),
        std::env::var_os("HOME")
            .or_else(|| std::env::var_os("USERPROFILE"))
            .map(PathBuf::from),
    )
}

fn root_from(
    explicit: Option<PathBuf>,
    data: Option<PathBuf>,
    home: Option<PathBuf>,
) -> Result<PathBuf, String> {
    if let Some(path) = explicit.filter(|p| !p.as_os_str().is_empty()) {
        return absolute(&path, &std::env::current_dir().map_err(|e| e.to_string())?);
    }
    if let Some(path) = data.filter(|p| p.is_absolute()) {
        return Ok(path.join("e5r/projects"));
    }
    home.filter(|p| p.is_absolute())
        .map(|p| p.join(".local/share/e5r/projects"))
        .ok_or_else(|| "no home directory; set E5R_PROJECT_HOME".into())
}

/// Validate a project name before using it as a directory or URL segment.
pub fn validate_name(name: &str) -> Result<(), String> {
    if name.is_empty()
        || name.len() > 64
        || name.starts_with('.')
        || !name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
    {
        return Err("project names need 1–64 ASCII letters, digits, '-', '_' or '.', and cannot start with '.'".into());
    }
    Ok(())
}

/// Make a default project name from a binary filename.
pub fn default_name(binary: &Path) -> String {
    let name: String = binary
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '.') {
                c
            } else {
                '-'
            }
        })
        .take(64)
        .collect();
    let name = name.trim_start_matches('.');
    if name.is_empty() {
        "analysis".into()
    } else {
        name.into()
    }
}

/// An absolute reference; canonicalize existing files and retain missing paths.
pub fn absolute(path: &Path, base: &Path) -> Result<PathBuf, String> {
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    };
    if !path.is_absolute() {
        return Err("reference base must be absolute".into());
    }
    Ok(fs::canonicalize(&path).unwrap_or(path))
}

/// Normalize every project reference against its original working directory.
pub fn normalize(project: &mut Project, base: &Path) -> Result<(), String> {
    fn path(value: &mut String, base: &Path) -> Result<(), String> {
        *value = absolute(Path::new(value), base)?
            .to_string_lossy()
            .into_owned();
        Ok(())
    }
    path(&mut project.binary.path, base)?;
    if let Some(log) = &mut project.log {
        path(log, base)?;
    } else {
        project.log = Some(format!("{}.e5r", project.binary.path));
    }
    for reference in project.signatures.iter_mut().chain(&mut project.patches) {
        path(reference, base)?;
    }
    Ok(())
}

/// Counts have literal task meanings, not agent-process or inferred health states.
#[derive(Default, Serialize)]
pub struct Counts {
    /// All recorded tasks.
    pub total: usize,
    /// Unfinished tasks.
    pub open: usize,
    /// Tasks being worked on.
    pub active: usize,
    /// Explicitly blocked tasks.
    pub blocked: usize,
    /// Results awaiting review.
    pub review: usize,
    /// Planned tasks with completed prerequisites.
    pub ready: usize,
    /// Accepted tasks.
    pub done: usize,
}

/// A cross-project item needing attention.
#[derive(Serialize)]
pub struct Attention {
    /// Task id, scoped to this project.
    pub id: String,
    /// Outcome.
    pub title: String,
    /// Explicit state.
    pub state: work::State,
    /// Recorded reason or handoff.
    pub why: String,
    /// Responsible person or agent.
    pub owner: String,
}

/// A lightweight project summary; listing does not analyze binary bytes.
#[derive(Serialize)]
pub struct Summary {
    /// Global name.
    pub name: String,
    /// Absolute manifest path.
    pub project: String,
    /// Recorded binary path, if the manifest is readable.
    pub binary: Option<String>,
    /// Available, missing, size_changed, or unreadable; content verified on open.
    pub availability: String,
    /// Latest task timestamp, if any.
    pub updated: Option<u64>,
    /// Task counts.
    pub counts: Counts,
    /// Tasks requiring attention.
    pub attention: Vec<Attention>,
    /// Manifest or task-store errors remain visible in the collection.
    pub error: Option<String>,
}

/// Global project directory. Construct directly in tests; use [`root`] in CLI.
pub struct Registry {
    root: PathBuf,
}

impl Registry {
    /// Open a directory without creating it until the first write.
    pub fn new(root: PathBuf) -> Self {
        Self { root }
    }
    /// Directory where managed projects live.
    pub fn root(&self) -> &Path {
        &self.root
    }
    /// Resolve a validated name to its global manifest.
    pub fn path(&self, name: &str) -> Result<PathBuf, String> {
        validate_name(name)?;
        let dir = self.root.join(name);
        if fs::symlink_metadata(&dir).is_ok_and(|m| m.file_type().is_symlink()) {
            return Err("a registered project directory cannot be a symlink".into());
        }
        Ok(dir.join("project.e5rproj"))
    }
    /// Read a named manifest.
    pub fn read(&self, name: &str) -> Result<Project, String> {
        let path = self.path(name)?;
        let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        Project::from_text(&text).map_err(|e| format!("{}: {e}", path.display()))
    }
    /// Store a new manifest and optional imported tasks, refusing name collisions.
    pub fn create(
        &self,
        name: &str,
        project: &Project,
        source_work: Option<&Path>,
    ) -> Result<PathBuf, String> {
        let path = self.path(name)?;
        let mut project = project.clone();
        // Callers must supply absolute references; a registry never depends on cwd.
        if !Path::new(&project.binary.path).is_absolute()
            || project
                .log
                .iter()
                .chain(&project.signatures)
                .chain(&project.patches)
                .any(|path| !Path::new(path).is_absolute())
        {
            return Err("registered projects require absolute file references".into());
        }
        if project.log.is_none() {
            project.log = Some(format!("{}.e5r", project.binary.path));
        }
        let tasks = match source_work {
            Some(root) => Store::new(root).list()?,
            None => Vec::new(),
        };
        let mut records = Vec::new();
        if let Some(root) = source_work {
            for kind in ["finding", "note", "report"] {
                records.push((kind, Store::new(root.join(kind)).list()?));
            }
        }
        fs::create_dir_all(&self.root).map_err(|e| e.to_string())?;
        let dir = path.parent().ok_or("invalid project path")?;
        fs::create_dir(dir)
            .map_err(|e| format!("cannot create project {name}: {e}; choose a different name"))?;
        let result = (|| {
            if !tasks.is_empty() {
                let work = work::beside(&path);
                fs::create_dir(&work).map_err(|e| e.to_string())?;
                for task in &tasks {
                    let text = serde_json::to_vec_pretty(task).map_err(|e| e.to_string())?;
                    fs::write(work.join(format!("{}.json", task.id)), text)
                        .map_err(|e| e.to_string())?;
                }
            }
            for (kind, items) in &records {
                if items.is_empty() {
                    continue;
                }
                let dest = work::beside(&path).join(kind);
                fs::create_dir_all(&dest).map_err(|e| e.to_string())?;
                for item in items {
                    fs::write(
                        dest.join(format!("{}.json", item.id)),
                        serde_json::to_vec_pretty(item).map_err(|e| e.to_string())?,
                    )
                    .map_err(|e| e.to_string())?;
                }
            }
            let temporary = dir.join("project.tmp");
            fs::write(&temporary, project.to_text()).map_err(|e| e.to_string())?;
            fs::rename(&temporary, &path).map_err(|e| e.to_string())?;
            Ok(path.clone())
        })();
        if result.is_err() {
            // Only remove files this creation wrote. Never recursively remove a
            // directory somebody else may have changed in the meantime.
            let work = work::beside(&path);
            for task in &tasks {
                let _ = fs::remove_file(work.join(format!("{}.json", task.id)));
            }
            for (kind, items) in &records {
                let dest = work.join(kind);
                for item in items {
                    let _ = fs::remove_file(dest.join(format!("{}.json", item.id)));
                }
                let _ = fs::remove_dir(dest);
            }
            let _ = fs::remove_dir(work);
            let _ = fs::remove_file(dir.join("project.tmp"));
            let _ = fs::remove_dir(dir);
        }
        result
    }
    /// Import a manifest and its task history as a new global project.
    pub fn import(
        &self,
        source: &Path,
        name: &str,
        base: Option<&Path>,
    ) -> Result<PathBuf, String> {
        let source = fs::canonicalize(source).map_err(|e| e.to_string())?;
        let text = fs::read_to_string(&source).map_err(|e| e.to_string())?;
        let mut project = Project::from_text(&text).map_err(|e| e.to_string())?;
        let base = base.unwrap_or(source.parent().ok_or("project has no parent directory")?);
        let base = absolute(base, &std::env::current_dir().map_err(|e| e.to_string())?)?;
        normalize(&mut project, &base)?;
        self.create(name, &project, Some(&work::beside(&source)))
    }
    /// List projects and live task signals without loading any binary.
    pub fn list(&self) -> Result<Vec<Summary>, String> {
        let entries = match fs::read_dir(&self.root) {
            Ok(entries) => entries,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(e.to_string()),
        };
        let mut summaries = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| e.to_string())?;
            if !entry.file_type().map_err(|e| e.to_string())?.is_dir() {
                continue;
            }
            let name = entry.file_name().to_string_lossy().into_owned();
            if validate_name(&name).is_err() {
                continue;
            }
            let path = self.path(&name)?;
            let mut summary = Summary {
                name: name.clone(),
                project: path.display().to_string(),
                binary: None,
                availability: "unreadable".into(),
                updated: None,
                counts: Counts::default(),
                attention: Vec::new(),
                error: None,
            };
            match self.read(&name) {
                Ok(project) => {
                    summary.binary = Some(project.binary.path.clone());
                    summary.availability = match fs::metadata(&project.binary.path) {
                        Ok(m) if m.is_file() && m.len() == project.binary.size => "available",
                        Ok(m) if m.is_file() => "size_changed",
                        _ => "missing",
                    }
                    .into();
                }
                Err(e) => summary.error = Some(e),
            }
            match Store::new(work::beside(&path)).board() {
                Ok(board) => {
                    for row in board.tasks {
                        summary.counts.total += 1;
                        if row.task.content.state != work::State::Done {
                            summary.counts.open += 1;
                        }
                        match row.task.content.state {
                            work::State::Active => summary.counts.active += 1,
                            work::State::Blocked => summary.counts.blocked += 1,
                            work::State::Review => summary.counts.review += 1,
                            work::State::Done => summary.counts.done += 1,
                            _ => {}
                        }
                        if row.ready {
                            summary.counts.ready += 1;
                        }
                        summary.updated = Some(summary.updated.unwrap_or(0).max(row.task.updated));
                        if let Some(why) = row.attention {
                            summary.attention.push(Attention {
                                id: row.task.id,
                                title: row.task.content.title,
                                state: row.task.content.state,
                                why,
                                owner: row.task.content.owner,
                            });
                        }
                    }
                }
                Err(e) => {
                    summary.error = Some(match summary.error {
                        Some(previous) => format!("{previous}; {e}"),
                        None => e,
                    })
                }
            }
            summaries.push(summary);
        }
        summaries.sort_by(|a, b| {
            b.attention
                .len()
                .cmp(&a.attention.len())
                .then_with(|| a.name.cmp(&b.name))
        });
        Ok(summaries)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn directory() -> PathBuf {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!("e5r-registry-{}-{stamp}", std::process::id()))
    }
    #[test]
    fn storage_precedence_and_names_are_predictable() {
        assert_eq!(
            root_from(
                Some("/custom".into()),
                Some("/data".into()),
                Some("/home/test".into())
            )
            .unwrap(),
            PathBuf::from("/custom")
        );
        assert_eq!(
            root_from(None, Some("/data".into()), Some("/home/test".into())).unwrap(),
            PathBuf::from("/data/e5r/projects")
        );
        assert_eq!(
            root_from(None, Some("relative".into()), Some("/home/test".into())).unwrap(),
            PathBuf::from("/home/test/.local/share/e5r/projects")
        );
        assert!(root_from(None, None, None).is_err());
        for name in ["../escape", ".hidden", "a/b", "", "a?b"] {
            assert!(validate_name(name).is_err());
        }
    }
    #[test]
    fn imports_keep_tasks_paths_and_corruption_visible() {
        let base = directory();
        fs::create_dir_all(&base).unwrap();
        fs::write(base.join("binary"), b"binary").unwrap();
        let project = Project::for_binary("binary", b"binary");
        let source = base.join("old.e5rproj");
        fs::write(&source, project.to_text()).unwrap();
        let task = Store::new(work::beside(&source))
            .create(
                work::Draft {
                    title: "Need sample".into(),
                    state: work::State::Blocked,
                    blocker: "Awaiting input".into(),
                    ..Default::default()
                },
                "agent",
            )
            .unwrap();
        let registry = Registry::new(base.join("global"));
        let saved = registry.import(&source, "parser", None).unwrap();
        assert_eq!(
            registry.read("parser").unwrap().binary.path,
            base.join("binary").to_string_lossy()
        );
        assert_eq!(
            Store::new(work::beside(&saved)).list().unwrap()[0].id,
            task.id
        );
        let summaries = registry.list().unwrap();
        assert_eq!(summaries[0].counts.blocked, 1);
        assert_eq!(summaries[0].attention[0].why, "Awaiting input");
        assert!(registry.import(&source, "parser", None).is_err());
        fs::write(&saved, "corrupt").unwrap();
        assert!(registry.list().unwrap()[0].error.is_some());
        fs::remove_dir_all(base).unwrap();
    }
}
