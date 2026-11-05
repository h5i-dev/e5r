//! Owned scratch directories and cooperative per-project exclusion.
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
static NEXT: AtomicU64 = AtomicU64::new(0);
pub struct Workspace {
    path: PathBuf,
    temporary: bool,
}
impl Workspace {
    pub fn new(keep: Option<&Path>) -> Result<Self, String> {
        let (path, temporary) = if let Some(p) = keep {
            std::fs::create_dir_all(p).map_err(|e| e.to_string())?;
            (p.to_path_buf(), false)
        } else {
            let p = loop {
                let p = std::env::temp_dir().join(format!(
                    "e5r-proof-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match std::fs::create_dir(&p) {
                    Ok(()) => break p,
                    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(e) => return Err(e.to_string()),
                }
            };
            (p, true)
        };
        Ok(Self {
            path: path.canonicalize().map_err(|e| e.to_string())?,
            temporary,
        })
    }
    pub fn path(&self) -> &Path {
        &self.path
    }
}
impl Drop for Workspace {
    fn drop(&mut self) {
        if self.temporary {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }
}
/// An OS flock lives on the verifier process and is released even after SIGKILL.
/// Linux tools outside e5r must still avoid mutating the project during a check.
/// Lock acquisition is fail-fast; orchestration does not queue unbounded work.
pub struct ProjectLock {
    _file: std::fs::File,
}
impl ProjectLock {
    pub fn acquire(project: &Path) -> Result<Self, String> {
        // Safe std file locking (MSRV for this API is documented in Cargo.toml).
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(project.join(".e5r-verification.lock"))
            .map_err(|e| e.to_string())?;
        file.try_lock()
            .map_err(|e| format!("verification project is busy ({}): {e}", project.display()))?;
        Ok(Self { _file: file })
    }
}
