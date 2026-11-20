//! Durable coordination beside a project, separate from its binary configuration.
//!
//! One JSON file per task makes unrelated changes reviewable and mergeable in git.
//! A store lock serializes local writers; revisions reject stale human/agent edits.

use serde::{Deserialize, Serialize};
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// The task's workflow state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum State {
    /// Available for planning or claiming.
    #[default]
    Planned,
    /// An owner is working on it.
    Active,
    /// Cannot proceed; the reason is recorded.
    Blocked,
    /// A person or another agent should review the result.
    Review,
    /// The result has been accepted.
    Done,
}

/// Explicit urgency, not an inferred score.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Priority {
    /// Address before ordinary work.
    High,
    /// Ordinary work.
    #[default]
    Normal,
    /// Can wait.
    Low,
}

/// A saved revision, so handoffs retain their author and context.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Change {
    /// Unix timestamp in seconds.
    pub at: u64,
    /// Person or agent who wrote it.
    pub author: String,
    /// The previous task content.
    pub previous: Draft,
}

/// Fields shared by creation and full replacement updates.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Draft {
    /// Short, concrete outcome.
    pub title: String,
    /// Context and acceptance criteria.
    #[serde(default)]
    pub description: String,
    /// Workflow state.
    #[serde(default)]
    pub state: State,
    /// Explicit urgency.
    #[serde(default)]
    pub priority: Priority,
    /// Person or agent responsible for the next step.
    #[serde(default)]
    pub owner: String,
    /// Concrete next step, also used for a handoff.
    #[serde(default)]
    pub next: String,
    /// Why work cannot proceed; required when blocked.
    #[serde(default)]
    pub blocker: String,
    /// Paths, addresses, commands or links supporting the result.
    #[serde(default)]
    pub evidence: Vec<String>,
    /// Tasks that must be done before this one can be started.
    #[serde(default)]
    pub depends_on: Vec<String>,
}

/// A durable task with an optimistic concurrency revision.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Task {
    /// Stable task id.
    pub id: String,
    /// Starts at one, incremented for each update.
    pub revision: u64,
    /// Current task content.
    pub content: Draft,
    /// Unix timestamp in seconds.
    pub created: u64,
    /// Last update timestamp.
    pub updated: u64,
    /// Last writer.
    pub author: String,
    /// Earlier contents, in chronological order.
    pub history: Vec<Change>,
}

/// A task plus mechanically derived coordination signals.
#[derive(Serialize)]
pub struct Row {
    /// Saved task.
    pub task: Task,
    /// Unfinished prerequisite task ids.
    pub waiting_on: Vec<String>,
    /// Can be claimed now.
    pub ready: bool,
    /// Why this needs a person's attention, if anything.
    pub attention: Option<String>,
}

/// Shared dashboard/agent snapshot, versioned independently from binary analysis.
#[derive(Serialize)]
pub struct Board {
    /// Shape version.
    pub schema: &'static str,
    /// Tasks ordered by urgency and id.
    pub tasks: Vec<Row>,
}

/// Task storage directory (typically `<project>.work`).
pub struct Store {
    root: PathBuf,
}

struct Lock(PathBuf);
impl Drop for Lock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn stamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

fn valid_id(id: &str) -> bool {
    id.starts_with("T-") && id.len() > 2 && id[2..].bytes().all(|b| b.is_ascii_digit())
}

impl Store {
    /// Open a directory without creating it until the first write.
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    fn lock(&self) -> Result<Lock, String> {
        fs::create_dir_all(&self.root).map_err(|e| e.to_string())?;
        let path = self.root.join(".lock");
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|e| {
                format!(
                    "cannot lock {}: {e}; another writer may be active",
                    self.root.display()
                )
            })?;
        let guard = Lock(path);
        writeln!(file, "pid={} at={}", std::process::id(), stamp()).map_err(|e| e.to_string())?;
        Ok(guard)
    }

    /// Read tasks, refusing corrupt or unknown data rather than hiding it.
    pub fn list(&self) -> Result<Vec<Task>, String> {
        let entries = match fs::read_dir(&self.root) {
            Ok(entries) => entries,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(e.to_string()),
        };
        let mut tasks = Vec::new();
        for entry in entries {
            let path = entry.map_err(|e| e.to_string())?.path();
            if path.extension().and_then(|s| s.to_str()) != Some("json") {
                continue;
            }
            let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            let task: Task =
                serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
            if !valid_id(&task.id)
                || path.file_stem().and_then(|s| s.to_str()) != Some(&task.id)
                || task.revision == 0
            {
                return Err(format!(
                    "{}: invalid task identity or revision",
                    path.display()
                ));
            }
            validate(&task.content)?;
            tasks.push(task);
        }
        tasks.sort_by(|a, b| {
            a.content
                .priority
                .cmp(&b.content.priority)
                .then_with(|| a.id.cmp(&b.id))
        });
        Ok(tasks)
    }

    /// Compute readiness and reasons from the same saved state for all clients.
    pub fn board(&self) -> Result<Board, String> {
        let tasks = self.list()?;
        let rows = tasks
            .iter()
            .map(|task| {
                let waiting_on: Vec<_> = task
                    .content
                    .depends_on
                    .iter()
                    .filter(|id| {
                        !tasks
                            .iter()
                            .any(|t| &t.id == *id && t.content.state == State::Done)
                    })
                    .cloned()
                    .collect();
                let attention = match task.content.state {
                    State::Blocked => Some(task.content.blocker.clone()),
                    State::Review => Some(if task.content.next.trim().is_empty() {
                        "Result needs review".into()
                    } else {
                        task.content.next.clone()
                    }),
                    State::Active if task.content.owner.trim().is_empty() => {
                        Some("Active work has no owner".into())
                    }
                    _ => None,
                };
                Row {
                    task: task.clone(),
                    ready: task.content.state == State::Planned && waiting_on.is_empty(),
                    waiting_on,
                    attention,
                }
            })
            .collect();
        Ok(Board {
            schema: "e5r.work.v1",
            tasks: rows,
        })
    }

    /// Create a new task. The author is explicit for human/agent parity.
    pub fn create(&self, content: Draft, author: &str) -> Result<Task, String> {
        validate_author(author)?;
        let _lock = self.lock()?;
        let tasks = self.list()?;
        let next = tasks
            .iter()
            .filter_map(|t| t.id[2..].parse::<u64>().ok())
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or("task ids exhausted")?;
        let id = format!("T-{next:04}");
        self.check(&id, &content, &tasks)?;
        let now = stamp();
        let task = Task {
            id,
            revision: 1,
            content,
            created: now,
            updated: now,
            author: author.into(),
            history: Vec::new(),
        };
        self.save(&task)?;
        Ok(task)
    }

    /// Replace task content only if the caller read its current revision.
    pub fn update(
        &self,
        id: &str,
        revision: u64,
        content: Draft,
        author: &str,
    ) -> Result<Task, String> {
        if !valid_id(id) {
            return Err("invalid task id".into());
        }
        validate_author(author)?;
        let _lock = self.lock()?;
        let tasks = self.list()?;
        let mut task = tasks
            .iter()
            .find(|t| t.id == id)
            .cloned()
            .ok_or("task not found")?;
        if task.revision != revision {
            return Err(format!(
                "revision conflict: expected {revision}, current {}; reload before editing",
                task.revision
            ));
        }
        self.check(id, &content, &tasks)?;
        task.history.push(Change {
            at: task.updated,
            author: task.author.clone(),
            previous: task.content,
        });
        task.content = content;
        task.revision = task.revision.checked_add(1).ok_or("revision exhausted")?;
        task.updated = stamp();
        task.author = author.into();
        self.save(&task)?;
        Ok(task)
    }

    fn check(&self, id: &str, content: &Draft, tasks: &[Task]) -> Result<(), String> {
        validate(content)?;
        for dep in &content.depends_on {
            if dep == id {
                return Err("a task cannot depend on itself".into());
            }
            let target = tasks
                .iter()
                .find(|t| &t.id == dep)
                .ok_or_else(|| format!("unknown prerequisite {dep}"))?;
            if matches!(content.state, State::Active | State::Review | State::Done)
                && target.content.state != State::Done
            {
                return Err(format!("prerequisite {dep} is not done"));
            }
            let mut pending = vec![dep.as_str()];
            let mut seen = std::collections::BTreeSet::new();
            while let Some(current) = pending.pop() {
                if current == id {
                    return Err("prerequisites would form a cycle".into());
                }
                if seen.insert(current)
                    && let Some(t) = tasks.iter().find(|t| t.id == current)
                {
                    pending.extend(t.content.depends_on.iter().map(String::as_str));
                }
            }
        }
        // Reopening a prerequisite must not invalidate already-started dependents.
        if content.state != State::Done
            && tasks.iter().any(|t| {
                t.id != id
                    && t.content.depends_on.iter().any(|d| d == id)
                    && matches!(t.content.state, State::Active | State::Review | State::Done)
            })
        {
            return Err(
                "cannot reopen a prerequisite while a dependent is active, in review or done"
                    .into(),
            );
        }
        Ok(())
    }

    fn save(&self, task: &Task) -> Result<(), String> {
        let path = self.root.join(format!("{}.json", task.id));
        let temporary = self.root.join(format!("{}.tmp", task.id));
        let data = serde_json::to_vec_pretty(task).map_err(|e| e.to_string())?;
        let mut file = fs::File::create(&temporary).map_err(|e| e.to_string())?;
        file.write_all(&data)
            .and_then(|_| file.write_all(b"\n"))
            .and_then(|_| file.sync_all())
            .map_err(|e| e.to_string())?;
        fs::rename(&temporary, &path).map_err(|e| e.to_string())?;
        Ok(())
    }
}

fn validate_author(author: &str) -> Result<(), String> {
    if author.trim().is_empty() || author.len() > 200 {
        return Err("writer name must contain 1 to 200 bytes".into());
    }
    Ok(())
}

fn validate(content: &Draft) -> Result<(), String> {
    if content.title.trim().is_empty() {
        return Err("a task needs a title".into());
    }
    if content.title.len() > 240 {
        return Err("title exceeds 240 bytes".into());
    }
    if content.state == State::Blocked && content.blocker.trim().is_empty() {
        return Err("blocked work needs a reason".into());
    }
    if content.state == State::Active && content.owner.trim().is_empty() {
        return Err("active work needs an owner".into());
    }
    if content.state != State::Blocked && !content.blocker.trim().is_empty() {
        return Err("clear the blocker when leaving blocked state".into());
    }
    if serde_json::to_vec(content)
        .map_err(|e| e.to_string())?
        .len()
        > 64 * 1024
    {
        return Err("task content exceeds 64 KiB".into());
    }
    let mut unique = std::collections::BTreeSet::new();
    if content
        .depends_on
        .iter()
        .any(|id| !valid_id(id) || !unique.insert(id))
    {
        return Err("prerequisites must be unique task ids".into());
    }
    Ok(())
}

/// The coordination directory for a binary project file.
pub fn beside(project: &Path) -> PathBuf {
    let mut path = project.as_os_str().to_os_string();
    path.push(".work");
    path.into()
}

#[cfg(test)]
mod tests {
    use super::*;
    fn store() -> Store {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        Store::new(std::env::temp_dir().join(format!("e5r-work-{}-{unique}", std::process::id())))
    }
    fn draft(title: &str) -> Draft {
        Draft {
            title: title.into(),
            ..Draft::default()
        }
    }
    #[test]
    fn stale_handoffs_cannot_overwrite_and_history_survives() {
        let s = store();
        let t = s.create(draft("Trace input"), "human").unwrap();
        let mut d = t.content.clone();
        d.state = State::Active;
        d.owner = "agent".into();
        d.next = "Inspect main".into();
        let updated = s.update(&t.id, 1, d.clone(), "agent").unwrap();
        assert_eq!(updated.revision, 2);
        assert!(
            s.update(&t.id, 1, d, "human")
                .unwrap_err()
                .contains("conflict")
        );
        let loaded = s.list().unwrap();
        assert_eq!(loaded[0].history[0].author, "human");
        assert_eq!(loaded[0].content.owner, "agent");
        fs::remove_dir_all(&s.root).unwrap();
    }
    #[test]
    fn readiness_cycles_and_reopening_are_enforced() {
        let s = store();
        let a = s.create(draft("Find parser"), "human").unwrap();
        let mut d = draft("Trace parser");
        d.depends_on.push(a.id.clone());
        let b = s.create(d.clone(), "agent").unwrap();
        assert!(
            !s.board()
                .unwrap()
                .tasks
                .iter()
                .find(|r| r.task.id == b.id)
                .unwrap()
                .ready
        );
        let mut cycle = a.content.clone();
        cycle.depends_on.push(b.id.clone());
        assert!(
            s.update(&a.id, 1, cycle, "human")
                .unwrap_err()
                .contains("cycle")
        );
        d.state = State::Active;
        d.owner = "agent".into();
        assert!(s.update(&b.id, 1, d.clone(), "agent").is_err());
        let mut done = a.content.clone();
        done.state = State::Done;
        s.update(&a.id, 1, done, "human").unwrap();
        s.update(&b.id, 1, d, "agent").unwrap();
        assert!(s.update(&a.id, 2, a.content, "human").is_err());
        fs::remove_dir_all(&s.root).unwrap();
    }
    #[test]
    fn simultaneous_claims_have_only_one_winner() {
        let s = store();
        let task = s.create(draft("Claim parser analysis"), "human").unwrap();
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
        let handles: Vec<_> = ["agent-a", "agent-b"]
            .into_iter()
            .map(|author| {
                let root = s.root.clone();
                let barrier = barrier.clone();
                let id = task.id.clone();
                let mut content = task.content.clone();
                content.state = State::Active;
                content.owner = author.into();
                std::thread::spawn(move || {
                    barrier.wait();
                    Store::new(root).update(&id, 1, content, author)
                })
            })
            .collect();
        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
        let loaded = s.list().unwrap();
        assert_eq!(loaded[0].revision, 2);
        assert_eq!(loaded[0].history.len(), 1);
        assert!(matches!(
            loaded[0].content.owner.as_str(),
            "agent-a" | "agent-b"
        ));
        fs::remove_dir_all(&s.root).unwrap();
    }
    #[test]
    fn invalid_or_corrupt_work_is_visible() {
        let s = store();
        let mut d = draft("Review parser");
        d.state = State::Blocked;
        assert!(s.create(d, "agent").is_err());
        fs::write(s.root.join("T-0001.json"), "broken").unwrap();
        assert!(s.board().is_err());
        fs::remove_dir_all(&s.root).unwrap();
    }
}
