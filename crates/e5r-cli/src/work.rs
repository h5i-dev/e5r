//! Project task commands; the database owns readiness and mutation rules.
use crate::{
    json,
    out::{Out, outln},
};
use clap::Subcommand;
use e5r_db::work::{Draft, Priority, Store};
use std::path::{Path, PathBuf};

#[derive(Subcommand)]
pub enum Command {
    /// Show tasks, readiness, blockers and review requests.
    List {
        /// Emit the same snapshot used by the dashboard.
        #[arg(long)]
        json: bool,
    },
    /// Add a task, optionally from a full Draft JSON file.
    Add {
        /// Concrete outcome. Required unless --input is supplied.
        #[arg(required_unless_present = "input", conflicts_with = "input")]
        title: Option<String>,
        /// Full task content as JSON (see docs/dashboard.md).
        #[arg(long)]
        input: Option<PathBuf>,
        /// Responsible person or agent.
        #[arg(long, default_value = "", conflicts_with = "input")]
        owner: String,
        /// Concrete next action.
        #[arg(long, default_value = "", conflicts_with = "input")]
        next: String,
        /// Context and acceptance criteria.
        #[arg(long, default_value = "", conflicts_with = "input")]
        description: String,
        /// Supporting paths, addresses, commands or URLs; repeatable.
        #[arg(long, conflicts_with = "input")]
        evidence: Vec<String>,
        /// Prerequisite task id; repeatable.
        #[arg(long, conflicts_with = "input")]
        depends_on: Vec<String>,
        /// high, normal or low.
        #[arg(long, default_value = "normal", value_parser = ["high", "normal", "low"], conflicts_with = "input")]
        priority: String,
        /// Writer, recorded in the task history.
        #[arg(long)]
        author: Option<String>,
    },
    /// Replace content, refusing an update based on a stale revision.
    Update {
        /// Task id from list.
        id: String,
        /// Revision from the last read.
        #[arg(long)]
        revision: u64,
        /// Full task content as JSON.
        #[arg(long)]
        input: PathBuf,
        /// Writer, recorded in the task history.
        #[arg(long)]
        author: Option<String>,
    },
}

fn read(path: &Path) -> Result<Draft, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))
}

pub fn run(w: &mut Out, project: &Path, command: &Command) -> Result<u8, String> {
    run_store(w, Store::new(e5r_db::work::beside(project)), command)
}

pub fn run_store(w: &mut Out, store: Store, command: &Command) -> Result<u8, String> {
    match command {
        Command::List { json: true } => json::emit(w, &store.board()?),
        Command::List { json: false } => {
            for row in store.board()?.tasks {
                let t = row.task;
                outln!(
                    w,
                    "{}  r{}  {:?}  {}  owner: {}",
                    t.id,
                    t.revision,
                    t.content.state,
                    t.content.title,
                    if t.content.owner.is_empty() {
                        "unassigned"
                    } else {
                        &t.content.owner
                    }
                );
                if let Some(why) = row.attention {
                    outln!(w, "  attention: {why}");
                }
                if !row.waiting_on.is_empty() {
                    outln!(w, "  waiting on: {}", row.waiting_on.join(", "));
                }
                if row.ready {
                    outln!(w, "  ready to claim");
                }
                if !t.content.next.is_empty() {
                    outln!(w, "  next: {}", t.content.next);
                }
            }
            Ok(0)
        }
        Command::Add {
            title,
            input,
            owner,
            next,
            description,
            evidence,
            depends_on,
            priority,
            author,
        } => {
            let content = if let Some(path) = input {
                read(path)?
            } else {
                Draft {
                    title: title.clone().unwrap_or_default(),
                    owner: owner.clone(),
                    next: next.clone(),
                    description: description.clone(),
                    evidence: evidence.clone(),
                    depends_on: depends_on.clone(),
                    priority: match priority.as_str() {
                        "high" => Priority::High,
                        "low" => Priority::Low,
                        _ => Priority::Normal,
                    },
                    ..Draft::default()
                }
            };
            let author = author.clone().unwrap_or_else(crate::whoami);
            json::emit(w, &store.create(content, &author)?)
        }
        Command::Update {
            id,
            revision,
            input,
            author,
        } => {
            let author = author.clone().unwrap_or_else(crate::whoami);
            json::emit(w, &store.update(id, *revision, read(input)?, &author)?)
        }
    }
}
