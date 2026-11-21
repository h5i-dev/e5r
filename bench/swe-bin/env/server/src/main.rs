//! `swe-bin-env`: serve swe-bin as an OpenEnv environment.

use std::path::PathBuf;
use std::time::Duration;

use clap::{Parser, ValueEnum};
use swe_bin_kernel as k;

#[derive(Clone, Copy, ValueEnum)]
enum Mode {
    /// SWE-bench: the agent gets the buggy binary and edits it (the default).
    Patch,
    /// SWE-bench-derived (function-level from-scratch): the gold patch's functions are stubbed.
    Scratch,
}

#[derive(Parser)]
#[command(about = "Serve swe-bin (SWE-bench Multilingual C/Rust on riscv64 binaries) as an OpenEnv environment")]
struct Args {
    #[command(flatten)]
    serve: senv::ServeArgs,
    /// The mode of every episode.
    #[arg(long, value_enum, default_value = "patch")]
    mode: Mode,
    /// The work root of the conversion (artifacts/, work/, dl/).
    #[arg(long, env = "SWB", default_value = "/mnt/scratch/ec2-user/swe-bin")]
    swb: PathBuf,
    /// bench/swe-bin of the NoCompiler checkout (tasks/, convert/).
    #[arg(long, default_value = concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))]
    bench: PathBuf,
    #[arg(long, default_value = "nocompiler")]
    nocompiler: PathBuf,
    /// The Python that runs convert/harness.py.
    #[arg(long, default_value = "/mnt/scratch/ec2-user/swe-bin/venv/bin/python")]
    python: PathBuf,
    /// Where episode directories go.
    #[arg(long, default_value = "/mnt/scratch/ec2-user/swe-bin/episodes")]
    episodes: PathBuf,
    #[arg(long, default_value_t = 60)]
    tool_timeout_secs: u64,
    #[arg(long, default_value_t = 3600)]
    test_timeout_secs: u64,
    #[arg(long, default_value_t = 256 * 1024)]
    max_output_bytes: usize,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let a = Args::parse();
    let tasks_dir = a.bench.join("tasks");
    let dataset = a.swb.join("dl/cr.jsonl");
    let tasks = swe_bin_env::load_tasks(&tasks_dir, &a.swb, &dataset)?;
    eprintln!("swe-bin: {} kept tasks from {}", tasks.len(), tasks_dir.display());
    std::fs::create_dir_all(&a.episodes)?;
    swe_bin_env::configure(swe_bin_env::Config {
        harness: a.bench.join("convert/harness.py"),
        swb: a.swb,
        tasks_dir,
        dataset,
        episodes: a.episodes,
        nocompiler: a.nocompiler,
        python: a.python,
        mode: match a.mode {
            Mode::Patch => k::Mode::Patch,
            Mode::Scratch => k::Mode::Scratch,
        },
        tool_timeout: Duration::from_secs(a.tool_timeout_secs),
        test_timeout: Duration::from_secs(a.test_timeout_secs),
        max_output: a.max_output_bytes,
        tasks,
    })?;
    senv::run(swe_bin_env::SweBinEnv, a.serve).await
}
