//! `e5r-verify`: export binaries for the Lean checker.
//!
//! `e5r-verify IMAGE.elf` is the V0 research export (strict RV32I subset).
//! `e5r-verify flash --board BOARD.json [--namespace NS] IMAGE.elf` exports
//! the flash contents a board boots from.
//! `e5r-verify check JOB.json [--resume] [--out RESULT.json]` rebuilds and rechecks a
//! verification job and prints its `e5r.verify.result.v1` document; the exit
//! status is 0 only for `proved`.
//! `e5r-verify verify-result RESULT.json` says whether a stored result still
//! describes the current inputs.
//! `e5r-verify bundle JOB.json --out DIR` writes a self-contained directory
//! whose `recheck.sh` rechecks the proofs with only the pinned Lean.
use std::process::ExitCode;

fn run(args: Vec<String>) -> Result<String, String> {
    let read = |p: &str| std::fs::read(p).map_err(|e| format!("{p}: {e}"));
    match args.first().map(String::as_str) {
        Some("flash") => {
            let mut board = None;
            let mut ns = "Image".to_string();
            let mut elf = None;
            let mut it = args[1..].iter();
            while let Some(a) = it.next() {
                match a.as_str() {
                    "--board" => board = it.next().cloned(),
                    "--namespace" => ns = it.next().cloned().ok_or("--namespace needs a value")?,
                    _ if elf.is_none() && !a.starts_with('-') => elf = Some(a.clone()),
                    _ => return Err(format!("unexpected argument {a}")),
                }
            }
            let board = board.ok_or("flash needs --board BOARD.json")?;
            let elf = elf.ok_or("flash needs an ELF path")?;
            let text = String::from_utf8(read(&board)?).map_err(|e| e.to_string())?;
            let w = e5r_verify::board::Board::parse(&text)?.windows()?;
            e5r_verify::flash::export_flash(&read(&elf)?, w, &ns)
        }
        Some("check") => {
            let mut out = None;
            let mut job = None;
            let mut resume = false;
            let mut it = args[1..].iter();
            while let Some(a) = it.next() {
                match a.as_str() {
                    "--out" => out = it.next().cloned(),
                    "--resume" => resume = true,
                    _ if job.is_none() && !a.starts_with('-') => job = Some(a.clone()),
                    _ => return Err(format!("unexpected argument {a}")),
                }
            }
            let job = job.ok_or("check needs a job file")?;
            let result = e5r_verify::job::run(std::path::Path::new(&job), resume);
            let text = serde_json::to_string_pretty(&result).unwrap() + "\n";
            if let Some(out) = out {
                std::fs::write(&out, &text).map_err(|e| format!("{out}: {e}"))?;
            }
            let code = match result["status"].as_str() {
                Some("proved") => 0,
                Some("failed") => 10,
                Some("unsupported") => 11,
                Some("resource_exhausted") => 12,
                _ => 13,
            };
            print!("{text}");
            std::process::exit(code);
        }
        Some("bundle") => {
            let (job, out) = match (args.get(1), args.get(2), args.get(3)) {
                (Some(job), Some(flag), Some(out)) if flag == "--out" => (job, out),
                _ => return Err("usage: e5r-verify bundle JOB.json --out DIR".into()),
            };
            let out = std::path::Path::new(out);
            if out.exists() {
                return Err(format!("{}: already exists", out.display()));
            }
            e5r_verify::job::bundle(std::path::Path::new(job), out)?;
            Ok(format!(
                "{}: bundle written; run its recheck.sh with the pinned Lean\n",
                out.display()
            ))
        }
        Some("verify-result") => {
            let path = args.get(1).ok_or("verify-result needs a result file")?;
            let text = String::from_utf8(read(path)?).map_err(|e| e.to_string())?;
            let result: serde_json::Value =
                serde_json::from_str(&text).map_err(|e| format!("{path}: {e}"))?;
            let changed = e5r_verify::job::stale(&result)?;
            if changed.is_empty() {
                Ok(format!("{path}: current\n"))
            } else {
                Err(format!("{path}: stale: {}", changed.join(", ")))
            }
        }
        Some(path) if args.len() == 1 && !path.starts_with('-') => e5r_verify::export(&read(path)?),
        _ => Err(
            "usage: e5r-verify IMAGE.elf | flash --board BOARD.json [--namespace NS] IMAGE.elf | \
                  check JOB.json [--resume] [--out RESULT.json] | verify-result RESULT.json | \
                  bundle JOB.json --out DIR"
                .into(),
        ),
    }
}

fn main() -> ExitCode {
    match run(std::env::args().skip(1).collect()) {
        Ok(source) => {
            print!("{source}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("e5r-verify: {e}");
            ExitCode::FAILURE
        }
    }
}
