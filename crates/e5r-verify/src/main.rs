//! `e5r-verify`: export binaries for the Lean checker.
//!
//! `e5r-verify IMAGE.elf` is the V0 research export (strict RV32I subset).
//! `e5r-verify flash --board BOARD.json [--namespace NS] IMAGE.elf` exports
//! the flash contents a board boots from.
//! `e5r-verify ram-image (--ram BASE:SIZE | --board BOARD.json) --mapping paddr=vaddr
//! [--max-file N] [--max-file-bytes N] [--namespace NS] --out DIR IMAGE.elf` exports the
//! initial RAM a loader writes for a RAM-resident ELF (`docs/ram-image-export.md`).
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
        Some("ram-image") => ram_image(&args[1..]),
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
                  ram-image (--ram BASE:SIZE | --board BOARD.json) --mapping paddr=vaddr \
                  [--max-file N] [--max-file-bytes N] [--namespace NS] --out DIR IMAGE.elf | \
                  check JOB.json [--resume] [--out RESULT.json] | verify-result RESULT.json | \
                  bundle JOB.json --out DIR"
                .into(),
        ),
    }
}

fn number(s: &str) -> Result<u64, String> {
    match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16),
        None => s.parse(),
    }
    .map_err(|e| format!("{s}: {e}"))
}

fn ram_image(args: &[String]) -> Result<String, String> {
    let (mut ram, mut board, mut mapping, mut out, mut elf) = (None, None, None, None, None);
    let (mut max_file, mut max_file_bytes) = (None, None);
    let mut ns = "Image".to_string();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{a} needs a value"));
        match a.as_str() {
            "--ram" => ram = Some(value()?),
            "--board" => board = Some(value()?),
            "--mapping" => mapping = Some(value()?),
            "--max-file" => max_file = Some(number(&value()?)?),
            "--max-file-bytes" => max_file_bytes = Some(number(&value()?)?),
            "--namespace" => ns = value()?,
            "--out" => out = Some(value()?),
            _ if elf.is_none() && !a.starts_with('-') => elf = Some(a.clone()),
            _ => return Err(format!("unexpected argument {a}")),
        }
    }
    if mapping.as_deref() != Some(e5r_verify::ram::MAPPING) {
        return Err(format!(
            "ram-image needs --mapping {} (the only supported policy)",
            e5r_verify::ram::MAPPING
        ));
    }
    let (base, size) = match (ram, board) {
        (Some(r), None) => {
            let (b, s) = r.split_once(':').ok_or("--ram takes BASE:SIZE")?;
            (number(b)?, number(s)?)
        }
        (None, Some(path)) => {
            let text = std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}"))?;
            let b = e5r_verify::board::Board::parse(&text)?;
            let mut rams = b.memory.iter().filter(|r| r.kind == "ram");
            match (rams.next(), rams.next()) {
                (Some(r), None) => (number(&r.base)?, number(&r.size)?),
                _ => return Err(format!("board {} needs exactly one ram region", b.id)),
            }
        }
        _ => return Err("ram-image needs exactly one of --ram BASE:SIZE and --board".into()),
    };
    let mut policy = e5r_verify::ram::Policy::new(base, size);
    policy.max_file = max_file.unwrap_or(policy.max_file);
    policy.max_file_bytes = max_file_bytes.unwrap_or(policy.max_file_bytes);
    let out = out.ok_or("ram-image needs --out DIR")?;
    let elf = elf.ok_or("ram-image needs an ELF path")?;
    let bytes = std::fs::read(&elf).map_err(|e| format!("{elf}: {e}"))?;
    let m = e5r_verify::ram::export(&bytes, policy, &ns, std::path::Path::new(&out))?;
    Ok(format!(
        "{out}: {} PT_LOADs, {} file bytes, {} zero bytes, ELF sha256 {}\n",
        m["segments"].as_array().unwrap().len(),
        m["totals"]["file_bytes"],
        m["totals"]["zero_bytes"],
        m["elf"]["sha256"].as_str().unwrap()
    ))
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
