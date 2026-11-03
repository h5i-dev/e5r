//! `e5r-verify`: assembly-level formal verification with Lean 4. It proves
//! properties of PTX kernels and RISC-V firmware binaries, and exports the
//! binaries the Lean proofs are about.
//!
//! `e5r-verify IMAGE.elf` is the V0 research export (strict RV32I subset).
//! `e5r-verify flash --board BOARD.json [--namespace NS] IMAGE.elf` exports
//! the flash contents a board boots from.
//! `e5r-verify ram-image (--ram BASE:SIZE | --board BOARD.json) --mapping paddr=vaddr
//! [--max-file N] [--max-file-bytes N] [--namespace NS] --out DIR IMAGE.elf` exports the
//! initial RAM a loader writes for a RAM-resident ELF (`docs/verification/ram-image-export.md`).
//! `e5r-verify check JOB.json [--resume] [--out RESULT.json]` rebuilds and rechecks a
//! verification job and prints its `e5r.verify.result.v1` document; the exit
//! status is 0 only for `proved`.
//! `e5r-verify verify-result RESULT.json` says whether a stored result still
//! describes the current inputs.
//! `e5r-verify bundle JOB.json --out DIR` writes a self-contained directory
//! whose `recheck.sh` rechecks the proofs with only the pinned Lean.
//! `e5r-verify ptx export|check|run …` exports PTX to Lean, proves or refutes
//! a kernel against its spec, and runs differential-test cases
//! (`docs/verification/ptx.md`, "Command line"; `e5r-verify ptx --help`).
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
        Some("ptx") => ptx(&args[1..]),
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
        Some("--help") | Some("-h") => Ok(HELP.into()),
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
            "usage: e5r-verify (ptx check|check|verify-result|bundle|flash|ram-image) ... \
                  or IMAGE.elf; run `e5r-verify --help`"
                .into(),
        ),
    }
}

const HELP: &str = "\
e5r-verify: assembly-level formal verification with Lean 4

Proves properties of the code a compiler emitted, checked by the Lean kernel.

PTX kernels (docs/verification/ptx.md):
  e5r-verify ptx check FILE.ptx --spec SPEC.json [--proof PROOF.lean] [--out RESULT.json]
      prove memory safety, race freedom and correctness, or replay a counterexample
      exit status: 0 proved, 1 refuted, 2 unsupported, 3 unknown, 4 error, 64 usage
  e5r-verify ptx export|run ...      see `e5r-verify ptx --help`

RISC-V firmware binaries (docs/verification/firmware.md):
  e5r-verify check JOB.json [--resume] [--out RESULT.json]
      rebuild and recheck a verification job; exit status 0 only for proved
  e5r-verify verify-result RESULT.json
      say whether a stored result still describes the current inputs
  e5r-verify bundle JOB.json --out DIR
      write a directory whose recheck.sh needs only the pinned Lean

Exporting a binary to Lean:
  e5r-verify flash --board BOARD.json [--namespace NS] IMAGE.elf
  e5r-verify ram-image (--ram BASE:SIZE | --board BOARD.json) --mapping paddr=vaddr
                       [--max-file N] [--max-file-bytes N] [--namespace NS] --out DIR IMAGE.elf
  e5r-verify IMAGE.elf               the V0 research export (strict RV32I subset)
";

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
            e5r_verify::ram::board_window(&e5r_verify::board::Board::parse(&text)?)?
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

fn ptx(args: &[String]) -> Result<String, String> {
    match args.first().map(String::as_str) {
        Some("export") => ptx_export(&args[1..]),
        Some("check") => ptx_check(&args[1..]),
        Some("run") => ptx_run(&args[1..]),
        Some("--help") | Some("-h") | None => Ok(PTX_USAGE.into()),
        // `ptx [--namespace NS] [--name NAME] FILE.ptx`, kept for existing scripts
        _ => ptx_export(args),
    }
}

const PTX_USAGE: &str = "\
e5r-verify ptx export [--namespace NS] [--name NAME] FILE.ptx
    print the Lean `Ptx.Module` of FILE.ptx (after the token round trip)
e5r-verify ptx check FILE.ptx --spec SPEC.json [--project DIR] [--out RESULT.json]
                     [--keep DIR] [--timeout SECS] [--memory-mb MB] [--no-search]
                     [--proof PROOF.lean]
    prove or refute SPEC for the kernel; prints an e5r.ptx.result.v1 document
    exit status: 0 proved, 1 refuted, 2 unsupported, 3 unknown, 4 error, 64 usage
e5r-verify ptx run --cases CASES FILE.ptx
    run differential-test cases on the (untrusted) concrete interpreter
";

fn ptx_export(args: &[String]) -> Result<String, String> {
    let (mut ns, mut name, mut file) = ("Ptx.Kernels.Module".to_string(), None, None);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--namespace" => ns = it.next().cloned().ok_or("--namespace needs a value")?,
            "--name" => name = Some(it.next().cloned().ok_or("--name needs a value")?),
            _ if file.is_none() && !a.starts_with('-') => file = Some(a.clone()),
            _ => return Err(format!("unexpected argument {a}")),
        }
    }
    let file = file.ok_or("ptx needs a .ptx file")?;
    let bytes = std::fs::read(&file).map_err(|e| format!("{file}: {e}"))?;
    let src = String::from_utf8(bytes.clone()).map_err(|e| format!("{file}: {e}"))?;
    let header = format!(
        "Generated by `e5r-verify ptx` from {} (sha256 {}).\n\
         Do not edit: scripts/check-lean-ptx.sh regenerates it and refuses a stale copy.",
        name.as_deref().unwrap_or(&file),
        e5r_verify::sha256::hex(&bytes)
    );
    e5r_ptx::export_lean(&src, &ns, &header).map_err(|e| format!("{file}: {e}"))
}

fn default_project() -> std::path::PathBuf {
    if let Ok(p) = std::env::var("E5R_PTX_PROJECT") {
        return p.into();
    }
    let here = std::path::PathBuf::from("verification/ptx");
    if here.join("lakefile.lean").exists() {
        return here;
    }
    std::env::current_exe()
        .ok()
        .and_then(|e| Some(e.parent()?.parent()?.parent()?.join("verification/ptx")))
        .unwrap_or(here)
}

fn ptx_check(args: &[String]) -> Result<String, String> {
    use e5r_verify::ptx;
    let usage = |m: String| -> ! {
        eprintln!("e5r-verify ptx check: {m}\n{PTX_USAGE}");
        std::process::exit(ptx::EXIT_USAGE)
    };
    let (mut file, mut spec, mut out, mut keep) = (None, None, None, None);
    let mut proof: Option<String> = None;
    let (mut project, mut timeout, mut memory, mut search) = (None, 600u64, 6144u64, true);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut value = || {
            it.next()
                .cloned()
                .unwrap_or_else(|| usage(format!("{a} needs a value")))
        };
        match a.as_str() {
            "--spec" => spec = Some(value()),
            "--out" => out = Some(value()),
            "--keep" => keep = Some(value()),
            "--proof" => proof = Some(value()),
            "--project" => project = Some(value()),
            "--timeout" => {
                timeout = value()
                    .parse()
                    .unwrap_or_else(|_| usage("--timeout takes seconds".into()))
            }
            "--memory-mb" => {
                memory = value()
                    .parse()
                    .unwrap_or_else(|_| usage("--memory-mb takes a number".into()))
            }
            "--no-search" => search = false,
            _ if file.is_none() && !a.starts_with('-') => file = Some(a.clone()),
            _ => usage(format!("unexpected argument {a}")),
        }
    }
    let file = file.unwrap_or_else(|| usage("needs a .ptx file".into()));
    let spec = spec.unwrap_or_else(|| usage("needs --spec SPEC.json".into()));
    let o = ptx::Options {
        ptx: file.into(),
        spec: spec.into(),
        project: project.map(Into::into).unwrap_or_else(default_project),
        keep: keep.map(Into::into),
        timeout: std::time::Duration::from_secs(timeout),
        memory_mb: memory,
        search,
        proof: proof.map(Into::into),
    };
    let (v, doc) = ptx::check(&o);
    let text = serde_json::to_string_pretty(&doc).unwrap() + "\n";
    if let Some(out) = out {
        std::fs::write(&out, &text).map_err(|e| format!("{out}: {e}"))?;
    }
    print!("{text}");
    std::process::exit(v.exit_code());
}

fn ptx_run(args: &[String]) -> Result<String, String> {
    let (mut cases, mut file) = (None, None);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--cases" => cases = it.next().cloned(),
            _ if file.is_none() && !a.starts_with('-') => file = Some(a.clone()),
            _ => return Err(format!("unexpected argument {a}")),
        }
    }
    let (cases, file) = (
        cases.ok_or("run needs --cases")?,
        file.ok_or("run needs a .ptx file")?,
    );
    let src = std::fs::read_to_string(&file).map_err(|e| format!("{file}: {e}"))?;
    let m = e5r_ptx::roundtrip(&src).map_err(|e| format!("{file}: {e}"))?;
    let text = std::fs::read_to_string(&cases).map_err(|e| format!("{cases}: {e}"))?;
    e5r_verify::ptxrun::run_cases(&m, &text)
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
