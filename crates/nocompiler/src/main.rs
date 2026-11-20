//! `nocompiler`: check a RISC-V binary against the nocompiler profile, record its
//! structure, and export it to Lean 4.

use nocompiler::cmd;
use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "\
nocompiler: a formal-verification-friendly RISC-V profile

usage:
  nocompiler check FILE [--json]          check every function against the profile
  nocompiler annotate FILE -o OUT         write FILE with an .nocompiler.struct section to OUT
  nocompiler cc [CLANG ARGS] SOURCES... -o OUT
                                   compile and link C or assembly into the profile,
                                   record .nocompiler.struct and check (docs/isa/toolchain.md)
  nocompiler export FILE --namespace NS [-o OUT.lean]
                                   export .text and every conforming function to Lean
  nocompiler module FILE --namespace NS [-o OUT.lean]
                                   the relocatable module of a linked binary, and its layout
  nocompiler disasm FILE                  list the code with its block/loop structure
  nocompiler --version

Exit status: 0 success, 1 a function violates the profile, 2 usage or input error.
docs/isa/ describes the profile, the metadata and the proof workflow.";

/// `writeln!` into the output buffer; formatting into a `String` cannot fail.
macro_rules! say {
    ($out:expr, $($t:tt)*) => {{
        use std::fmt::Write as _;
        let _ = writeln!($out, $($t)*);
    }};
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // Output is collected and written once, so that a reader that stops early
    // (`nocompiler disasm FILE | head`) ends the command quietly instead of making
    // `println!` panic on the closed pipe.
    let mut out = String::new();
    let code = match run(&args, &mut out) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("nocompiler: {e}");
            ExitCode::from(2)
        }
    };
    use std::io::Write as _;
    let mut stdout = std::io::stdout().lock();
    match stdout
        .write_all(out.as_bytes())
        .and_then(|()| stdout.flush())
    {
        Ok(()) => code,
        Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => code,
        Err(e) => {
            eprintln!("nocompiler: writing the output: {e}");
            ExitCode::from(2)
        }
    }
}

fn opt<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
}

/// Argument parsing only; the commands are in `nocompiler::cmd`.
fn run(args: &[String], out: &mut String) -> Result<ExitCode, String> {
    let Some(cmd) = args.first() else {
        say!(out, "{USAGE}");
        return Ok(ExitCode::from(2));
    };
    let file = |what: &str| -> Result<&Path, String> {
        args.get(1)
            .map(Path::new)
            .ok_or_else(|| format!("{what}: FILE missing"))
    };
    let code = match cmd.as_str() {
        "--help" | "-h" | "help" => {
            say!(out, "{USAGE}");
            0
        }
        "--version" | "-V" => {
            say!(out, "nocompiler {}", env!("CARGO_PKG_VERSION"));
            0
        }
        "check" => cmd::check(file("check")?, args.iter().any(|a| a == "--json"), out)?,
        "annotate" => {
            let dst = opt(args, "-o").ok_or("annotate: -o OUT missing")?;
            cmd::annotate(file("annotate")?, Path::new(dst), out)?
        }
        "cc" => {
            let dst = opt(args, "-o").ok_or("cc: -o OUT missing")?;
            let mut rest = Vec::new();
            let mut i = 1;
            while i < args.len() {
                if args[i] == "-o" {
                    i += 2;
                    continue;
                }
                rest.push(args[i].clone());
                i += 1;
            }
            cmd::cc(&rest, Path::new(dst), out)?
        }
        "export" => {
            let ns = opt(args, "--namespace").ok_or("export: --namespace NS missing")?;
            cmd::export(file("export")?, ns, opt(args, "-o").map(Path::new), out)?
        }
        "module" => {
            let ns = opt(args, "--namespace").ok_or("module: --namespace NS missing")?;
            cmd::module(file("module")?, ns, opt(args, "-o").map(Path::new), out)?
        }
        "disasm" => cmd::disasm(file("disasm")?, out)?,
        other => return Err(format!("unknown command {other}\n{USAGE}")),
    };
    Ok(ExitCode::from(code))
}
