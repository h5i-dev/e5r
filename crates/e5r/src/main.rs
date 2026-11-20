//! `e5r`: check a RISC-V binary against the e5r profile, record its
//! structure, and export it to Lean 4.

use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "\
e5r: a formal-verification-friendly RISC-V profile

usage:
  e5r check FILE [--json]          check every function against the profile
  e5r annotate FILE -o OUT         write FILE with an .e5r.struct section to OUT
  e5r cc [CLANG ARGS] SOURCES... -o OUT
                                   compile and link C or assembly into the profile,
                                   record .e5r.struct and check (docs/isa/toolchain.md)
  e5r export FILE --namespace NS [-o OUT.lean]
                                   export .text and every conforming function to Lean
  e5r disasm FILE                  list the code with its block/loop structure
  e5r --version

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
    // (`e5r disasm FILE | head`) ends the command quietly instead of making
    // `println!` panic on the closed pipe.
    let mut out = String::new();
    let code = match run(&args, &mut out) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("e5r: {e}");
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
            eprintln!("e5r: writing the output: {e}");
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

fn read(path: &str) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|e| format!("{path}: {e}"))
}

fn json_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn run(args: &[String], out: &mut String) -> Result<ExitCode, String> {
    let Some(cmd) = args.first() else {
        say!(out, "{USAGE}");
        return Ok(ExitCode::from(2));
    };
    match cmd.as_str() {
        "--help" | "-h" | "help" => {
            say!(out, "{USAGE}");
            Ok(ExitCode::SUCCESS)
        }
        "--version" | "-V" => {
            say!(out, "e5r {}", env!("CARGO_PKG_VERSION"));
            Ok(ExitCode::SUCCESS)
        }
        "check" => {
            let file = args.get(1).ok_or("check: FILE missing")?;
            let bytes = read(file)?;
            let bin = e5r::load(&bytes)?;
            let reports = bin.check();
            let bad = reports.iter().filter(|r| r.result.is_err()).count();
            if args.iter().any(|a| a == "--json") {
                let fs: Vec<String> = reports
                    .iter()
                    .map(|r| {
                        let body = match &r.result {
                            Ok(m) => format!(
                                "\"conforms\":true,\"frame\":{},\"callees\":[{}]",
                                m.frame,
                                m.callees
                                    .iter()
                                    .map(|c| c.to_string())
                                    .collect::<Vec<_>>()
                                    .join(",")
                            ),
                            Err(vs) => format!(
                                "\"conforms\":false,\"violations\":[{}]",
                                vs.iter()
                                    .map(|v| format!(
                                        "{{\"addr\":{},\"rule\":{},\"detail\":{}}}",
                                        v.addr,
                                        json_str(v.rule),
                                        json_str(&v.detail)
                                    ))
                                    .collect::<Vec<_>>()
                                    .join(",")
                            ),
                        };
                        format!(
                            "{{\"name\":{},\"entry\":{},{body}}}",
                            json_str(&r.name),
                            r.entry
                        )
                    })
                    .collect();
                say!(
                    out,
                    "{{\"file\":{},\"metadata\":{},\"functions\":[{}]}}",
                    json_str(file),
                    bin.recorded.is_some(),
                    fs.join(",")
                );
            } else {
                for r in &reports {
                    match &r.result {
                        Ok(m) => say!(
                            out,
                            "ok   {} {:#x} frame {} callees {}",
                            r.name,
                            r.entry,
                            m.frame,
                            m.callees.len()
                        ),
                        Err(vs) => {
                            say!(out, "FAIL {} {:#x}", r.name, r.entry);
                            for v in vs {
                                say!(out, "     {v}");
                            }
                        }
                    }
                }
                say!(
                    out,
                    "{} of {} functions conform ({})",
                    reports.len() - bad,
                    reports.len(),
                    if bin.recorded.is_some() {
                        "checked against .e5r.struct"
                    } else {
                        "structure recovered"
                    }
                );
            }
            Ok(if bad == 0 {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            })
        }
        "annotate" => {
            let file = args.get(1).ok_or("annotate: FILE missing")?;
            let dst = opt(args, "-o").ok_or("annotate: -o OUT missing")?;
            match e5r::annotate(std::path::Path::new(file), std::path::Path::new(dst))? {
                Ok((n, bytes)) => {
                    say!(
                        out,
                        "{dst}: {n} functions, {bytes} bytes of {}",
                        e5r::meta::SECTION
                    );
                    Ok(ExitCode::SUCCESS)
                }
                Err(vs) => {
                    for v in vs {
                        eprintln!("{v}");
                    }
                    Ok(ExitCode::from(1))
                }
            }
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
            let report = e5r::cc::build(&rest, std::path::Path::new(dst))?;
            out.push_str(&report.text);
            Ok(if report.conforms {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            })
        }
        "export" => {
            let file = args.get(1).ok_or("export: FILE missing")?;
            let ns = opt(args, "--namespace").ok_or("export: --namespace NS missing")?;
            let bytes = read(file)?;
            let bin = e5r::load(&bytes)?;
            let mut metas = Vec::new();
            for r in bin.check() {
                match r.result {
                    Ok(m) => metas.push(m),
                    Err(vs) => eprintln!("e5r: skipping {} ({} violations)", r.name, vs.len()),
                }
            }
            let name = Path::new(file)
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            let text = e5r::lean::export(&bin, &metas, ns, &name)?;
            match opt(args, "-o") {
                Some(dst) => std::fs::write(dst, text).map_err(|e| format!("{dst}: {e}"))?,
                None => out.push_str(&text),
            }
            Ok(ExitCode::SUCCESS)
        }
        "disasm" => {
            let file = args.get(1).ok_or("disasm: FILE missing")?;
            let bytes = read(file)?;
            let bin = e5r::load(&bytes)?;
            for (f, r) in bin.funcs.iter().zip(bin.check()) {
                say!(out, "\n{} {:#x}:", f.name, f.entry);
                let nodes = match &r.result {
                    Ok(m) => m.nodes.clone(),
                    Err(vs) => {
                        for v in vs {
                            say!(out, "  ; {v}");
                        }
                        vec![]
                    }
                };
                let mut marks: Vec<(u64, bool, usize, &'static str)> = Vec::new();
                fn walk(
                    ns: &[e5r::profile::Node],
                    d: usize,
                    m: &mut Vec<(u64, bool, usize, &'static str)>,
                ) {
                    for n in ns {
                        let k = match n.kind {
                            e5r::profile::Kind::Block => "block",
                            e5r::profile::Kind::Loop => "loop",
                        };
                        m.push((n.start, true, d, k));
                        walk(&n.children, d + 1, m);
                        m.push((n.end, false, d, k));
                    }
                }
                walk(&nodes, 0, &mut marks);
                for (i, &w) in f.words.iter().enumerate() {
                    let pc = f.entry + 4 * i as u64;
                    for &(_, _, d, k) in marks.iter().filter(|m| m.0 == pc && !m.1) {
                        say!(out, "  {:ind$}end {k}", "", ind = 2 * d);
                    }
                    for &(_, _, d, k) in marks.iter().filter(|m| m.0 == pc && m.1) {
                        say!(out, "  {:ind$}{k} {{", "", ind = 2 * d);
                    }
                    let depth = marks.iter().filter(|m| m.1 && m.0 <= pc).count()
                        - marks.iter().filter(|m| !m.1 && m.0 <= pc).count();
                    let text = e5r::isa::decode(w)
                        .map(|i| i.asm(pc))
                        .unwrap_or_else(|| format!(".word {w:#010x}"));
                    say!(
                        out,
                        "  {:ind$}{pc:8x}: {w:08x}  {text}",
                        "",
                        ind = 2 * depth
                    );
                }
                for &(_, _, d, k) in marks.iter().filter(|m| m.0 == f.end() && !m.1) {
                    say!(out, "  {:ind$}end {k}", "", ind = 2 * d);
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        other => Err(format!("unknown command {other}\n{USAGE}")),
    }
}
