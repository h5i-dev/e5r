//! `e5r`: check a RISC-V binary against the e5r profile, record its
//! structure, and export it to Lean 4.

use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "\
e5r: a formal-verification-friendly RISC-V profile

usage:
  e5r check FILE [--json]          check every function against the profile
  e5r annotate FILE -o OUT         write FILE with an .e5r.struct section to OUT
  e5r export FILE --namespace NS [-o OUT.lean]
                                   export .text and every conforming function to Lean
  e5r disasm FILE                  list the code with its block/loop structure
  e5r --version

Exit status: 0 success, 1 a function violates the profile, 2 usage or input error.
docs/isa/ describes the profile, the metadata and the proof workflow.";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("e5r: {e}");
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

fn run(args: &[String]) -> Result<ExitCode, String> {
    let Some(cmd) = args.first() else {
        println!("{USAGE}");
        return Ok(ExitCode::from(2));
    };
    match cmd.as_str() {
        "--help" | "-h" | "help" => {
            println!("{USAGE}");
            Ok(ExitCode::SUCCESS)
        }
        "--version" | "-V" => {
            println!("e5r {}", env!("CARGO_PKG_VERSION"));
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
                println!(
                    "{{\"file\":{},\"metadata\":{},\"functions\":[{}]}}",
                    json_str(file),
                    bin.recorded.is_some(),
                    fs.join(",")
                );
            } else {
                for r in &reports {
                    match &r.result {
                        Ok(m) => println!(
                            "ok   {} {:#x} frame {} callees {}",
                            r.name,
                            r.entry,
                            m.frame,
                            m.callees.len()
                        ),
                        Err(vs) => {
                            println!("FAIL {} {:#x}", r.name, r.entry);
                            for v in vs {
                                println!("     {v}");
                            }
                        }
                    }
                }
                println!(
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
            let out = opt(args, "-o").ok_or("annotate: -o OUT missing")?;
            let bytes = read(file)?;
            let bin = e5r::load(&bytes)?;
            let reports = bin.check();
            let mut metas = Vec::new();
            for r in reports {
                match r.result {
                    Ok(m) => metas.push(m),
                    Err(vs) => {
                        for v in vs {
                            eprintln!("{} {v}", r.name);
                        }
                        return Ok(ExitCode::from(1));
                    }
                }
            }
            let data = e5r::meta::encode(&metas);
            let tmp = format!("{out}.e5r-struct.tmp");
            std::fs::write(&tmp, &data).map_err(|e| format!("{tmp}: {e}"))?;
            let objcopy = std::env::var("E5R_OBJCOPY").unwrap_or_else(|_| "llvm-objcopy".into());
            let verb = if bin.recorded.is_some() {
                "--update-section"
            } else {
                "--add-section"
            };
            let st = std::process::Command::new(&objcopy)
                .arg(format!("{verb}={}={tmp}", e5r::meta::SECTION))
                .arg(file)
                .arg(out)
                .status()
                .map_err(|e| format!("{objcopy}: {e} (set E5R_OBJCOPY)"));
            let _ = std::fs::remove_file(&tmp);
            if !st?.success() {
                return Err(format!("{objcopy} failed"));
            }
            println!(
                "{out}: {} functions, {} bytes of {}",
                metas.len(),
                data.len(),
                e5r::meta::SECTION
            );
            Ok(ExitCode::SUCCESS)
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
                Some(out) => std::fs::write(out, text).map_err(|e| format!("{out}: {e}"))?,
                None => print!("{text}"),
            }
            Ok(ExitCode::SUCCESS)
        }
        "disasm" => {
            let file = args.get(1).ok_or("disasm: FILE missing")?;
            let bytes = read(file)?;
            let bin = e5r::load(&bytes)?;
            for (f, r) in bin.funcs.iter().zip(bin.check()) {
                println!("\n{} {:#x}:", f.name, f.entry);
                let nodes = match &r.result {
                    Ok(m) => m.nodes.clone(),
                    Err(vs) => {
                        for v in vs {
                            println!("  ; {v}");
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
                        println!("  {:ind$}end {k}", "", ind = 2 * d);
                    }
                    for &(_, _, d, k) in marks.iter().filter(|m| m.0 == pc && m.1) {
                        println!("  {:ind$}{k} {{", "", ind = 2 * d);
                    }
                    let depth = marks.iter().filter(|m| m.1 && m.0 <= pc).count()
                        - marks.iter().filter(|m| !m.1 && m.0 <= pc).count();
                    let text = e5r::isa::decode(w)
                        .map(|i| i.asm(pc))
                        .unwrap_or_else(|| format!(".word {w:#010x}"));
                    println!("  {:ind$}{pc:8x}: {w:08x}  {text}", "", ind = 2 * depth);
                }
                for &(_, _, d, k) in marks.iter().filter(|m| m.0 == f.end() && !m.1) {
                    println!("  {:ind$}end {k}", "", ind = 2 * d);
                }
            }
            Ok(ExitCode::SUCCESS)
        }
        other => Err(format!("unknown command {other}\n{USAGE}")),
    }
}
