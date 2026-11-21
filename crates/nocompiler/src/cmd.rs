//! The core commands, as library functions: `check`, `annotate`, `cc`,
//! `export` and `disasm`. The `nocompiler` binary (crates/nocompiler-cli) only
//! parses arguments and calls these; add or change a core command here.
//!
//! Every command writes its standard output into `out` (the caller prints it
//! once, so a reader that closes the pipe early ends the command quietly) and
//! returns its exit status: `Ok(0)` success, `Ok(1)` a function violates the
//! profile, `Err(_)` a usage or input error (exit status 2).

use std::path::Path;

/// `writeln!` into the output buffer; formatting into a `String` cannot fail.
macro_rules! say {
    ($out:expr, $($t:tt)*) => {{
        use std::fmt::Write as _;
        let _ = writeln!($out, $($t)*);
    }};
}

/// Exit status of a command that found a profile violation.
pub const VIOLATION: u8 = 1;
/// Exit status of a usage or input error.
pub const USAGE_ERROR: u8 = 2;

fn read(path: &Path) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn file_name(path: &Path) -> String {
    path.file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default()
}

/// A JSON string literal.
pub fn json_str(s: &str) -> String {
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

fn slot_json(s: &crate::profile::Slot) -> String {
    match s.kind {
        crate::profile::SlotKind::Save(r) => format!("{{\"off\":{},\"save\":\"{r}\"}}", s.off),
        crate::profile::SlotKind::Spill => format!("{{\"off\":{},\"spill\":true}}", s.off),
    }
}

/// `nocompiler check FILE [--json]`: check every function against the profile:
/// its level (L0, L1, L2) and, below L2, why.
pub fn check(file: &Path, json: bool, out: &mut String) -> Result<u8, String> {
    let bytes = read(file)?;
    let bin = crate::load(&bytes)?;
    let reports = bin.check();
    let bad = reports.iter().filter(|r| r.result.is_err()).count();
    let viol = |vs: &[crate::profile::Violation]| {
        vs.iter()
            .map(|v| {
                format!(
                    "{{\"addr\":{},\"rule\":{},\"detail\":{}}}",
                    v.addr,
                    json_str(v.rule),
                    json_str(&v.detail)
                )
            })
            .collect::<Vec<_>>()
            .join(",")
    };
    if json {
        let fs: Vec<String> = reports
            .iter()
            .map(|r| {
                let level = match r.level {
                    Some(l) => format!("\"{l:?}\""),
                    None => "null".into(),
                };
                let body = match &r.result {
                    Ok(m) => format!(
                        "\"conforms\":true,\"frame\":{},\"callees\":[{}],\"slots\":[{}],\"ranges\":[{}],\"missed\":[{}]",
                        m.frame,
                        m.callees.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(","),
                        m.slots.iter().map(slot_json).collect::<Vec<_>>().join(","),
                        m.ranges
                            .iter()
                            .map(|g| format!(
                                "{{\"off\":{},\"len\":{},\"source\":\"{:?}\"}}",
                                g.off, g.len, g.source
                            ))
                            .collect::<Vec<_>>()
                            .join(","),
                        viol(&r.missed)
                    ),
                    Err(vs) => format!("\"conforms\":false,\"violations\":[{}]", viol(vs)),
                };
                format!(
                    "{{\"name\":{},\"entry\":{},\"level\":{level},{body}}}",
                    json_str(&r.name),
                    r.entry
                )
            })
            .collect();
        say!(
            out,
            "{{\"file\":{},\"metadata\":{},\"functions\":[{}]}}",
            json_str(&file.to_string_lossy()),
            bin.recorded.is_some(),
            fs.join(",")
        );
    } else {
        for r in &reports {
            let level = r.level.map_or("--".to_string(), |l| format!("{l:?}"));
            match &r.result {
                Ok(m) => {
                    say!(
                        out,
                        "{level}   {} {:#x} frame {} callees {} slots {} ranges {}",
                        r.name,
                        r.entry,
                        m.frame,
                        m.callees.len(),
                        m.slots.len(),
                        m.ranges.len()
                    );
                    for g in &m.ranges {
                        say!(
                            out,
                            "     range [{}, {}) length from {:?}",
                            g.off,
                            g.off + g.len,
                            g.source
                        );
                    }
                    for v in &r.missed {
                        say!(out, "     not L2: {v}");
                    }
                }
                Err(vs) => {
                    say!(out, "{level}   FAIL {} {:#x}", r.name, r.entry);
                    for v in vs {
                        say!(out, "     {v}");
                    }
                }
            }
        }
        let l2 = reports
            .iter()
            .filter(|r| r.level == Some(crate::profile::Level::L2))
            .count();
        say!(
            out,
            "{} of {} functions conform, {l2} at L2 ({})",
            reports.len() - bad,
            reports.len(),
            if bin.recorded.is_some() {
                "checked against .nocompiler.struct"
            } else {
                "structure recovered"
            }
        );
    }
    Ok(if bad == 0 { 0 } else { VIOLATION })
}

/// `nocompiler annotate FILE -o OUT`: write FILE with a `.nocompiler.struct`
/// section to OUT. Violations go to standard error.
pub fn annotate(file: &Path, dst: &Path, out: &mut String) -> Result<u8, String> {
    match crate::annotate(file, dst)? {
        Ok((n, bytes)) => {
            say!(
                out,
                "{}: {n} functions, {bytes} bytes of {}",
                dst.display(),
                crate::meta::SECTION
            );
            Ok(0)
        }
        Err(vs) => {
            for v in vs {
                eprintln!("{v}");
            }
            Ok(VIOLATION)
        }
    }
}

/// `nocompiler cc [CLANG ARGS] SOURCES... -o OUT`: compile and link into the
/// profile, record `.nocompiler.struct` and check (docs/isa/toolchain.md).
/// `args` are passed to clang as given (without `-o OUT`).
pub fn cc(args: &[String], dst: &Path, out: &mut String) -> Result<u8, String> {
    let report = crate::cc::build(args, dst)?;
    out.push_str(&report.text);
    Ok(if report.conforms { 0 } else { VIOLATION })
}

/// `nocompiler export FILE --namespace NS [--format chunks] [-o OUT.lean]`: export
/// `.text` and every conforming function to Lean; with `chunks`, in the format
/// of lean/NoCompiler/Image.lean, "Code in chunks". Without `dst` the text goes
/// to `out`.
pub fn export(
    file: &Path,
    ns: &str,
    chunks: bool,
    lean_level_check: bool,
    dst: Option<&Path>,
    out: &mut String,
) -> Result<u8, String> {
    let bytes = read(file)?;
    let bin = crate::load(&bytes)?;
    let mut metas = Vec::new();
    for r in bin.check() {
        match r.result {
            Ok(m) => metas.push(m),
            Err(vs) => eprintln!("nocompiler: skipping {} ({} violations)", r.name, vs.len()),
        }
    }
    let text =
        crate::lean::export_with(&bin, &metas, ns, &file_name(file), chunks, lean_level_check)?;
    match dst {
        Some(dst) => std::fs::write(dst, text).map_err(|e| format!("{}: {e}", dst.display()))?,
        None => out.push_str(&text),
    }
    Ok(0)
}

/// `nocompiler module FILE --namespace NS [--format chunks] [-o OUT]`: the
/// relocatable module of a linked binary and its layout, as Lean
/// (crate::module); with `chunks`, the module in chunks and no layout
/// (`module::lean_chunks`, lean/NoCompiler/ModuleChunks.lean).
pub fn module(
    file: &Path,
    ns: &str,
    chunks: bool,
    dst: Option<&Path>,
    out: &mut String,
) -> Result<u8, String> {
    let bytes = read(file)?;
    let bin = crate::load(&bytes)?;
    let m = crate::module::of_binary(&bin)?;
    for f in &m.skipped {
        eprintln!(
            "nocompiler: skipping {} (not relocatable: {})",
            f.name, f.reason
        );
    }
    let sha = crate::sha256::hex(&crate::sha256::digest(&bytes));
    let text = if chunks {
        crate::module::lean_chunks(&m, ns, &file_name(file), &sha)?
    } else {
        crate::module::lean(&m, ns, &file_name(file), &sha)
    };
    match dst {
        Some(dst) => std::fs::write(dst, text).map_err(|e| format!("{}: {e}", dst.display()))?,
        None => out.push_str(&text),
    }
    Ok(0)
}

/// `nocompiler ledger FILE [--proofs TSV]`: the ledger entries of a binary's
/// module (docs/isa/ledger.md), one JSON object per line. TSV lines are
/// `function<TAB>theorem<TAB>spec`.
pub fn ledger(file: &Path, proofs: Option<&Path>, out: &mut String) -> Result<u8, String> {
    let bytes = read(file)?;
    let bin = crate::load(&bytes)?;
    let m = crate::module::of_binary(&bin)?;
    for f in &m.skipped {
        eprintln!(
            "nocompiler: skipping {} (not relocatable: {})",
            f.name, f.reason
        );
    }
    let mut p = std::collections::BTreeMap::new();
    if let Some(t) = proofs {
        let text = std::fs::read_to_string(t).map_err(|e| format!("{}: {e}", t.display()))?;
        for l in text
            .lines()
            .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        {
            let c: Vec<&str> = l.split('\t').collect();
            let [f, th, sp] = c[..] else {
                return Err(format!(
                    "{}: `{l}`: want function, theorem, spec",
                    t.display()
                ));
            };
            p.insert(f.to_string(), (th.to_string(), sp.to_string()));
        }
    }
    out.push_str(&crate::module::ledger_json(&crate::module::ledger(
        &bin, &m, &p,
    )));
    Ok(0)
}

/// `nocompiler asm FILE -o OUT.o`: assemble the structured text into a
/// relocatable object (docs/isa/asm.md). Status 1 when a function does not
/// conform (nothing is written).
pub fn asm(file: &Path, dst: &Path, out: &mut String) -> Result<u8, String> {
    let text = std::fs::read_to_string(file).map_err(|e| format!("{}: {e}", file.display()))?;
    let o = match crate::text::assemble(&text) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("{}: {e}", file.display());
            return Ok(1);
        }
    };
    let bytes = crate::text::write_object(&o)?;
    std::fs::write(dst, &bytes).map_err(|e| format!("{}: {e}", dst.display()))?;
    say!(
        out,
        "{}: {} functions ({}), {} data sections",
        dst.display(),
        o.funcs.len(),
        o.funcs
            .iter()
            .map(|a| format!("{} {:?}", a.func.name, a.meta.level))
            .collect::<Vec<_>>()
            .join(", "),
        o.data.len()
    );
    Ok(0)
}

/// `nocompiler sim FILE [--stdin IN] [--function F] [--json] [--fuel N]`: run
/// the binary in the simulated performance oracle (docs/isa/sim.md). The
/// program's own output goes to standard output, the report to standard
/// error. Status: the program's exit status, or 3 if it faulted.
pub fn sim(
    file: &Path,
    stdin: Option<&Path>,
    function: Option<&str>,
    json: bool,
    fuel: Option<u64>,
) -> Result<u8, String> {
    let bytes = read(file)?;
    let input = match stdin {
        Some(p) => std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()))?,
        None => Vec::new(),
    };
    let m = crate::sim::Model::inorder5();
    let mut out = Vec::new();
    let r = crate::sim::run(&bytes, &input, &mut out, &m, fuel.unwrap_or(10_000_000_000))?;
    crate::sim::write_out(&out);
    if json {
        eprintln!("{}", crate::sim::report_json(&r, &m));
    } else {
        eprint!("{}", crate::sim::report_text(&r, &m, function));
    }
    Ok(match r.exit {
        Some(c) => c as u8,
        None => 3,
    })
}

/// `nocompiler refine A.elf B.elf FUNC [--func-b NAME] [--namespace NS -o OUT.lean]`:
/// the diff of the two functions' block/loop trees (docs/isa/refine.md, item
/// 5): the unchanged instructions as lockstep pairs and the changed
/// intervals as regions, printed, and with `-o` as Lean.
#[allow(clippy::too_many_arguments)] // one per CLI option
pub fn refine(
    a_file: &Path,
    b_file: &Path,
    func: &str,
    func_b: Option<&str>,
    ns: Option<&str>,
    dst: Option<&Path>,
    images: Option<(&str, &str)>,
    bv: bool,
    out: &mut String,
) -> Result<u8, String> {
    let (ab, bb) = (read(a_file)?, read(b_file)?);
    let (ba, bbn) = (crate::load(&ab)?, crate::load(&bb)?);
    let pick = |bin: &crate::Binary,
                name: &str,
                file: &Path|
     -> Result<(u64, Vec<u32>, Vec<crate::profile::Node>), String> {
        let f = bin
            .funcs
            .iter()
            .find(|f| f.name == name)
            .ok_or_else(|| format!("{}: no function {name}", file.display()))?;
        let r = bin
            .check()
            .into_iter()
            .find(|r| r.entry == f.entry)
            .unwrap();
        let nodes = r
            .result
            .map(|m| m.nodes)
            .map_err(|_| format!("{}: {name} is below L1", file.display()))?;
        Ok((f.entry, f.words.clone(), nodes))
    };
    let (ea, wa, na) = pick(&ba, func, a_file)?;
    let (eb, wb, nb) = pick(&bbn, func_b.unwrap_or(func), b_file)?;
    let a = crate::treediff::Side {
        entry: ea,
        words: &wa,
        nodes: &na,
    };
    let b = crate::treediff::Side {
        entry: eb,
        words: &wb,
        nodes: &nb,
    };
    let d = crate::treediff::diff(&a, &b)?;
    out.push_str(&crate::treediff::summary(&d, &a, &b));
    if let Some(dst) = dst {
        let ns = ns.ok_or("refine: -o needs --namespace NS")?;
        let title = format!(
            "{} in {} (A) against {} (B)",
            func,
            file_name(a_file),
            file_name(b_file)
        );
        let proofs = images.map(|(ia, ib)| crate::treediff::Proofs {
            img_a: ia,
            img_b: ib,
            id_a: crate::lean::ident(func),
            id_b: crate::lean::ident(func_b.unwrap_or(func)),
            bv,
        });
        std::fs::write(
            dst,
            crate::treediff::lean(&d, &a, &b, ns, &title, proofs.as_ref()),
        )
        .map_err(|e| format!("{}: {e}", dst.display()))?;
    }
    Ok(0)
}

/// `nocompiler disasm FILE [FUNC]`: list the code with its block/loop
/// structure; every function, or only the one named `only`.
pub fn disasm(file: &Path, only: Option<&str>, out: &mut String) -> Result<u8, String> {
    let bytes = read(file)?;
    let bin = crate::load(&bytes)?;
    if let Some(name) = only
        && !bin.funcs.iter().any(|f| f.name == name)
    {
        return Err(format!("disasm: no function {name} in {}", file.display()));
    }
    // The structured text (docs/isa/asm.md), which `asm` reads back; the
    // address listing when the code has no relocatable form.
    match crate::text::print(&bin, only) {
        Ok(t) => {
            out.push_str(&t);
            return Ok(0);
        }
        Err(e) => say!(
            out,
            "; no structured text ({e}); the address listing instead"
        ),
    }
    listing(&bin, only, out)
}

/// The address listing: every word with its address, nested by the tree.
pub fn listing(bin: &crate::Binary, only: Option<&str>, out: &mut String) -> Result<u8, String> {
    for (f, r) in bin.funcs.iter().zip(bin.check()) {
        if only.is_some_and(|n| n != f.name) {
            continue;
        }
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
            ns: &[crate::profile::Node],
            d: usize,
            m: &mut Vec<(u64, bool, usize, &'static str)>,
        ) {
            for n in ns {
                let k = match n.kind {
                    crate::profile::Kind::Block => "block",
                    crate::profile::Kind::Loop => "loop",
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
            let text = crate::isa::decode(w)
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
    Ok(0)
}
