//! The three gates on the compiler, over every `.slaspec` Ghidra ships.
//!
//! 1. **Byte comparison against the reference compiler.** Compile the same
//!    specification both ways and diff the decompressed payloads. Where they
//!    differ, the test says which elements differ and why, because "does not
//!    match" is not a finding.
//! 2. **Round trip through our own reader.** What we wrote must read back, and
//!    what reads back must agree with what `r12e-sleigh` parsed: the same
//!    spaces, the same registers, the same constructors, the same operands.
//!    This catches everything the byte comparison cannot, because it holds
//!    even where the reference orders things differently.
//! 3. **Cross-read by the reference.** Whether Ghidra will load a `.sla` we
//!    wrote, checked without a GUI where that is possible.
//!
//! The corpus is a Ghidra source or binary tree. Without one the tests report
//! and return, which is the convention in this repository.

mod slaload;
mod sleighc;

use std::path::{Path, PathBuf};

use r12e_sla::{Sla, model::SymbolBody};

/// Every Ghidra tree on the machine. A source checkout and a binary
/// distribution hold different sets of `.slaspec`, so both are searched.
fn ghidra_roots() -> Vec<PathBuf> {
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(v) = std::env::var("R12E_GHIDRA_DIR") {
        roots.push(PathBuf::from(v));
    }
    if let Ok(home) = std::env::var("HOME") {
        roots.push(PathBuf::from(&home).join(".local/share/ghidra-cli/ghidra"));
        roots.push(PathBuf::from(&home).join("ghidra"));
        roots.push(PathBuf::from(&home).join("Ref/ghidra"));
    }
    roots.push(PathBuf::from("/opt/ghidra"));
    roots.retain(|r| r.is_dir());
    roots
}

/// The first tree, for the things that need only one: the reference compiler
/// and the headless launcher.
fn ghidra_root() -> Option<PathBuf> {
    ghidra_roots().into_iter().next()
}

fn find(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            find(&p, ext, out);
        } else if p.extension().is_some_and(|x| x == ext) {
            out.push(p);
        }
    }
}

fn slaspecs() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for root in ghidra_roots() {
        find(&root, "slaspec", &mut out);
    }
    out.sort();
    // The same language appears in both trees; compile each one once.
    let mut seen: Vec<std::ffi::OsString> = Vec::new();
    out.retain(|p| {
        let name = p.file_name().unwrap_or_default().to_os_string();
        if seen.contains(&name) {
            return false;
        }
        seen.push(name);
        true
    });
    out
}

/// The reference compiler, if this machine has one. A distribution unpacks
/// into a versioned directory, so one level down is checked as well.
fn reference() -> Option<PathBuf> {
    for root in ghidra_roots() {
        let direct = root.join("support/sleigh");
        if direct.is_file() {
            return Some(direct);
        }
        for e in std::fs::read_dir(&root).into_iter().flatten().flatten() {
            let nested = e.path().join("support/sleigh");
            if nested.is_file() {
                return Some(nested);
            }
        }
    }
    None
}

struct Outcome {
    name: String,
    constructors: usize,
    ok: bool,
    note: String,
}

/// Gate 2, and the one that has to pass: everything we write reads back, and
/// what reads back is what the front end parsed.
#[test]
fn every_slaspec_compiles_and_reads_back() {
    let specs = slaspecs();
    if specs.is_empty() {
        println!("no Ghidra tree on this machine, skipping");
        return;
    }

    let mut parsed = 0usize;
    let mut written = 0usize;
    let mut verified = 0usize;
    let mut constructors = 0usize;
    let mut semantics_missing = 0usize;
    let mut context_sets = 0usize;
    let mut computed = 0usize;
    let mut globalsets = 0usize;
    let mut dropped = 0usize;
    let mut failures: Vec<String> = Vec::new();
    let mut rows: Vec<Outcome> = Vec::new();

    for path in &specs {
        let name = path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        let spec = match r12e_sleigh::parse_file(path) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{name}: parse: {e}"));
                continue;
            }
        };
        parsed += 1;
        let (bytes, report) = match sleighc::compile_to_bytes(&spec) {
            Ok(v) => v,
            Err(e) => {
                failures.push(format!("{name}: compile: {e}"));
                rows.push(Outcome {
                    name,
                    constructors: 0,
                    ok: false,
                    note: format!("compile: {e}"),
                });
                continue;
            }
        };
        written += 1;
        constructors += report.constructors;
        semantics_missing += report.without_semantics;
        context_sets += report.context_sets;
        computed += report.computed_operands;
        globalsets += report.globalsets;
        dropped += report.dropped_tables;

        let back = match Sla::parse(&bytes) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{name}: read back: {e}"));
                rows.push(Outcome {
                    name,
                    constructors: report.constructors,
                    ok: false,
                    note: format!("read back: {e}"),
                });
                continue;
            }
        };

        let problems = back.check();
        let mut note = String::new();
        let mut ok = problems.is_empty();
        if !ok {
            note = format!(
                "{} inconsistencies, first {:?}",
                problems.len(),
                problems[0]
            );
        }
        // The model that comes back has to be the specification again.
        if let Err(e) = agrees(&spec, &back, &report) {
            ok = false;
            note = e;
        }
        if ok {
            verified += 1;
        } else {
            failures.push(format!("{name}: {note}"));
        }
        rows.push(Outcome {
            name,
            constructors: report.constructors,
            ok,
            note,
        });
    }

    println!(
        "slaspec corpus: {} found, {parsed} parsed, {written} compiled, {verified} verified",
        specs.len()
    );
    println!(
        "{constructors} constructors written; {semantics_missing} of them have a semantic body \
         the compiler does not yet turn into p-code"
    );
    println!(
        "disassembly actions: {context_sets} context assignments, {computed} computed operands, \
         {globalsets} globalsets; {dropped} unreferenced tables dropped"
    );
    for r in rows.iter().filter(|r| !r.ok).take(20) {
        println!(
            "  FAIL {} ({} constructors): {}",
            r.name, r.constructors, r.note
        );
    }
    assert!(
        failures.is_empty(),
        "{} failures: {failures:#?}",
        failures.len()
    );
}

/// What the compiled file says must be what the specification said.
fn agrees(spec: &r12e_sleigh::Spec, back: &Sla, report: &sleighc::Report) -> Result<(), String> {
    let p = &back.program;

    let declared = spec
        .spaces
        .iter()
        .filter(|s| {
            !matches!(
                s.kind,
                r12e_sleigh::model::SpaceKind::Constant | r12e_sleigh::model::SpaceKind::Unique
            )
        })
        .count();
    // Two more than the specification declares: OTHER and unique.
    if p.spaces.len() != declared + 2 {
        return Err(format!(
            "{} spaces read back, specification declares {declared} plus OTHER and unique",
            p.spaces.len()
        ));
    }

    let registers = p.registers().count();
    if registers != spec.varnodes.len() {
        return Err(format!(
            "{registers} varnode symbols read back, specification has {}",
            spec.varnodes.len()
        ));
    }

    // A table no operand names is not written, the same way the reference
    // drops it, so the count to match is what was kept.
    let subtables = p.subtables().count();
    let kept = spec.tables.len() - report.dropped_tables;
    if subtables != kept {
        return Err(format!(
            "{subtables} subtables read back, {kept} of the specification's {} were written",
            spec.tables.len()
        ));
    }

    if p.constructor_count() != report.constructors {
        return Err(format!(
            "{} constructors read back, {} written",
            p.constructor_count(),
            report.constructors
        ));
    }

    // Every operand a constructor names must resolve to an operand symbol
    // whose own record points back at that constructor.
    for s in p.subtables() {
        let SymbolBody::Subtable { constructors, .. } = &s.body else {
            continue;
        };
        for (k, c) in constructors.iter().enumerate() {
            for (i, o) in c.operands.iter().enumerate() {
                let Some(sym) = p.symbol(*o) else {
                    return Err(format!("operand symbol {o} is missing"));
                };
                let SymbolBody::Operand { index, expr, .. } = &sym.body else {
                    return Err(format!("symbol {o} is not an operand"));
                };
                if *index != i as u64 {
                    return Err(format!(
                        "operand {o} says index {index}, constructor says {i}"
                    ));
                }
                match expr.first() {
                    Some(r12e_sla::model::Expr::OperandValue { table, ct, .. })
                        if *table == u64::from(s.id) && *ct == k as u64 => {}
                    other => {
                        return Err(format!(
                            "operand {o} points at {other:?}, expected table {} constructor {k}",
                            s.id
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// Gate 1: the byte comparison. Not a pass-or-fail gate, because the symbol
/// numbering and the decision tree are deliberately not the reference's; it
/// reports how far apart the two files are and in what.
#[test]
#[ignore = "runs the reference compiler over the whole corpus, minutes"]
fn byte_comparison_against_the_reference_compiler() {
    let Some(sleigh) = reference() else {
        println!("no reference sleigh compiler on this machine, skipping");
        return;
    };
    let specs = slaspecs();
    let tmp = std::env::temp_dir().join("r12e-sleighc");
    let _ = std::fs::create_dir_all(&tmp);

    let mut compared = 0usize;
    let mut identical = 0usize;
    let mut same_symbols = 0usize;
    let mut same_constructors = 0usize;
    let mut same_spaces = 0usize;
    let mut same_registers = 0usize;
    let mut ours_bytes = 0usize;
    let mut theirs_bytes = 0usize;
    let mut rows: Vec<String> = Vec::new();

    for path in specs.iter() {
        let out = tmp.join("ref.sla");
        let _ = std::fs::remove_file(&out);
        let status = std::process::Command::new(&sleigh)
            .arg(path)
            .arg(&out)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status();
        if !status.map(|s| s.success()).unwrap_or(false) || !out.is_file() {
            continue;
        }
        let Ok(theirs) = Sla::open(&out) else {
            continue;
        };
        let Ok(spec) = r12e_sleigh::parse_file(path) else {
            continue;
        };
        let Ok((bytes, _)) = sleighc::compile_to_bytes(&spec) else {
            continue;
        };
        let Ok(ours) = Sla::parse(&bytes) else {
            continue;
        };
        compared += 1;

        let a = r12e_sla::encode::encode(&ours.tree).expect("encodes");
        let b = r12e_sla::encode::encode(&theirs.tree).expect("encodes");
        if a == b {
            identical += 1;
            continue;
        }
        if ours.program.symbols.len() == theirs.program.symbols.len() {
            same_symbols += 1;
        }
        if ours.program.constructor_count() == theirs.program.constructor_count() {
            same_constructors += 1;
        } else {
            rows.push(format!(
                "{}: {} constructors against the reference's {}",
                path.file_name().unwrap_or_default().to_string_lossy(),
                ours.program.constructor_count(),
                theirs.program.constructor_count(),
            ));
        }
        if ours.program.spaces.len() == theirs.program.spaces.len() {
            same_spaces += 1;
        }
        if ours.program.registers().count() == theirs.program.registers().count() {
            same_registers += 1;
        }
        ours_bytes += a.len();
        theirs_bytes += b.len();
    }

    println!("byte comparison against the reference compiler, {compared} languages:");
    println!("  payload byte for byte:   {identical}");
    println!("  same number of spaces:   {same_spaces}");
    println!("  same register table:     {same_registers}");
    println!("  same symbol count:       {same_symbols}");
    println!("  same constructor count:  {same_constructors}");
    println!(
        "  payload size: {ours_bytes} against {theirs_bytes}, {:.0}% (we write no p-code)",
        100.0 * ours_bytes as f64 / theirs_bytes.max(1) as f64
    );
    for r in rows.iter().take(30) {
        println!("  {r}");
    }
}

/// Gate 3: can the reference load what we wrote? There is no headless command
/// in the shipped distribution that only parses a `.sla`, so what can be
/// checked without a GUI is recorded here rather than claimed.
#[test]
#[ignore = "needs a Ghidra install"]
fn report_whether_the_reference_can_load_our_output() {
    let Some(root) = ghidra_root() else {
        println!("no Ghidra tree, skipping");
        return;
    };
    let headless = root.join("support/analyzeHeadless");
    println!(
        "analyzeHeadless present: {}. Loading a language means importing a binary for it, \
         which builds a project and runs the analyzer, so this is reported rather than \
         asserted.",
        headless.is_file()
    );
}

/// A compiled specification has to survive being written and read on the same
/// terms as one Ghidra produced: the fixtures are small enough to check by
/// hand and they are committed, so this is the fast gate.
#[test]
fn the_committed_fixtures_compile() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let mut any = false;
    for name in ["minimal", "tokens", "subtable"] {
        let sinc = dir.join(format!("{name}.sinc"));
        if !sinc.is_file() {
            continue;
        }
        any = true;
        let text = std::fs::read_to_string(&sinc).expect("readable");
        let text = text.replace("$(ENDIAN)", "little");
        let spec = r12e_sleigh::parse_str(&text).expect("the fixture source parses");
        let (bytes, report) = sleighc::compile_to_bytes(&spec).expect("compiles");
        let back = Sla::parse(&bytes).expect("reads back");
        assert!(back.check().is_empty(), "{name}: {:?}", back.check());
        assert_eq!(
            back.program.constructor_count(),
            report.constructors,
            "{name}"
        );
        assert!(
            back.program.symbols.iter().all(|s| s.name.is_some()),
            "{name}"
        );
        println!(
            "{name}: {} symbols, {} constructors, {} bytes",
            back.program.symbols.len(),
            report.constructors,
            bytes.len()
        );
    }
    assert!(any, "the fixture sources should be present");
}

/// Write one compiled language to a file, for diffing against the reference
/// compiler's output by hand. `R12E_SPEC` names the `.slaspec`, `R12E_OUT` the
/// file to write. A diagnostic, not a gate.
#[test]
#[ignore = "diagnostic: writes one compiled language to R12E_OUT"]
fn write_one_compiled_language() {
    let Ok(spec_path) = std::env::var("R12E_SPEC") else {
        println!("set R12E_SPEC and R12E_OUT");
        return;
    };
    let out = std::env::var("R12E_OUT").unwrap_or_else(|_| "out.sla".into());
    let spec = r12e_sleigh::parse_file(Path::new(&spec_path)).expect("parses");
    let (bytes, report) = sleighc::compile_to_bytes(&spec).expect("compiles");
    std::fs::write(&out, &bytes).expect("writes");
    println!(
        "{out}: {} bytes, {} constructors, {} without p-code",
        bytes.len(),
        report.constructors,
        report.without_semantics
    );
    for n in &report.notes {
        println!("  {n}");
    }
}

// ---------------------------------------------------------- the decode gate

/// Gate 2, second half, and the strongest statement the writer can make.
///
/// `r12e-sleigh`'s decode engine is measured at zero disagreements with
/// objdump on AArch64, x86-64 and RISC-V. Compile the same specification here,
/// read the file back, rebuild a decodable model from it with
/// [`slaload`], and decode the same bytes with both. Every instruction that
/// decodes differently is something the round trip lost, and the count is the
/// number that matters.
///
/// The bytes are a deterministic sweep rather than a compiled object, so the
/// test needs no toolchain and still reaches thousands of distinct
/// constructors.
#[test]
fn a_file_we_wrote_decodes_the_way_its_source_does() {
    let langs = [
        ("AArch64", "AARCH64/data/languages/AARCH64.slaspec", 4usize),
        ("RISC-V", "RISCV/data/languages/riscv.lp64d.slaspec", 4),
        ("x86-64", "x86/data/languages/x86-64.slaspec", 16),
    ];
    let Some(root) = ghidra_roots()
        .into_iter()
        .find(|r| r.join("Ghidra/Processors").is_dir())
    else {
        println!("no Ghidra processor tree on this machine, skipping");
        return;
    };

    let mut any = false;
    let mut total_wrong = 0usize;
    for (name, rel, width) in langs {
        let path = root.join("Ghidra/Processors").join(rel);
        if !path.is_file() {
            continue;
        }
        any = true;
        let spec = r12e_sleigh::parse_file(&path).expect("the language parses");
        let (bytes, report) = sleighc::compile_to_bytes(&spec).expect("compiles");
        let back = Sla::parse(&bytes).expect("reads back");
        let loaded = slaload::load(&back.program);

        let r = compare_decodes(&spec, &loaded.spec, width);
        println!(
            "{name}: {} encodings swept, source decodes {}, the .sla we wrote decodes {}, \
             {} agree, {} differ",
            r.cases, r.source_ok, r.sla_ok, r.agree, r.differ
        );
        for e in r.examples.iter().take(4) {
            println!("    {e}");
        }
        for n in loaded.notes.iter().take(4) {
            println!("    note: {n}");
        }
        // A constructor whose pattern the compiler could only write
        // approximately is a known gap with a number, not a silent one. Where
        // there is none, a disagreement is a bug and the gate says so.
        if report.approximate_patterns == 0 {
            assert_eq!(
                r.differ, 0,
                "{name} writes every pattern exactly, so a decode must not differ"
            );
        } else {
            println!(
                "    {} constructors have a pattern this compiler cannot state exactly",
                report.approximate_patterns
            );
        }
        total_wrong += r.differ;
    }
    if !any {
        println!("no language files found, skipping");
        return;
    }
    println!("{total_wrong} disagreements over the three architectures");
    // A ceiling, not a target. Every one of these is a constructor whose
    // pattern carries a constraint that is not a bit test and that this
    // compiler could not enumerate into bits, and the number only moves down.
    assert!(
        total_wrong <= 8,
        "{total_wrong} encodings decode differently through the file we wrote, was 8"
    );
}

struct DecodeParity {
    cases: usize,
    source_ok: usize,
    sla_ok: usize,
    agree: usize,
    differ: usize,
    examples: Vec<String>,
}

/// Decode the same sweep with two specifications and compare what came out.
fn compare_decodes(a: &r12e_sleigh::Spec, b: &r12e_sleigh::Spec, width: usize) -> DecodeParity {
    const CASES: usize = 20_000;
    let mut r = DecodeParity {
        cases: 0,
        source_ok: 0,
        sla_ok: 0,
        agree: 0,
        differ: 0,
        examples: Vec::new(),
    };
    let mut da = r12e_sleigh::Decoder::new(a);
    let mut db = r12e_sleigh::Decoder::new(b);
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut buf = vec![0u8; width.max(4)];
    for _ in 0..CASES {
        for slot in buf.iter_mut() {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *slot = (state >> 24) as u8;
        }
        r.cases += 1;
        let ra = da.decode(&buf, 0x1000).ok();
        let rb = db.decode(&buf, 0x1000).ok();
        if ra.is_some() {
            r.source_ok += 1;
        }
        if rb.is_some() {
            r.sla_ok += 1;
        }
        let ta = ra.as_ref().map(|d| (d.len, d.text(a)));
        let tb = rb.as_ref().map(|d| (d.len, d.text(b)));
        if ta == tb {
            r.agree += 1;
        } else {
            r.differ += 1;
            if r.examples.len() < 8 {
                r.examples
                    .push(format!("{:02x?}: source {ta:?}, sla {tb:?}", &buf[..]));
            }
        }
    }
    r
}
