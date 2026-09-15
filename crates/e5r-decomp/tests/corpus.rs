//! A measurement, not a gate.
//!
//! The structuring quality numbers the roadmap publishes are corpus numbers,
//! and the twenty fixtures `quality.rs` holds a ceiling over are too few to
//! tell a real movement from noise. This walks every built fixture and prints
//! the totals, so two builds can be compared. Ignored by default because it is
//! slow and asserts nothing.

use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program};
use e5r_format::LoadOptions;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(e5r_analysis::analyze(obj, &Options::default()))
}

#[test]
#[ignore = "a measurement over the whole corpus, printed rather than asserted"]
fn corpus_structuring_totals() {
    let Some(dir) = build_dir() else { return };
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| e.file_type().is_ok_and(|t| t.is_file()))
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();

    let (mut gotos, mut lost, mut functions, mut unstructured, mut bytes) = (0usize, 0, 0, 0, 0);
    for name in names {
        let Some(p) = open(&name) else { continue };
        let targets: Vec<&e5r_analysis::Function> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .collect();
        if targets.is_empty() {
            continue;
        }
        // Exactly the path `no_block_is_lost` takes. Note when reading an
        // `E5R_GOTO_STATS` histogram from this run that it counts more
        // structurings than there are functions here: two passes, over the
        // targets and over the callees around them that never reach the
        // output.
        for d in e5r_api::decompile_program(&p, &targets).functions {
            functions += 1;
            gotos += d.gotos;
            lost += d.lost;
            unstructured += usize::from(d.gotos > 0);
            bytes += d.text.len();
        }
    }
    println!(
        "CORPUS functions={functions} gotos={gotos} lost={lost} \
         unstructured={unstructured} share={:.4} bytes={bytes}",
        unstructured as f64 / functions.max(1) as f64
    );
}

/// The whole corpus's decompiled text, for comparing two structurings.
///
/// A change that moves output size has to show what moved. Dumping every
/// function twice and comparing the multiset of lines is what proves a
/// difference is the gotos and the labels rather than code appearing or
/// disappearing. Writes to the path in `E5R_DUMP`.
#[test]
#[ignore = "a dump for comparing two builds, written rather than asserted"]
fn corpus_dump() {
    use std::io::Write;

    let Some(dir) = build_dir() else { return };
    let Some(out) = std::env::var_os("E5R_DUMP") else {
        return;
    };
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| e.file_type().is_ok_and(|t| t.is_file()))
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();

    let mut w = std::io::BufWriter::new(std::fs::File::create(out).unwrap());
    for name in names {
        let Some(p) = open(&name) else { continue };
        let targets: Vec<&e5r_analysis::Function> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .collect();
        if targets.is_empty() {
            continue;
        }
        for d in e5r_api::decompile_program(&p, &targets).functions {
            let _ = writeln!(w, "// {name} {}", d.name);
            let _ = w.write_all(d.text.as_bytes());
        }
    }
}
