//! A measurement, not a gate.
//!
//! The structuring quality numbers the roadmap publishes are corpus numbers,
//! and the twenty fixtures `quality.rs` holds a ceiling over are too few to
//! tell a real movement from noise. This walks every built fixture and prints
//! the totals, so two builds can be compared. Ignored by default because it is
//! slow and asserts nothing.

use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program};
use r12e_format::LoadOptions;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(r12e_analysis::analyze(obj, &Options::default()))
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
        let targets: Vec<&r12e_analysis::Function> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .collect();
        if targets.is_empty() {
            continue;
        }
        // Exactly the path `no_block_is_lost` takes. Note when reading an
        // `R12E_GOTO_STATS` histogram from this run that it counts more
        // structurings than there are functions here: two passes, over the
        // targets and over the callees around them that never reach the
        // output.
        for d in r12e_api::decompile_program(&p, &targets).functions {
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
