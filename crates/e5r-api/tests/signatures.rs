//! Signature matching measured on a binary whose names were removed.
//!
//! The oracle is the unstripped copy: signatures are built from it, applied to
//! the stripped one, and every name the matcher produces has to be the name
//! that function actually had. A wrong name is worse than no name, so the test
//! treats one as a failure and a miss as a gap with a floor.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_format::LoadOptions;

/// Floor on the share of named functions a stripped copy gets back.
const MIN_RECALL: f64 = 0.90;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

#[test]
fn a_stripped_binary_gets_its_names_back() {
    let (Some(named), Some(stripped)) = (open("hello.a64.O2"), open("hello.a64.O2.stripped"))
    else {
        return;
    };

    let library = e5r_api::collect_signatures(&named, "hello.a64.O2");
    assert!(!library.is_empty(), "no signatures were collected");

    // What each address was really called, from the unstripped copy.
    // Import thunks are excluded from libraries, so they are not what recall
    // is measured over either.
    let truth: BTreeMap<u64, String> = named
        .functions_by_address()
        .filter(|f| !f.name.as_deref().is_some_and(|n| n.ends_with("@plt")))
        .filter_map(|f| Some((f.entry.get(), f.name.clone()?)))
        .collect();

    let found = e5r_api::identify(&stripped, &library);
    let mut wrong = Vec::new();
    for identified in &found {
        match truth.get(&identified.addr.get()) {
            Some(real) if *real != identified.name => wrong.push(format!(
                "{}: called it {:?}, it is {real:?} ({})",
                identified.addr,
                identified.name,
                identified.resolution.as_str()
            )),
            // A function the unstripped copy did not name cannot be checked,
            // and claiming a name for it is not evidence of anything.
            _ => {}
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} matches name the wrong function:\n  {}",
        wrong.len(),
        found.len(),
        wrong.join("\n  ")
    );

    let recovered = found
        .iter()
        .filter(|i| truth.contains_key(&i.addr.get()))
        .count();
    let recall = recovered as f64 / truth.len().max(1) as f64;
    assert!(
        recall >= MIN_RECALL,
        "recovered {recovered} of {} names ({recall:.2}), floor is {MIN_RECALL}",
        truth.len()
    );
    println!(
        "recovered {recovered} of {} names ({recall:.2})",
        truth.len()
    );
}

#[test]
fn a_library_built_from_one_build_recognizes_another() {
    // Same source at a different optimization level is a different function,
    // and the matcher must not claim otherwise.
    let (Some(a), Some(b)) = (open("hello.a64.O0"), open("hello.a64.O2")) else {
        return;
    };
    let library = e5r_api::collect_signatures(&a, "hello.a64.O0");
    let truth: BTreeMap<u64, String> = b
        .functions_by_address()
        .filter_map(|f| Some((f.entry.get(), f.name.clone()?)))
        .collect();
    let found = e5r_api::identify(&b, &library);
    for identified in &found {
        if let Some(real) = truth.get(&identified.addr.get()) {
            assert_eq!(
                *real, identified.name,
                "a match across optimization levels named the wrong function"
            );
        }
    }
}

#[test]
fn the_library_file_survives_a_round_trip() {
    let Some(p) = open("hello.a64.O2") else {
        return;
    };
    let library = e5r_api::collect_signatures(&p, "hello");
    let text = library.to_text();
    let back = e5r_db::signature::Library::from_text(&text);
    assert_eq!(back.len(), library.len());
    assert_eq!(back.to_text(), text);
}
