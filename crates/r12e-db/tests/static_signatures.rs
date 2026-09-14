//! Signature matching against a real distribution's static libraries.
//!
//! This is the case the feature exists for. A statically linked binary has the
//! library code inside the image and, once stripped, nothing at all to say
//! about what any of it is: several thousand functions, no names. The names
//! are not lost though, they are in the distribution's own development
//! packages, in the `.a` archives the linker copied that code out of.
//!
//! So the library here is built the way `scripts/build-siglib.sh` builds one
//! for a user: every object in every archive is analyzed, and every function a
//! symbol names becomes one signature. It is then applied to the stripped
//! binary and checked against the unstripped copy, which is the oracle.
//!
//! A wrong name is worse than no name, because the reader will believe it, so
//! the wrong count is asserted at zero and recall is a floor that only moves
//! one way. The oracle is a set of names per address rather than one name: a
//! linker puts `strlen` and `__strlen` at the same byte, and calling that
//! address either of them is right.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_analysis::{Options, Program, analyze};
use r12e_db::anchor::Anchor;
use r12e_db::signature::{Library, Signature};
use r12e_format::LoadOptions;

/// Floor on the share of the binary's named functions that get a name back.
///
/// Below the measured number with room for another distribution's glibc to be
/// built differently, because the floor is here to catch a regression and the
/// number the test prints is the measure. What keeps it off 100% is that most
/// of what a static link pulls in is short: under the shape floor a function is
/// identified by its exact bytes alone, and one relocation applied anywhere in
/// the body changes those.
const MIN_RECALL: f64 = 0.40;

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// Analysis with the parts a signature does not use switched off.
fn options() -> Options {
    Options {
        strings: false,
        xrefs: false,
        ..Options::default()
    }
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &options()))
}

/// Where the distribution keeps the static libraries this binary was linked
/// from. The compiler knows, so it is asked rather than guessed at.
fn archive(name: &str) -> Option<PathBuf> {
    let out = Command::new("gcc")
        .arg(format!("-print-file-name={name}"))
        .output()
        .ok()?;
    let path = PathBuf::from(String::from_utf8(out.stdout).ok()?.trim());
    // The compiler echoes the name back unchanged when it has no such file.
    (path.is_absolute() && path.is_file()).then_some(path)
}

/// One function's fingerprint, exactly as a signature records it.
fn anchor_of(p: &Program, f: &r12e_analysis::Function) -> Anchor {
    let insns = p.instructions(f);
    let mut body = Vec::with_capacity(f.cfg.covered_bytes() as usize);
    for b in f.cfg.blocks.values() {
        if let Some(bytes) = p.object.memory.slice(b.range.start(), b.range.len()) {
            body.extend_from_slice(bytes);
        }
    }
    Anchor::function(f.entry, &insns, &body)
}

/// Signatures for every named function in every object an archive holds.
///
/// This is what the script does through the command line, done in process so
/// the gate does not need a built binary to run.
fn signatures_of_archive(path: &Path, into: &mut Vec<Signature>) -> usize {
    let Ok(data) = std::fs::read(path) else {
        return 0;
    };
    let Ok(ar) = r12e_format::archive::open(&data) else {
        return 0;
    };
    let label = path.file_name().unwrap_or_default().to_string_lossy();
    let mut objects = 0;
    for (n, member) in ar.objects() {
        let Ok(obj) = ar.load_member(n, &LoadOptions::default()) else {
            continue;
        };
        objects += 1;
        let p = analyze(obj, &options());
        let source = format!("{label}({})", member.name);
        for f in p.functions_by_address() {
            // A name is the whole point: a signature called `sub_401000`
            // identifies nothing and a library of them matches everything.
            let Some(name) = f.raw_name() else {
                continue;
            };
            if name.is_empty() || name.ends_with("@plt") {
                continue;
            }
            into.push(Signature::new(&anchor_of(&p, f), name, &source));
        }
    }
    objects
}

/// Every name the file gives each address, so an alias is not a wrong answer.
fn names_by_address(p: &Program) -> BTreeMap<u64, BTreeSet<String>> {
    let mut out: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for s in &p.object.symbols {
        if s.is_defined_function() && !s.name.is_empty() {
            out.entry(s.addr.get()).or_default().insert(s.name.clone());
        }
    }
    for f in p.functions_by_address() {
        if let Some(n) = f.raw_name() {
            if !n.is_empty() {
                out.entry(f.entry.get()).or_default().insert(n.to_string());
            }
        }
    }
    out
}

#[test]
fn a_stripped_static_binary_gets_its_library_names_back() {
    let (Some(named), Some(stripped)) =
        (open("hello.static.a64"), open("hello.static.a64.stripped"))
    else {
        return;
    };
    // libm is in the link line even when nothing calls it, and libc_nonshared
    // carries the handful of stubs libc.a leaves out.
    let archives: Vec<PathBuf> = ["libc.a", "libm.a", "libc_nonshared.a"]
        .iter()
        .filter_map(|n| archive(n))
        .collect();
    if archives.is_empty() {
        return;
    }

    let mut collected = Vec::new();
    let mut objects = 0;
    for a in &archives {
        objects += signatures_of_archive(a, &mut collected);
    }
    let raw = collected.len();
    let library = Library::build(collected);
    assert!(
        !library.is_empty(),
        "no signatures came out of {archives:?}"
    );

    let truth = names_by_address(&named);
    let mut recovered = 0usize;
    let mut wrong: Vec<String> = Vec::new();
    for f in stripped.functions_by_address() {
        let Some(found) = library.identify(&anchor_of(&stripped, f)) else {
            continue;
        };
        // A function the unstripped copy does not name cannot be checked, and
        // a name claimed for it is not evidence either way.
        let Some(real) = truth.get(&f.entry.get()) else {
            continue;
        };
        if real.contains(&found.signature.name) {
            recovered += 1;
        } else {
            wrong.push(format!(
                "{}: called it {:?}, it is {:?} ({}, from {})",
                f.entry,
                found.signature.name,
                real,
                found.resolution.as_str(),
                found.signature.source
            ));
        }
    }

    let claimed = stripped
        .functions_by_address()
        .filter(|f| library.identify(&anchor_of(&stripped, f)).is_some())
        .count();
    let checkable = stripped
        .functions_by_address()
        .filter(|f| truth.contains_key(&f.entry.get()))
        .count();
    let recall = recovered as f64 / checkable.max(1) as f64;
    println!(
        "{raw} signatures ({} after merging) from {objects} objects in {} archives",
        library.len(),
        archives.len()
    );
    println!(
        "{claimed} functions identified, {recovered} of {checkable} names \
         recovered ({:.1}%), {} wrong",
        recall * 100.0,
        wrong.len()
    );

    assert!(
        wrong.is_empty(),
        "{} names are wrong, which is worse than having none:\n  {}",
        wrong.len(),
        wrong.join("\n  ")
    );
    assert!(
        recall >= MIN_RECALL,
        "recovered {recovered} of {checkable} ({recall:.3}), floor is {MIN_RECALL}"
    );
}

#[test]
fn a_library_from_one_distribution_does_not_name_another_program() {
    // The other direction, and the one that matters more: applying a library
    // to a binary none of its code is in must produce no name at all, not a
    // plausible-looking wrong one.
    let Some(p) = open("insndiff.a64") else {
        return;
    };
    let Some(a) = archive("libc.a") else {
        return;
    };
    let mut collected = Vec::new();
    signatures_of_archive(&a, &mut collected);
    let library = Library::build(collected);
    if library.is_empty() {
        return;
    }
    let truth = names_by_address(&p);
    for f in p.functions_by_address() {
        let Some(found) = library.identify(&anchor_of(&p, f)) else {
            continue;
        };
        let Some(real) = truth.get(&f.entry.get()) else {
            continue;
        };
        assert!(
            real.contains(&found.signature.name),
            "{} is {real:?} and a libc library called it {:?}",
            f.entry,
            found.signature.name
        );
    }
}
