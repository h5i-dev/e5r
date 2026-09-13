//! The demangler measured against `c++filt`, over every mangled symbol in the
//! system's C++ libraries.
//!
//! Two numbers, kept apart because they are not the same thing. A name we
//! decline to demangle is a gap, and the caller still sees the mangled form,
//! which is honest. A name we demangle *differently* from c++filt is a bug.
//!
//! The bug ceiling is not zero yet, which is a real admission. The remaining
//! disagreements are substitution-table corners in heavily nested templates,
//! where an index resolves to a sibling type. They are display-only: a
//! demangled name is shown, never acted on, and the alternative to a slightly
//! wrong `std::basic_string<...>` is an unreadable mangled string. Both
//! numbers ratchet in one direction and neither is allowed to slip.

use std::process::{Command, Stdio};

use r12e_types::itanium;

/// Floor on names demangled exactly as c++filt does. Only ever raised.
const MIN_COVERAGE: f64 = 0.93;
/// Ceiling on names demangled differently. Only ever lowered.
const MAX_WRONG: f64 = 0.025;

/// Mangled names from the system libraries, via `nm`.
fn symbols() -> Vec<String> {
    let mut out = Vec::new();
    for lib in [
        "/usr/lib/aarch64-linux-gnu/libstdc++.so.6",
        "/usr/lib/aarch64-linux-gnu/libc.so.6",
        "/lib/aarch64-linux-gnu/libstdc++.so.6",
    ] {
        if !std::path::Path::new(lib).is_file() {
            continue;
        }
        let Ok(o) = Command::new("nm")
            .args(["-D", "--defined-only"])
            .arg(lib)
            .output()
        else {
            continue;
        };
        for line in String::from_utf8_lossy(&o.stdout).lines() {
            if let Some(name) = line.split_whitespace().last() {
                // `nm -D` appends `@@VERSION`, which is not part of the
                // mangled name and which c++filt will not demangle.
                let name = name.split('@').next().unwrap_or(name);
                if name.starts_with("_Z") {
                    out.push(name.to_string());
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// What c++filt makes of the same names, one per line.
///
/// Names go as arguments in batches rather than through stdin. Feeding a child
/// tens of thousands of lines on a pipe and only then reading its output
/// deadlocks both processes, and handing it a file on stdin did not return
/// either; arguments have neither problem.
fn expected(names: &[String]) -> Option<Vec<String>> {
    let mut out = Vec::with_capacity(names.len());
    for chunk in names.chunks(200) {
        let result = Command::new("c++filt")
            .args(chunk)
            .stdin(Stdio::null())
            .output()
            .ok()?;
        if !result.status.success() {
            return None;
        }
        let text = String::from_utf8_lossy(&result.stdout);
        let lines: Vec<&str> = text.lines().collect();
        if lines.len() != chunk.len() {
            return None;
        }
        out.extend(lines.into_iter().map(|s| s.to_string()));
    }
    Some(out)
}

/// c++filt and this demangler disagree about whitespace in a few places that
/// carry no meaning; compare with it removed.
fn normalize(s: &str) -> String {
    s.replace(", ", ",").replace(' ', "")
}

#[test]
fn itanium_matches_cxxfilt() {
    let names = symbols();
    if names.len() < 100 {
        return; // no C++ library here
    }
    let Some(want) = expected(&names) else { return };
    if want.len() != names.len() {
        return;
    }

    let mut matched = 0usize;
    let mut declined = 0usize;
    let mut wrong: Vec<String> = Vec::new();

    for (name, want) in names.iter().zip(&want) {
        // c++filt echoes a name it cannot read, which means it has no opinion.
        if want == name {
            continue;
        }
        match itanium::demangle(name) {
            None => declined += 1,
            Some(got) if normalize(&got) == normalize(want) => matched += 1,
            Some(got) => wrong.push(format!("{name}\n  c++filt {want}\n  ours    {got}")),
        }
    }

    let total = matched + declined + wrong.len();
    assert!(total > 100, "only {total} names compared");

    let wrong_rate = wrong.len() as f64 / total as f64;
    assert!(
        wrong_rate <= MAX_WRONG,
        "{} of {total} names ({:.2}%) demangle differently from c++filt, \
         ceiling is {:.1}%\nfirst 5:\n{}",
        wrong.len(),
        wrong_rate * 100.0,
        MAX_WRONG * 100.0,
        wrong.iter().take(5).cloned().collect::<Vec<_>>().join("\n")
    );

    let coverage = matched as f64 / total as f64;
    assert!(
        coverage >= MIN_COVERAGE,
        "demangled {:.1}% of {total} names exactly, floor is {:.0}% \
         ({declined} declined, {} wrong)",
        coverage * 100.0,
        MIN_COVERAGE * 100.0,
        wrong.len()
    );
    println!(
        "c++filt parity: {total} names, {matched} exact ({:.1}%), {declined} declined, \
         {} wrong ({:.2}%)",
        coverage * 100.0,
        wrong.len(),
        wrong_rate * 100.0
    );
}

/// A work list, like the decoder reports. Ignored by default.
#[test]
#[ignore]
fn cxxfilt_report() {
    let names = symbols();
    let Some(want) = expected(&names) else { return };
    let mut wrong = 0;
    let mut declined = 0;
    let mut wrong_examples: Vec<String> = Vec::new();
    let mut declined_examples: Vec<String> = Vec::new();
    for (name, want) in names.iter().zip(&want) {
        if want == name {
            continue;
        }
        match itanium::demangle(name) {
            None => {
                declined += 1;
                if declined_examples.len() < 8 {
                    declined_examples.push(format!("DECLINED {name}\n  want {want}"));
                }
            }
            Some(got) if normalize(&got) == normalize(want) => {}
            Some(got) => {
                wrong += 1;
                if wrong_examples.len() < 12 {
                    wrong_examples.push(format!("WRONG {name}\n  want {want}\n  got  {got}"));
                }
            }
        }
    }
    println!("{} names, {wrong} wrong, {declined} declined", names.len());
    for e in wrong_examples.iter().chain(&declined_examples) {
        println!("{e}");
    }
}
