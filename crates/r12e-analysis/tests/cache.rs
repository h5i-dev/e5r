//! The on-disk cache: that a hit is the same answer, that a key which does not
//! match is a miss rather than a partial reuse, and that damage is a miss
//! rather than a panic or a lie.

mod common;

use std::path::Path;

use common::{fingerprint, load, scratch};
use r12e_analysis::{Cache, ContentHash, Options, Session, analyze};

/// A session over `name` that reads and writes `dir`.
fn cached(dir: &Path, name: &str, opts: &Options) -> r12e_analysis::Program {
    let (data, obj) = load(name).expect("fixture");
    Session::new(obj, opts.clone())
        .with_cache(Cache::at(dir), ContentHash::of(&data))
        .into_program()
}

/// Every cache file in a directory, sorted so the list is stable.
fn entries(dir: &Path) -> Vec<std::path::PathBuf> {
    let mut v: Vec<_> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.flatten()
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|e| e == "bin"))
                .collect()
        })
        .unwrap_or_default();
    v.sort();
    v
}

#[test]
fn a_second_open_gets_the_same_answer_from_disk() {
    if common::corpus().is_none() {
        return;
    }
    let dir = scratch("roundtrip");
    let opts = Options::default();
    let first = cached(&dir, "hello.a64.O2", &opts);
    assert_eq!(
        entries(&dir).len(),
        3,
        "functions, xrefs and strings each get an entry"
    );
    let second = cached(&dir, "hello.a64.O2", &opts);
    assert_eq!(fingerprint(&first), fingerprint(&second));

    // And against a run that never saw the cache, so a hit is checked against
    // the engine rather than against itself.
    let (_, obj) = load("hello.a64.O2").expect("fixture");
    assert_eq!(fingerprint(&analyze(obj, &opts)), fingerprint(&second));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn only_the_parts_that_were_asked_for_are_written() {
    let Some((data, obj)) = load("hello.a64.O2") else {
        return;
    };
    let dir = scratch("parts");
    let s =
        Session::new(obj, Options::default()).with_cache(Cache::at(&dir), ContentHash::of(&data));
    let _ = s.functions();
    assert_eq!(
        entries(&dir).len(),
        1,
        "a run that asked only for functions wrote more than the functions"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn different_options_do_not_share_an_entry() {
    if common::corpus().is_none() {
        return;
    }
    let dir = scratch("keys");
    let with_gaps = Options::default();
    let without = Options {
        scan_gaps: false,
        ..Options::default()
    };
    let a = cached(&dir, "hello.go.stripped", &with_gaps);
    let b = cached(&dir, "hello.go.stripped", &without);

    // The two runs must agree with what they would have computed alone, which
    // is the property "no partial reuse" protects.
    let (_, obj) = load("hello.go.stripped").expect("fixture");
    assert_eq!(fingerprint(&analyze(obj, &with_gaps)), fingerprint(&a));
    let (_, obj) = load("hello.go.stripped").expect("fixture");
    assert_eq!(fingerprint(&analyze(obj, &without)), fingerprint(&b));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_different_binary_does_not_share_an_entry() {
    if common::corpus().is_none() {
        return;
    }
    let dir = scratch("content");
    let opts = Options::default();
    let a = cached(&dir, "hello.a64.O2", &opts);
    let b = cached(&dir, "hello.a64.O0", &opts);
    assert_ne!(fingerprint(&a), fingerprint(&b));
    let (_, obj) = load("hello.a64.O0").expect("fixture");
    assert_eq!(fingerprint(&analyze(obj, &opts)), fingerprint(&b));
    let _ = std::fs::remove_dir_all(&dir);
}

/// A cached answer has to be the answer, at any thread count: the cache is
/// exactly the kind of thing that can break gate G5 by handing one run a
/// result another run computed differently.
#[test]
fn a_hit_matches_a_fresh_run_at_every_thread_count() {
    if common::corpus().is_none() {
        return;
    }
    let dir = scratch("threads");
    let written = Options {
        threads: Some(1),
        ..Options::default()
    };
    let expected = fingerprint(&cached(&dir, "hello.go.stripped", &written));
    for threads in [1, 4, 10] {
        let read = Options {
            threads: Some(threads),
            ..Options::default()
        };
        assert_eq!(
            expected,
            fingerprint(&cached(&dir, "hello.go.stripped", &read)),
            "a cache written at one thread read differently at {threads}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Truncation and single-byte corruption at hundreds of offsets in every cache
/// file, each one checked to produce the right answer anyway.
///
/// This is the test the format exists for. A decoder that indexes a slice
/// panics here; one that trusts a length allocates until it is killed; one
/// without a checksum returns a plausible wrong answer, which is the worst of
/// the three and the only one a person would not notice.
#[test]
fn damaged_cache_files_are_a_miss_and_never_a_wrong_answer() {
    if common::corpus().is_none() {
        return;
    }
    let dir = scratch("damage");
    let opts = Options::default();
    let good = fingerprint(&cached(&dir, "hello.a64.O2", &opts));

    let files = entries(&dir);
    assert_eq!(files.len(), 3);
    let originals: Vec<(std::path::PathBuf, Vec<u8>)> = files
        .iter()
        .map(|p| (p.clone(), std::fs::read(p).expect("read entry")))
        .collect();

    let mut checked = 0usize;
    for (path, original) in &originals {
        // Every offset in the header and then a stride through the payload, so
        // the sweep covers the fields that decide what the file is as well as
        // the body it describes.
        let offsets: Vec<usize> = (0..original.len().min(48))
            .chain((48..original.len()).step_by(7))
            .collect();
        for off in offsets {
            // Truncated: the file stops in the middle of something.
            std::fs::write(path, &original[..off]).expect("truncate");
            restore_others(&originals, path);
            let got = fingerprint(&cached(&dir, "hello.a64.O2", &opts));
            assert_eq!(got, good, "truncating {path:?} at {off} changed the answer");

            // Corrupted: one byte is not what was written.
            let mut bad = original.clone();
            bad[off] ^= 0xff;
            std::fs::write(path, &bad).expect("corrupt");
            restore_others(&originals, path);
            let got = fingerprint(&cached(&dir, "hello.a64.O2", &opts));
            assert_eq!(
                got, good,
                "flipping byte {off} of {path:?} changed the answer"
            );
            checked += 2;
        }
        std::fs::write(path, original).expect("restore");
    }
    assert!(checked > 300, "only {checked} damaged files were tried");

    // A file of pure noise, and an empty one, are the degenerate cases.
    for (path, original) in &originals {
        std::fs::write(path, []).expect("empty");
        assert_eq!(fingerprint(&cached(&dir, "hello.a64.O2", &opts)), good);
        let noise: Vec<u8> = (0..original.len()).map(|i| (i * 31 + 7) as u8).collect();
        std::fs::write(path, &noise).expect("noise");
        assert_eq!(fingerprint(&cached(&dir, "hello.a64.O2", &opts)), good);
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Put back every entry except the one under test, because a run that found
/// damage rewrites the file it could not read.
fn restore_others(originals: &[(std::path::PathBuf, Vec<u8>)], skip: &Path) {
    for (path, bytes) in originals {
        if path != skip {
            let _ = std::fs::write(path, bytes);
        }
    }
}

#[test]
fn damage_is_reported_rather_than_swallowed() {
    let Some((data, obj)) = load("hello.a64.O2") else {
        return;
    };
    let dir = scratch("warn");
    let s =
        Session::new(obj, Options::default()).with_cache(Cache::at(&dir), ContentHash::of(&data));
    let _ = s.functions();
    let file = entries(&dir).into_iter().next().expect("an entry");
    let mut bytes = std::fs::read(&file).expect("read");
    let n = bytes.len();
    bytes[n - 1] ^= 0x01;
    std::fs::write(&file, &bytes).expect("corrupt");

    let (_, obj) = load("hello.a64.O2").expect("fixture");
    let s =
        Session::new(obj, Options::default()).with_cache(Cache::at(&dir), ContentHash::of(&data));
    let _ = s.functions();
    let warnings = s.warnings();
    assert!(
        warnings.iter().any(|w| w.contains("damaged cache file")),
        "a damaged file was ignored silently: {warnings:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_cache_directory_that_cannot_be_written_is_not_an_error() {
    let Some((data, obj)) = load("hello.a64.O2") else {
        return;
    };
    // A file where the directory should be: creating it fails, and analysis
    // has to carry on regardless. A cache is an optimization, never a
    // precondition.
    let blocker = scratch("unwritable");
    std::fs::write(&blocker, b"not a directory").expect("write blocker");
    let s = Session::new(obj, Options::default())
        .with_cache(Cache::at(blocker.join("inside")), ContentHash::of(&data));
    assert!(!s.functions().is_empty());
    assert!(
        s.warnings().iter().any(|w| w.contains("could not write")),
        "a cache that could not be written said nothing"
    );
    let _ = std::fs::remove_file(&blocker);
}

#[test]
fn the_cache_directory_follows_xdg() {
    // Not run in parallel with anything that reads the environment: these two
    // variables are process-wide, which is why this is one test and not two.
    let dir = Cache::discover().map(|c| c.dir().to_path_buf());
    if let Some(dir) = dir {
        let expected = match std::env::var_os("XDG_CACHE_HOME") {
            Some(v) if !v.is_empty() => std::path::PathBuf::from(v),
            _ => std::path::PathBuf::from(std::env::var_os("HOME").expect("HOME")).join(".cache"),
        };
        assert_eq!(dir, expected.join("r12e").join("analysis"));
    }
}
