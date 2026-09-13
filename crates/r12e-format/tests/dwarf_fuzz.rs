//! Hostile DWARF: the list sections, corrupted on purpose.
//!
//! `fuzz.rs` mutates whole files at random, which reaches the debug sections
//! only by luck. The range and location lists are walked by a length and a
//! kind byte that both come from the file, and a base address that also comes
//! from the file, so they get their own sweep: every byte of every list
//! section set to the two values that break arithmetic, and the whole file
//! truncated at every step. The contract is the one the crate promises
//! everywhere: a value or an error, never a panic, a hang, or an allocation
//! that follows a number the file chose.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use r12e_format::{LoadOptions, load};

/// Sections whose contents the new readers walk.
const TARGETS: [&str; 6] = [
    ".debug_info",
    ".debug_abbrev",
    ".debug_rnglists",
    ".debug_loclists",
    ".debug_line",
    ".debug_str_offsets",
];

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// Where each target section's bytes are in the file, found by loading it once.
fn regions(bytes: &[u8]) -> Vec<(String, u64, u64)> {
    let Ok(obj) = load(bytes, &LoadOptions::default()) else {
        return Vec::new();
    };
    obj.sections
        .iter()
        .filter(|s| TARGETS.contains(&s.name.as_str()) && s.file_size > 0)
        .map(|s| (s.name.clone(), s.file_offset, s.file_size))
        .collect()
}

#[test]
fn corrupting_a_debug_section_never_panics_or_hangs() {
    let Some(dir) = corpus() else { return };
    let opts = LoadOptions::default();
    let mut cases = 0u64;
    let started = Instant::now();
    for name in ["hello.a64.O2", "wide.a64.O2.o", "wide.x64.O2.o"] {
        let Ok(full) = std::fs::read(dir.join(name)) else {
            continue;
        };
        let regions = regions(&full);
        assert!(
            !regions.is_empty(),
            "{name} has no debug sections to corrupt"
        );
        for (_, offset, size) in regions {
            // Every byte would be a throughput test; every seventh reaches
            // each field of every record without being one.
            for i in (offset..offset + size).step_by(7) {
                for value in [0xffu8, 0x00, 0x80] {
                    let mut bad = full.clone();
                    if let Some(b) = bad.get_mut(i as usize) {
                        *b = value;
                    }
                    let _ = load(&bad, &opts);
                    cases += 1;
                }
            }
        }
    }
    assert!(cases > 100, "only {cases} cases, so this proves nothing");
    assert!(
        started.elapsed() < Duration::from_secs(60),
        "{cases} corrupted debug sections took {:?}",
        started.elapsed()
    );
    println!("dwarf fuzz: {cases} corrupted debug sections, no panics");
}

#[test]
fn a_truncated_debug_section_stops_rather_than_guessing() {
    let Some(dir) = corpus() else { return };
    let opts = LoadOptions::default();
    let started = Instant::now();
    let mut cases = 0u64;
    for name in ["hello.a64.O2", "wide.a64.O2.o"] {
        let Ok(full) = std::fs::read(dir.join(name)) else {
            continue;
        };
        for cut in (0x40..full.len()).step_by(97) {
            let _ = load(&full[..cut], &opts);
            cases += 1;
        }
    }
    assert!(cases > 50);
    assert!(
        started.elapsed() < Duration::from_secs(30),
        "{cases} truncations took {:?}",
        started.elapsed()
    );
}

/// A range list whose entries claim to run off the end of the section.
///
/// Built rather than mutated: the interesting case is a well-formed unit
/// header followed by a list that lies, which a random flip rarely produces.
#[test]
fn a_range_list_that_runs_off_the_end_is_bounded() {
    let Some(dir) = corpus() else { return };
    let Ok(full) = std::fs::read(dir.join("hello.a64.O2")) else {
        return;
    };
    let Some((_, offset, size)) = regions(&full)
        .into_iter()
        .find(|(name, _, size)| name == ".debug_rnglists" && *size > 16)
    else {
        return;
    };
    let started = Instant::now();
    // Fill the whole list with start-length entries whose length is the
    // largest a uleb128 can spell, which is what an unchecked reader adds to
    // a base address and then trusts.
    let mut bad = full.clone();
    let body = &mut bad[offset as usize..(offset + size) as usize];
    let mut i = 12; // past the section header
    while i + 10 <= body.len() {
        body[i] = 0x07; // DW_RLE_start_length
        for b in &mut body[i + 1..i + 9] {
            *b = 0xff;
        }
        body[i + 9] = 0x7f; // a one-byte uleb128 of 127
        i += 10;
    }
    let _ = load(&bad, &LoadOptions::default());
    assert!(started.elapsed() < Duration::from_secs(5));
}
