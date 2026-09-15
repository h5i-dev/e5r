//! Archive tests, with `ar t` and `nm -s` as the oracle.
//!
//! Skipped when the corpus or the binutils are absent so a fresh checkout
//! still passes; run `scripts/build-fixtures.sh` to enable them.

use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_core::Arch;
use e5r_format::archive::{self, Flavor};
use e5r_format::{LoadOptions, load};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn read(name: &str) -> Option<Vec<u8>> {
    std::fs::read(corpus()?.join(name)).ok()
}

/// Run a binutil over a fixture, or `None` when it is not installed.
fn tool(cmd: &str, args: &[&str], name: &str) -> Option<String> {
    let p = corpus()?.join(name);
    let out = Command::new(cmd).args(args).arg(&p).output().ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

#[test]
fn members_match_ar_t() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    let Some(listing) = tool("ar", &["t"], "libshapes.a") else {
        return;
    };
    let a = archive::open(&data).expect("libshapes.a did not parse");
    assert_eq!(a.flavor, Flavor::Gnu);
    assert!(!a.thin);
    assert!(a.warnings.is_empty(), "{:?}", a.warnings);
    let want: Vec<&str> = listing
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    let got: Vec<&str> = a.objects().map(|(_, m)| m.name.as_str()).collect();
    assert_eq!(got, want);
    // The long name only fits in the `//` table, which is the point of it.
    assert!(
        want.iter().any(|n| n.len() > 16),
        "the fixture lost its long member name"
    );
}

#[test]
fn member_sizes_and_offsets_land_on_real_objects() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    let a = archive::open(&data).unwrap();
    for (i, m) in a.objects() {
        assert_eq!(m.data().len() as u64, m.size);
        // The recorded offset and size have to name the same bytes the
        // member handed out, or a caller reading the file itself would
        // disagree with a caller reading `data()`.
        let at = m.offset as usize;
        assert_eq!(&data[at..at + m.size as usize], m.data());
        let obj = a.load_member(i, &LoadOptions::default()).expect(&m.name);
        assert_eq!(obj.arch, Arch::AArch64);
        assert!(obj.section(".text").is_some(), "{} has no .text", m.name);
    }
}

#[test]
fn the_index_matches_nm_s() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    let Some(listing) = tool("nm", &["-s"], "libshapes.a") else {
        return;
    };
    let a = archive::open(&data).unwrap();
    // `nm -s` prints "symbol in member" under an "Archive index:" heading.
    let mut want: Vec<(String, String)> = listing
        .lines()
        .filter_map(|l| l.split_once(" in "))
        .map(|(s, m)| (s.trim().to_string(), m.trim().to_string()))
        .collect();
    if want.is_empty() {
        return;
    }
    let mut got: Vec<(String, String)> = a
        .index
        .iter()
        .filter_map(|e| {
            e.member
                .map(|i| (e.name.clone(), a.members[i].name.clone()))
        })
        .collect();
    want.sort();
    got.sort();
    assert_eq!(got, want);
    // Every index entry resolved, so no offset pointed into open space.
    assert!(a.index.iter().all(|e| e.member.is_some()));
}

#[test]
fn a_symbol_names_the_member_that_defines_it() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    let Some(listing) = tool("nm", &["-s"], "libshapes.a") else {
        return;
    };
    let a = archive::open(&data).unwrap();
    let Some((sym, member)) = listing.lines().find_map(|l| l.split_once(" in ")) else {
        return;
    };
    let (sym, member) = (sym.trim(), member.trim());
    let definers = a.definers(sym);
    assert!(!definers.is_empty(), "{sym} is defined by nothing");
    assert!(
        definers.iter().any(|&i| a.members[i].name == member),
        "{sym} should be in {member}, found {:?}",
        definers
            .iter()
            .map(|&i| &a.members[i].name)
            .collect::<Vec<_>>()
    );
    assert!(a.symbols_of(definers[0]).contains(&sym));
}

#[test]
fn a_thin_archive_lists_members_without_their_bytes() {
    let Some(data) = read("libshapes-thin.a") else {
        return;
    };
    let Some(listing) = tool("ar", &["t"], "libshapes-thin.a") else {
        return;
    };
    let a = archive::open(&data).expect("thin archive did not parse");
    assert!(a.thin);
    // `ar t` resolves a thin member against the archive's directory, so the
    // basename is the part both sides agree on.
    let want: Vec<&str> = listing
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| l.rsplit('/').next().unwrap())
        .collect();
    let got: Vec<&str> = a
        .objects()
        .map(|(_, m)| m.name.rsplit('/').next().unwrap())
        .collect();
    assert_eq!(got, want);
    // The bytes are elsewhere, and saying so is better than handing back the
    // wrong ones.
    let external = a.members.iter().position(|m| m.thin).unwrap();
    assert!(a.load_member(external, &LoadOptions::default()).is_err());
}

#[test]
fn load_says_it_is_an_archive() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    let e = load(&data, &LoadOptions::default()).unwrap_err();
    assert!(
        !e.is_not_recognized(),
        "an archive should not read as garbage"
    );
    let msg = e.to_string();
    assert!(msg.contains("archive"), "{msg}");
    assert!(msg.contains("member"), "{msg}");
}

#[test]
fn every_truncation_returns_an_answer() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    // A step, because a byte at a time over a megabyte is a benchmark.
    let step = (data.len() / 512).max(1);
    let mut n = 0;
    for end in (0..data.len()).step_by(step) {
        let a = archive::open(&data[..end]);
        if let Ok(a) = a {
            // Whatever survived has to be self-consistent.
            for m in &a.members {
                assert!(m.offset + m.size <= end as u64);
            }
        }
        n += 1;
    }
    assert!(n > 100, "only {n} truncations tried");
}

#[test]
fn corrupt_archives_never_panic_or_hang() {
    let Some(data) = read("libshapes.a") else {
        return;
    };
    let head = &data[..data.len().min(64 * 1024)];
    let mut state = 0x1234_5678_9abc_def1u64;
    let mut next = move || {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state.wrapping_mul(0x2545_f491_4f6c_dd1d)
    };
    let started = std::time::Instant::now();
    for _ in 0..4000 {
        let mut v = head.to_vec();
        // Saturate a run, which is how a size or a count becomes enormous.
        let at = (next() as usize) % v.len();
        let len = (next() as usize) % 16 + 1;
        for b in v.iter_mut().skip(at).take(len) {
            *b = if next() & 1 == 0 { 0xff } else { b'9' };
        }
        if let Ok(a) = archive::open(&v) {
            for i in 0..a.members.len() {
                let _ = a.load_member(i, &LoadOptions::default());
            }
        }
    }
    assert!(
        started.elapsed() < std::time::Duration::from_secs(30),
        "corrupt archives took too long"
    );
}
