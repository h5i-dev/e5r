//! Overlay, entropy and packer-evidence tests.
//!
//! The one that matters most is the false-positive check: an ordinary compiled
//! binary must produce no finding an analyst would act on. A detector that
//! fires on everything is the same as no detector.
//!
//! Skipped when the corpus is absent; run `scripts/build-fixtures.sh`.

use std::path::{Path, PathBuf};

use r12e_core::Strength;
use r12e_format::overlay::{self, Content, Kind};
use r12e_format::{LoadOptions, Object, load};

/// Fixtures that are whole images rather than relocatable objects, one per
/// container the overlay walk knows how to measure.
const IMAGES: &[&str] = &[
    "hello.a64.O0",
    "hello.a64.O2",
    "hello.a64.O0.stripped",
    "driver.x64.O2",
    "driver.a64.O2",
    "hello.go",
    "panicky",
];

/// Relocatable objects, whose symbol, string and relocation tables sit past
/// the last section and are the easiest way to invent an overlay that is not
/// there.
const OBJECTS: &[&str] = &[
    "shapes.a64.O0.o",
    "shapes.x64.O2.o",
    "shapes.coff.o",
    "wide.coff.o",
    "shapes.macho.a64.o",
    "shapes.macho.x64.o",
    "greeter.macho.a64.o",
];

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<(Object, Vec<u8>)> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = load(&data, &LoadOptions::default()).ok()?;
    Some((obj, data))
}

/// A deterministic byte stream, so a failure reproduces.
fn pseudorandom(n: usize) -> Vec<u8> {
    let mut s = 0x243f_6a88_85a3_08d3u64;
    (0..n)
        .map(|_| {
            s ^= s >> 12;
            s ^= s << 25;
            s ^= s >> 27;
            (s.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 33) as u8
        })
        .collect()
}

#[test]
fn a_clean_binary_has_no_overlay() {
    let mut checked = 0;
    for name in IMAGES.iter().chain(OBJECTS) {
        let Some((obj, data)) = open(name) else {
            continue;
        };
        let r = overlay::analyze(&obj, &data);
        assert!(
            r.overlay.is_none(),
            "{name}: {} bytes of overlay at {:#x}, but nothing was appended",
            r.overlay.as_ref().map(|o| o.size).unwrap_or(0),
            r.described_end
        );
        checked += 1;
    }
    assert!(checked > 0, "no images in the corpus");
}

#[test]
fn appended_bytes_are_found_at_the_right_offset() {
    let Some((_, data)) = open("hello.a64.O0") else {
        return;
    };
    let tail = pseudorandom(9000);
    let mut grown = data.clone();
    grown.extend_from_slice(&tail);
    let obj = load(&grown, &LoadOptions::default()).unwrap();
    let r = overlay::analyze(&obj, &grown);
    let o = r.overlay.expect("appended bytes were not reported");
    assert_eq!(o.offset, data.len() as u64);
    assert_eq!(o.size, tail.len() as u64);
    assert!(o.entropy > 7.5, "{}", o.entropy);
    assert_eq!(o.content, Content::HighEntropy);
    assert!(r.findings.iter().any(|f| f.kind == Kind::OverlayPresent));
}

#[test]
fn an_appended_container_is_named() {
    let Some((_, data)) = open("hello.a64.O0") else {
        return;
    };
    for (magic, want) in [
        (b"PK\x03\x04".as_slice(), Content::Zip),
        (b"MSCF".as_slice(), Content::Cabinet),
        (b"\x7fELF".as_slice(), Content::Elf),
    ] {
        let mut grown = data.clone();
        grown.extend_from_slice(magic);
        grown.extend_from_slice(&pseudorandom(4096));
        let obj = load(&grown, &LoadOptions::default()).unwrap();
        let o = overlay::analyze(&obj, &grown).overlay.expect("no overlay");
        assert_eq!(o.content, want);
        assert_eq!(o.offset, data.len() as u64);
    }
}

#[test]
fn a_run_of_zeros_scores_nothing_and_random_bytes_score_eight() {
    let Some((_, data)) = open("hello.a64.O0") else {
        return;
    };
    let mut zeros = data.clone();
    zeros.extend_from_slice(&[0u8; 16384]);
    let obj = load(&zeros, &LoadOptions::default()).unwrap();
    let o = overlay::analyze(&obj, &zeros).overlay.unwrap();
    assert!(o.entropy < 0.01, "zeros scored {}", o.entropy);

    let mut noise = data.clone();
    noise.extend_from_slice(&pseudorandom(1 << 18));
    let obj = load(&noise, &LoadOptions::default()).unwrap();
    let o = overlay::analyze(&obj, &noise).overlay.unwrap();
    assert!(o.entropy > 7.9, "noise scored {}", o.entropy);
}

#[test]
fn the_entropy_map_localizes_a_packed_window() {
    let Some((obj, data)) = open("hello.a64.O0") else {
        return;
    };
    let Some(text) = obj.section(".text") else {
        return;
    };
    // Replace one four-kilobyte window of .text with noise. The section
    // average moves a little; the window it happened in moves to the top.
    if text.file_size < 3 * overlay::WINDOW {
        return;
    }
    let at = (text.file_offset + overlay::WINDOW) as usize;
    let mut packed = data.clone();
    packed[at..at + overlay::WINDOW as usize]
        .copy_from_slice(&pseudorandom(overlay::WINDOW as usize));
    let obj = load(&packed, &LoadOptions::default()).unwrap();
    let r = overlay::analyze(&obj, &packed);
    let se = r
        .sections
        .iter()
        .find(|s| s.name == ".text")
        .expect("no .text in the map");
    let peak = se.peak().expect("no windows measured");
    assert_eq!(peak.offset, at as u64, "the noisy window was not the peak");
    assert!(peak.entropy > 7.5, "{}", peak.entropy);
    assert!(
        peak.entropy > se.entropy,
        "a window should stand out from its section average"
    );
}

#[test]
fn section_entropy_covers_every_section_and_clips_to_the_file() {
    let Some((obj, data)) = open("hello.a64.O0") else {
        return;
    };
    let r = overlay::analyze(&obj, &data);
    assert_eq!(r.sections.len(), obj.sections.len());
    for s in &r.sections {
        assert!(s.file_offset + s.size <= data.len() as u64);
        assert!((0.0..=8.0).contains(&s.entropy));
        let measured: u64 = s.windows.iter().map(|w| w.size).sum();
        assert!(measured == s.size || s.windows.is_empty());
    }
    assert!(r.warnings.is_empty(), "{:?}", r.warnings);
}

#[test]
fn a_normal_binary_produces_no_strong_evidence() {
    let mut checked = 0;
    for name in IMAGES.iter().chain(OBJECTS) {
        let Some((obj, data)) = open(name) else {
            continue;
        };
        let r = overlay::analyze(&obj, &data);
        let strong: Vec<String> = r
            .at_least(Strength::Inferred)
            .map(|f| format!("{}: {}", f.kind, f.detail))
            .collect();
        assert!(strong.is_empty(), "{name} produced {strong:#?}");
        checked += 1;
    }
    assert!(checked > 0, "no images in the corpus");
}

#[test]
fn a_packer_name_is_only_claimed_when_it_is_a_signature() {
    let Some((mut obj, data)) = open("hello.a64.O0") else {
        return;
    };
    // Rename a section to a signature the module knows, which is the only
    // case where naming a product is a fact rather than a guess.
    obj.sections[1].name = "UPX1".into();
    let f = overlay::evidence(&obj, &data, &[], None);
    let named: Vec<&overlay::Finding> = f
        .iter()
        .filter(|f| f.kind == Kind::PackerSectionName)
        .collect();
    assert_eq!(named.len(), 1);
    assert!(named[0].detail.contains("UPX"));
    // And nothing anywhere says the file is packed.
    assert!(
        !f.iter()
            .any(|f| f.detail.to_lowercase().contains("is packed")),
        "a verdict leaked into the evidence"
    );
}

#[test]
fn evidence_is_ordered_strongest_first_and_is_deterministic() {
    let Some((obj, data)) = open("hello.a64.O0") else {
        return;
    };
    let (map, _) = overlay::section_entropy(&obj, &data);
    let a = overlay::evidence(&obj, &data, &map, None);
    let b = overlay::evidence(&obj, &data, &map, None);
    assert_eq!(a, b);
    assert!(a.windows(2).all(|w| w[0].strength >= w[1].strength));
}

#[test]
fn analysis_of_hostile_bytes_returns() {
    let Some((obj, data)) = open("hello.a64.O0") else {
        return;
    };
    // A section table that claims the world, over bytes that are not there.
    let mut hostile = obj.clone();
    for s in &mut hostile.sections {
        s.file_offset = u64::MAX - 1024;
        s.file_size = u64::MAX / 2;
    }
    let started = std::time::Instant::now();
    let r = overlay::analyze(&hostile, &data);
    assert!(r.sections.iter().all(|s| s.size == 0));
    assert!(
        r.findings
            .iter()
            .any(|f| f.kind == Kind::SectionOutsideFile)
    );
    assert!(started.elapsed() < std::time::Duration::from_secs(2));
}
