//! Patch sets against random images and against real binaries.
//!
//! The claim a patch set makes is that it either lands whole or does nothing,
//! and that what it did can be undone byte for byte. Neither is provable from
//! a handful of examples, so the round trip is checked over a few hundred
//! generated patch sets, with a deterministic generator so a failure is
//! reproducible from its seed.

use std::path::{Path, PathBuf};

use r12e_core::Addr;
use r12e_db::anchor::{Anchor, AnchorIndex, Resolution};
use r12e_db::patch::{Conflict, Edit, Patch};

/// A small deterministic generator, so a failure is reproducible from its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*, chosen for being four lines and reproducible.
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }

    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

/// The address the generated images are loaded at.
const BASE: Addr = Addr(0x40_0000);

/// A patch set of non-overlapping edits captured from `image`.
fn generate(rng: &mut Rng, image: &[u8]) -> Patch {
    let mut patch = Patch::new("generated");
    let mut at = 0usize;
    loop {
        at += 1 + rng.below(16);
        let len = 1 + rng.below(8);
        if at + len > image.len() {
            return patch;
        }
        let addr = BASE.wrapping_offset(at as i64);
        // Half anchored by content, half by address alone: both have to work
        // when no index is supplied.
        let target = if rng.next() & 1 == 0 {
            Anchor {
                shape: rng.next(),
                bytes: rng.next(),
                insns: 4,
                abs: addr,
                offset: 0,
            }
        } else {
            Anchor {
                shape: 0,
                bytes: 0,
                insns: 0,
                abs: addr,
                offset: 0,
            }
        };
        patch
            .record(target, image, BASE, rng.bytes(len))
            .expect("the edit is inside the image");
        at += len;
    }
}

#[test]
fn applying_then_reverting_restores_every_byte() {
    let mut rng = Rng(0x1234_5678_9abc_def0);
    for _ in 0..300 {
        let len = 64 + rng.below(960);
        let original = rng.bytes(len);
        let patch = generate(&mut rng, &original);
        let mut image = original.clone();
        let applied = patch.apply(&mut image, BASE, None).expect("it applies");
        assert_eq!(applied.changes.len(), patch.len());
        assert_eq!(
            applied.bytes,
            patch.edits().iter().map(|e| e.expect.len()).sum::<usize>()
        );
        // Every edit is on the image, and the preview said so in advance.
        for c in &applied.changes {
            let off = (c.addr.get() - BASE.get()) as usize;
            assert_eq!(&image[off..off + c.after.len()], &c.after[..]);
            assert_eq!(&original[off..off + c.before.len()], &c.before[..]);
        }
        patch
            .revert()
            .apply(&mut image, BASE, None)
            .expect("the inverse applies");
        assert_eq!(image, original);
    }
}

#[test]
fn a_patch_made_against_other_bytes_writes_nothing() {
    let mut rng = Rng(0xfeed_face_dead_beef);
    let mut checked = 0;
    for _ in 0..300 {
        let len = 64 + rng.below(960);
        let original = rng.bytes(len);
        let patch = generate(&mut rng, &original);
        if patch.is_empty() {
            continue;
        }
        // Corrupt one byte an edit covers, the way a rebuilt binary would.
        let victim = &patch.edits()[rng.below(patch.len())];
        let off = (victim.addr().get() - BASE.get()) as usize + rng.below(victim.expect.len());
        let mut image = original.clone();
        image[off] ^= 0xff;
        let corrupt = image.clone();

        let e = patch
            .apply(&mut image, BASE, None)
            .expect_err("the expected bytes are gone");
        assert!(matches!(e, Conflict::Mismatch { .. }), "{e}");
        assert_eq!(image, corrupt, "a failed apply wrote something");
        checked += 1;
    }
    assert!(checked > 200, "only {checked} sets had an edit to corrupt");
}

#[test]
fn the_text_form_round_trips_over_generated_sets() {
    let mut rng = Rng(0x0bad_c0de_0bad_c0de);
    for _ in 0..300 {
        let len = 64 + rng.below(256);
        let image = rng.bytes(len);
        let mut patch = generate(&mut rng, &image);
        patch.binary = Some(format!("fnv:{:016x}", rng.next()));
        let text = patch.to_text();
        let back = Patch::from_text(&text).expect("it parses");
        assert_eq!(back.edits(), patch.edits());
        assert_eq!(back.binary, patch.binary);
        assert_eq!(back.to_text(), text);
    }
}

/// A four-instruction function whose third word is a branch, so a relink
/// changes the bytes without changing the shape.
fn function(base: u64, displacement: u32) -> (Anchor, Vec<u8>) {
    let words = [
        0xd280_0020u32,             // mov x0, #1
        0xf100_041f,                // cmp x0, #1
        0x9400_0000 | displacement, // bl <somewhere>
        0xd65f_03c0,                // ret
    ];
    let body: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let insns: Vec<r12e_arch::Insn> = words
        .iter()
        .enumerate()
        .filter_map(|(n, w)| r12e_arch::aarch64::decode_word(*w, Addr(base + n as u64 * 4)))
        .collect();
    assert_eq!(insns.len(), 4, "the fixture words all decode");
    (Anchor::function(Addr(base), &insns, &body), body)
}

#[test]
fn an_anchored_edit_survives_a_relink() {
    // The patch was made against the function at 0x1000; the rebuilt binary
    // has it at 0x9000 with a different call displacement, so its bytes
    // fingerprint differs and only the shape can find it.
    let (before, _) = function(0x1000, 4);
    let (after, mut image) = function(0x9000, 9);
    assert_eq!(before.shape, after.shape);
    assert_ne!(before.bytes, after.bytes);

    let mut patch = Patch::new("nop the compare");
    patch.push(
        Edit::new(
            before.at_offset(4),
            0xf100_041fu32.to_le_bytes().to_vec(),
            0xd503_201fu32.to_le_bytes().to_vec(),
        )
        .unwrap()
        .by("alice")
        .noted("the length check"),
    );

    // Without an index the edit falls back to the address it was recorded at,
    // which is not in this image at all.
    let e = patch
        .apply(&mut image.clone(), Addr(0x9000), None)
        .expect_err("0x1004 is not in the relinked image");
    assert!(matches!(e, Conflict::OutOfRange { .. }), "{e}");

    let index = AnchorIndex::build([after]);
    let applied = patch
        .apply(&mut image, Addr(0x9000), Some(&index))
        .expect("the shape resolves");
    assert_eq!(applied.changes[0].addr, Addr(0x9004));
    assert_eq!(applied.changes[0].resolution, Resolution::Shape);
    assert!(applied.is_confident());
    assert_eq!(&image[4..8], &0xd503_201fu32.to_le_bytes());
}

#[test]
fn the_resolution_says_when_only_the_address_matched() {
    let (before, image) = function(0x1000, 4);
    // An index that knows nothing about this function.
    let (other, _) = function(0x5000, 0x20);
    let mut index_anchor = other;
    index_anchor.shape ^= 0xdead;
    let index = AnchorIndex::build([index_anchor]);

    let mut patch = Patch::new("p");
    patch.push(
        Edit::new(
            before.at_offset(12),
            0xd65f_03c0u32.to_le_bytes().to_vec(),
            0xd503_201fu32.to_le_bytes().to_vec(),
        )
        .unwrap(),
    );
    let changes = patch
        .preview(&image, Addr(0x1000), Some(&index))
        .expect("it still lands, on the address alone");
    assert_eq!(changes[0].resolution, Resolution::Address);
    assert!(!changes[0].resolution.is_confident());
}

/// A real binary, or `None` when the fixtures have not been built.
fn fixture() -> Option<(PathBuf, Vec<u8>)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .ok()?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();
    files.sort();
    let path = files
        .into_iter()
        .find(|p| std::fs::read(p).is_ok_and(|d| d.starts_with(b"\x7fELF") && d.len() > 0x400))?;
    let data = std::fs::read(&path).ok()?;
    Some((path, data))
}

#[test]
fn a_real_binary_is_patched_and_restored() {
    let Some((path, original)) = fixture() else {
        // Fixtures are built on demand; their absence is not a failure.
        return;
    };
    let mut rng = Rng(0x5eed_0000_0000_0001);
    let mut image = original.clone();
    let patch = generate(&mut rng, &original);
    assert!(!patch.is_empty(), "{} produced no edits", path.display());

    let applied = patch.apply(&mut image, BASE, None).expect("it applies");
    assert!(applied.bytes > 0);
    assert_ne!(image, original);

    // The same patch against the file it has already changed is a conflict,
    // which is what stops a patch being applied twice.
    let e = patch
        .apply(&mut image.clone(), BASE, None)
        .expect_err("the expected bytes are gone");
    assert!(matches!(e, Conflict::Mismatch { .. }), "{e}");

    patch
        .revert()
        .apply(&mut image, BASE, None)
        .expect("the inverse applies");
    assert_eq!(image, original);
}
