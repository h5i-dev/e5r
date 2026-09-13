//! Project files: the verdict on a binary, and a parser that never panics.
//!
//! A project file is the one file a session starts from, so it is also the one
//! most likely to be hand-edited, truncated by a full disk, or merged badly. A
//! reader that panics on any of that takes the session with it, so the parser
//! is checked against mutated and truncated copies of a good file rather than
//! against a good file alone.

use std::path::{Path, PathBuf};

use r12e_core::{Addr, Arch};
use r12e_db::patch::Patch;
use r12e_db::project::{Project, Verdict, digest};

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
}

fn session(path: &str, data: &[u8]) -> Project {
    let mut p = Project::for_binary(path, data);
    p.load.base = Some(Addr(0x40_0000));
    p.load.arch = Some(Arch::AArch64);
    p.load.readers.insert("eh_frame".into());
    p.load.readers.insert("dwarf".into());
    p.load.readers.insert("go".into());
    p.analysis.insert("sweep".into(), "recursive".into());
    p.analysis.insert("jump-tables".into(), "on".into());
    p.log = Some("notes.r12e".into());
    p.signatures = vec!["libc.sig".into(), "openssl.sig".into()];
    p.patches = vec!["nop-check.r12e-patch".into()];
    p
}

#[test]
fn a_session_round_trips_through_the_file() {
    let p = session("/srv/bin/target", b"bytes of a binary");
    let text = p.to_text();
    let back = Project::from_text(&text).expect("it parses");
    assert_eq!(back, p);
    assert_eq!(back.to_text(), text);
    // Every reference survives, because losing one silently drops an
    // analyst's work out of the session.
    assert_eq!(back.log.as_deref(), Some("notes.r12e"));
    assert_eq!(back.signatures.len(), 2);
    assert_eq!(back.patches, ["nop-check.r12e-patch"]);
    assert_eq!(back.load.readers.len(), 3);
}

#[test]
fn the_three_verdicts_are_distinguishable() {
    let data = b"bytes of a binary".to_vec();
    let p = session("/srv/bin/target", &data);
    assert_eq!(p.verify(&data), Verdict::Same);
    assert_eq!(p.verify_at("/srv/bin/target", &data), Verdict::Same);

    let moved = p.verify_at("/home/analyst/target", &data);
    assert!(matches!(moved, Verdict::Moved { .. }), "{moved}");
    assert!(moved.is_usable());
    if let Verdict::Moved { recorded, found } = moved {
        assert_eq!(recorded, "/srv/bin/target");
        assert_eq!(found, "/home/analyst/target");
    }

    let mut rebuilt = data.clone();
    rebuilt[3] ^= 1;
    let verdict = p.verify(&rebuilt);
    assert!(matches!(verdict, Verdict::Different { .. }), "{verdict}");
    assert!(!verdict.is_usable());
    // A rebuild that happens to keep the size is still a different binary.
    assert_eq!(rebuilt.len(), data.len());
    // And so is a truncation.
    assert!(!p.verify(&data[..data.len() - 1]).is_usable());
}

#[test]
fn a_mutated_file_errors_rather_than_panicking() {
    let good = session("/srv/bin/target", b"bytes of a binary").to_text();
    let mut rng = Rng(0xc0ff_ee00_0000_0001);
    let mut parsed = 0;
    for _ in 0..600 {
        let mut bytes = good.clone().into_bytes();
        match rng.below(3) {
            // Truncate anywhere, including mid-line and mid-header.
            0 => bytes.truncate(rng.below(good.len())),
            // Flip a byte, which breaks keys, numbers and the header alike.
            1 => {
                let at = rng.below(bytes.len());
                bytes[at] ^= 1 << rng.below(7);
            }
            // Drop a line, the way a bad merge resolution does.
            _ => {
                let keep: Vec<&str> = good
                    .lines()
                    .enumerate()
                    .filter(|(n, _)| *n != rng.below(good.lines().count()))
                    .map(|(_, l)| l)
                    .collect();
                bytes = keep.join("\n").into_bytes();
            }
        }
        let text = String::from_utf8_lossy(&bytes).into_owned();
        if let Ok(p) = Project::from_text(&text) {
            // Whatever survived must still be a project that writes and reads
            // back as itself.
            assert_eq!(Project::from_text(&p.to_text()).unwrap(), p);
            parsed += 1;
        }
    }
    assert!(
        parsed > 0,
        "every mutation was rejected, so nothing was read"
    );
}

#[test]
fn a_project_without_a_binary_is_refused() {
    // The one thing it cannot do without: a project that cannot name its
    // binary cannot check it either.
    let text = "r12e-project 1\nlog = notes.r12e\n";
    let e = Project::from_text(text).unwrap_err().to_string();
    assert!(e.contains("binary"), "{e}");
}

#[test]
fn the_digest_separates_files_of_the_same_length() {
    let mut rng = Rng(0xabcd_ef01_2345_6789);
    let mut seen = std::collections::BTreeSet::new();
    for _ in 0..2000 {
        let data: Vec<u8> = (0..32).map(|_| rng.next() as u8).collect();
        seen.insert(digest(&data));
    }
    assert_eq!(
        seen.len(),
        2000,
        "the digest collided on random 32-byte files"
    );
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
        .find(|p| std::fs::read(p).is_ok_and(|d| d.starts_with(b"\x7fELF")))?;
    let data = std::fs::read(&path).ok()?;
    Some((path, data))
}

#[test]
fn a_project_for_a_real_binary_recognizes_it() {
    let Some((path, data)) = fixture() else {
        // Fixtures are built on demand; their absence is not a failure.
        return;
    };
    let name = path.to_string_lossy().into_owned();
    let mut p = Project::for_binary(&name, &data);
    assert_eq!(p.binary.size, data.len() as u64);
    assert_eq!(p.verify(&data), Verdict::Same);
    assert!(
        p.verify_at("/elsewhere/copy", &data).is_usable(),
        "a copy of the same file is still the same binary"
    );

    // A patch set the project names, applied to the file the project names:
    // the pair has to agree about the same bytes.
    let mut patch = Patch::new("first byte of the ident");
    patch.binary = Some(format!("{:016x}", p.binary.hash));
    patch
        .record(
            r12e_db::anchor::Anchor {
                shape: 0,
                bytes: 0,
                insns: 0,
                abs: Addr(0x10),
                offset: 0,
            },
            &data,
            Addr(0),
            vec![0x00, 0x00],
        )
        .expect("the edit is inside the file");
    p.patches.push("ident.r12e-patch".into());

    let mut image = data.clone();
    patch.apply(&mut image, Addr(0), None).expect("it applies");
    // The patched file is no longer the binary the project was made for, which
    // is the whole point of recording the digest.
    assert!(matches!(p.verify(&image), Verdict::Different { .. }));
    patch
        .revert()
        .apply(&mut image, Addr(0), None)
        .expect("the inverse applies");
    assert_eq!(p.verify(&image), Verdict::Same);

    let back = Project::from_text(&p.to_text()).expect("it parses");
    assert_eq!(back, p);
}
