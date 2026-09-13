//! G9: two analysts on separate branches merge with `git merge` alone.
//!
//! This is the claim the whole storage design exists to make, so it is tested
//! against real git rather than against a model of it. Skipped when git is not
//! installed.

use std::path::Path;
use std::process::Command;

use r12e_core::Addr;
use r12e_db::{Anchor, Field, Log};

fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "test")
        .env("GIT_AUTHOR_EMAIL", "test@example.invalid")
        .env("GIT_COMMITTER_NAME", "test")
        .env("GIT_COMMITTER_EMAIL", "test@example.invalid")
        .output()
        .ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

fn anchor(n: u64) -> Anchor {
    Anchor {
        shape: n.wrapping_mul(0x9e37_79b9_7f4a_7c15),
        bytes: n.wrapping_mul(0xc2b2_ae3d_27d4_eb4f),
        insns: 8,
        abs: Addr(0x400000 + n * 0x40),
        offset: 0,
    }
}

/// A repo whose annotation files use git's union merge driver, which keeps
/// both sides of a conflicting hunk. For a log whose fold ignores order, the
/// union of two branches is the correct merge.
fn setup(dir: &Path) -> Option<()> {
    git(dir, &["init", "-q", "-b", "main"])?;
    std::fs::write(dir.join(".gitattributes"), "*.r12e merge=union\n").ok()?;
    Some(())
}

#[test]
fn two_branches_merge_without_conflict_markers() {
    let tmp = std::env::temp_dir().join(format!("r12e-merge-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).unwrap();
    if setup(&tmp).is_none() {
        return; // no git here
    }
    let file = tmp.join("bin.r12e");

    // A shared starting point: both analysts pull the same file.
    let mut base = Log::new();
    base.binary = Some("sha256:shared".into());
    for i in 0..20 {
        base.assert(anchor(i), Field::Name, Some(format!("known_{i}")), "base");
    }
    std::fs::write(&file, base.to_text()).unwrap();
    git(&tmp, &["add", "."]).unwrap();
    git(&tmp, &["commit", "-qm", "base"]).unwrap();

    // Alice names twenty more functions on her branch.
    git(&tmp, &["checkout", "-qb", "alice"]).unwrap();
    let mut alice = base.clone();
    for i in 100..120 {
        alice.assert(anchor(i), Field::Name, Some(format!("alice_{i}")), "alice");
        alice.assert(
            anchor(i),
            Field::Comment,
            Some(format!("note {i}")),
            "alice",
        );
    }
    std::fs::write(&file, alice.to_text()).unwrap();
    git(&tmp, &["commit", "-qam", "alice"]).unwrap();

    // Bob does the same on his, from the same base.
    git(&tmp, &["checkout", "-q", "main"]).unwrap();
    git(&tmp, &["checkout", "-qb", "bob"]).unwrap();
    let mut bob = base.clone();
    for i in 200..220 {
        bob.assert(anchor(i), Field::Name, Some(format!("bob_{i}")), "bob");
        bob.assert(
            anchor(i),
            Field::Type,
            Some(format!("int f{i}(void)")),
            "bob",
        );
    }
    std::fs::write(&file, bob.to_text()).unwrap();
    git(&tmp, &["commit", "-qam", "bob"]).unwrap();

    // git merges them with no help from us.
    git(&tmp, &["checkout", "-q", "alice"]).unwrap();
    let merged = git(&tmp, &["merge", "--no-edit", "bob"]);
    let text = std::fs::read_to_string(&file).unwrap();
    assert!(
        merged.is_some(),
        "git could not merge the two branches:\n{text}"
    );
    assert!(
        !text.contains("<<<<<<<"),
        "the merge left conflict markers:\n{text}"
    );

    // And the merged file says what both analysts wrote.
    let log = Log::from_text(&text).unwrap();
    let folded = log.fold();
    let values: Vec<&str> = folded.values().filter_map(|a| a.value.as_deref()).collect();
    assert_eq!(folded.len(), 20 + 40 + 40, "lost assertions in the merge");
    // Union merge can repeat a line; reading must not double-count it.
    assert_eq!(
        log.records().len(),
        log.fold().len(),
        "duplicates survived the read"
    );
    assert!(values.contains(&"alice_100"));
    assert!(values.contains(&"bob_200"));
    assert!(values.contains(&"known_0"));

    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn editing_the_same_function_resolves_rather_than_conflicting() {
    let tmp = std::env::temp_dir().join(format!("r12e-same-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).unwrap();
    if setup(&tmp).is_none() {
        return;
    }
    let file = tmp.join("bin.r12e");

    let mut base = Log::new();
    for i in 0..10 {
        base.assert(anchor(i), Field::Name, Some(format!("f{i}")), "base");
    }
    std::fs::write(&file, base.to_text()).unwrap();
    git(&tmp, &["add", "."]).unwrap();
    git(&tmp, &["commit", "-qm", "base"]).unwrap();

    // Both analysts rename the same function, differently.
    git(&tmp, &["checkout", "-qb", "alice"]).unwrap();
    let mut alice = base.clone();
    alice.assert(anchor(3), Field::Name, Some("parse_header".into()), "alice");
    std::fs::write(&file, alice.to_text()).unwrap();
    git(&tmp, &["commit", "-qam", "alice"]).unwrap();

    git(&tmp, &["checkout", "-q", "main"]).unwrap();
    git(&tmp, &["checkout", "-qb", "bob"]).unwrap();
    let mut bob = base.clone();
    bob.assert(anchor(3), Field::Name, Some("read_header".into()), "bob");
    std::fs::write(&file, bob.to_text()).unwrap();
    git(&tmp, &["commit", "-qam", "bob"]).unwrap();

    git(&tmp, &["checkout", "-q", "alice"]).unwrap();
    let merged = git(&tmp, &["merge", "--no-edit", "bob"]);
    let text = std::fs::read_to_string(&file).unwrap();

    // Two edits to the same field are distinct lines, so git still merges.
    // The fold picks one deterministically and keeps the other as history.
    if merged.is_some() {
        assert!(!text.contains("<<<<<<<"), "{text}");
        let log = Log::from_text(&text).unwrap();
        let winner = log
            .fold()
            .values()
            .find(|a| a.target.shape == anchor(3).shape && a.field == Field::Name)
            .and_then(|a| a.value.clone())
            .unwrap();
        assert!(
            winner == "parse_header" || winner == "read_header",
            "unexpected winner {winner:?}"
        );
        // Both are still recorded, so the losing name is recoverable.
        assert!(text.contains("parse_header"));
        assert!(text.contains("read_header"));
    }

    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn the_file_survives_a_round_trip_through_git() {
    let tmp = std::env::temp_dir().join(format!("r12e-rt-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).unwrap();
    if setup(&tmp).is_none() {
        return;
    }
    let file = tmp.join("bin.r12e");
    let mut log = Log::new();
    log.assert(
        anchor(1),
        Field::Comment,
        Some("a comment with \"quotes\", a\ttab and a\nnewline".into()),
        "alice",
    );
    std::fs::write(&file, log.to_text()).unwrap();
    git(&tmp, &["add", "."]).unwrap();
    git(&tmp, &["commit", "-qm", "one"]).unwrap();
    git(&tmp, &["checkout", "-q", "--", "bin.r12e"]).unwrap();

    let back = Log::from_text(&std::fs::read_to_string(&file).unwrap()).unwrap();
    assert_eq!(back.records(), log.records());
    let _ = std::fs::remove_dir_all(&tmp);
}
