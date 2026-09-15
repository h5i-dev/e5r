//! Shared by the session and cache tests: loading a fixture, and flattening a
//! result so two runs can be compared.

// Each test binary compiles its own copy of this module and uses part of it,
// so what the other one needs looks unused here.
#![allow(dead_code)]

use std::path::{Path, PathBuf};

use e5r_format::{LoadOptions, Object};

/// The built fixture directory, absent on a checkout that has not run
/// `scripts/build-fixtures.sh`.
pub fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().ok()).flatten()
}

/// A fixture's bytes and the object loaded from them.
pub fn load(name: &str) -> Option<(Vec<u8>, Object)> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some((data, obj))
}

/// Everything a run is supposed to produce, flattened to a string.
///
/// A string rather than a derived `PartialEq` because the point is to compare
/// a cached answer against a computed one field by field, and a mismatch has
/// to be readable: `assert_eq!` on two of these names the line that differs.
pub fn fingerprint(p: &e5r_analysis::Program) -> String {
    let mut s = String::new();
    for f in p.functions.values() {
        s.push_str(&format!(
            "{:x} {:?} {} {} {} {:?} {} {}\n",
            f.entry.get(),
            f.name,
            f.range.start().get(),
            f.range.end().get(),
            f.provenance,
            f.cfg.halt,
            f.cfg.has_indirect,
            f.cfg.insns()
        ));
        for b in f.cfg.blocks.values() {
            s.push_str(&format!(
                "  b {:x}-{:x} {} {} {:?} {:?}\n",
                b.range.start().get(),
                b.range.end().get(),
                b.insns,
                b.unresolved,
                b.terminator,
                b.successors.iter().map(|a| a.get()).collect::<Vec<_>>()
            ));
        }
        for t in &f.cfg.tables {
            s.push_str(&format!("  t {t:?}\n"));
        }
        for c in &f.cfg.calls {
            s.push_str(&format!("  c {:x}\n", c.get()));
        }
    }
    for x in p.xrefs.all() {
        s.push_str(&format!(
            "x {:x} {:x} {:?}\n",
            x.from.get(),
            x.to.get(),
            x.kind
        ));
    }
    for f in &p.strings {
        s.push_str(&format!(
            "s {:x} {} {:?} {}\n",
            f.addr.get(),
            f.len,
            f.encoding,
            f.text
        ));
    }
    for a in &p.noreturn {
        s.push_str(&format!("n {:x}\n", a.get()));
    }
    s.push_str(&format!("rounds {}\n", p.rounds));
    s
}

/// A directory of our own under the system temporary directory, removed by the
/// caller. Named for the test so a leftover says which one left it.
pub fn scratch(tag: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.subsec_nanos())
        .unwrap_or(0);
    let d = std::env::temp_dir().join(format!(
        "e5r-cache-test-{tag}-{}-{nanos}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&d);
    d
}
