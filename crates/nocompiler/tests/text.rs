//! Criterion 5 of docs/isa/v1.md: `asm(disasm(x)) = x` for every function at
//! L1 or above, on the committed binaries and the C corpus.
//!
//! For every such function, the object `asm` makes from the text `disasm`
//! prints holds the same relocatable function (words with the relocated
//! fields zero, and the relocations) as the binary, with the same tree, level
//! and frame partition. And where ld.lld is available, the object linked again
//! at the binary's section addresses and function order is the binary's
//! `.text` and data, byte for byte. Also: what the text format refuses.

use nocompiler::text::{assemble, print, write_object};
use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn lld() -> Option<String> {
    ["ld.lld", "ld.lld-20", "ld.lld-19", "ld.lld-18"]
        .into_iter()
        .find(|c| {
            Command::new(c)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success())
        })
        .map(String::from)
}

fn shift(ns: &[nocompiler::profile::Node], d: u64) -> Vec<(u8, u64, u64, usize)> {
    let mut out = Vec::new();
    fn go(
        ns: &[nocompiler::profile::Node],
        d: u64,
        depth: usize,
        out: &mut Vec<(u8, u64, u64, usize)>,
    ) {
        for n in ns {
            out.push((n.kind as u8, n.start - d, n.end - d, depth));
            go(&n.children, d, depth + 1, out);
        }
    }
    go(ns, d, 0, &mut out);
    out
}

/// Round-trip one binary; the number of functions checked, and whether every
/// function was at L1 (so the whole program could be relinked).
fn round_trip(name: &str, bytes: &[u8], dir: &Path) -> (usize, bool) {
    let file = name.replace('/', "_");
    let bin = nocompiler::load(bytes).unwrap();
    let text = print(&bin, None).unwrap_or_else(|e| panic!("{name}: {e}"));
    let obj = assemble(&text).unwrap_or_else(|e| panic!("{name}: {e}\n{text}"));
    let m = nocompiler::module::of_binary(&bin).unwrap();
    let reports = bin.check();
    let mut n = 0;
    let mut all = true;
    for r in &reports {
        let Ok(meta) = &r.result else {
            all = false;
            continue;
        };
        let want = m.funcs.iter().find(|f| f.name == r.name).unwrap();
        let got = obj
            .funcs
            .iter()
            .find(|a| a.func.name == r.name)
            .unwrap_or_else(|| panic!("{name}: {} not assembled", r.name));
        assert_eq!(got.func.words, want.words, "{name} {}: words", r.name);
        assert_eq!(
            got.func.relocs, want.relocs,
            "{name} {}: relocations",
            r.name
        );
        assert_eq!(got.meta.level, meta.level, "{name} {}: level", r.name);
        assert_eq!(got.meta.frame, meta.frame, "{name} {}: frame", r.name);
        assert_eq!(got.meta.slots, meta.slots, "{name} {}: slots", r.name);
        let ranges = |rs: &[nocompiler::profile::Range]| {
            rs.iter().map(|g| (g.off, g.len)).collect::<Vec<_>>()
        };
        assert_eq!(
            ranges(&got.meta.ranges),
            ranges(&meta.ranges),
            "{name} {}: ranges",
            r.name
        );
        assert_eq!(
            shift(&got.meta.nodes, got.meta.entry),
            shift(&meta.nodes, meta.entry),
            "{name} {}: tree",
            r.name
        );
        n += 1;
    }
    // Relink, if every function made it into the text.
    if all {
        if let Some(lld) = lld() {
            let o = dir.join(format!("{file}.o"));
            std::fs::write(&o, write_object(&obj).unwrap()).unwrap();
            let e = nocompiler::elf::Elf::parse(bytes).unwrap();
            let mut args: Vec<String> = vec![
                "-static".into(),
                "-e".into(),
                "_start".into(),
                "--build-id=none".into(),
                "-z".into(),
                "noseparate-code".into(),
            ];
            for s in &e.sections {
                if s.flags & nocompiler::elf::SHF_ALLOC != 0 && s.addr != 0 {
                    args.push(format!("--section-start={}={:#x}", s.name, s.addr));
                }
            }
            let mut order: Vec<_> = bin.funcs.iter().collect();
            order.sort_by_key(|f| f.entry);
            let of = dir.join(format!("{file}.order"));
            std::fs::write(
                &of,
                order
                    .iter()
                    .map(|f| format!("{}\n", f.name))
                    .collect::<String>(),
            )
            .unwrap();
            args.push(format!("--symbol-ordering-file={}", of.display()));
            let out = dir.join(format!("{file}.re.elf"));
            let st = Command::new(&lld)
                .args(&args)
                .arg(&o)
                .arg("-o")
                .arg(&out)
                .output()
                .unwrap();
            assert!(
                st.status.success(),
                "{name}: ld.lld: {}",
                String::from_utf8_lossy(&st.stderr)
            );
            let b2 = std::fs::read(&out).unwrap();
            let bin2 = nocompiler::load(&b2).unwrap();
            assert_eq!(bin2.text_addr, bin.text_addr, "{name}: .text address");
            assert_eq!(bin2.text, bin.text, "{name}: .text");
            let segs = |b: &nocompiler::Binary| {
                b.segments
                    .iter()
                    .map(|g| (g.name.clone(), g.addr, g.bytes.clone()))
                    .collect::<Vec<_>>()
            };
            assert_eq!(segs(&bin2), segs(&bin), "{name}: data");
            // And the metadata the object carried checks against the code.
            assert!(bin2.recorded.is_some(), "{name}: no .nocompiler.struct");
            assert!(
                bin2.check().iter().all(|r| r.result.is_ok()),
                "{name}: relinked binary does not check"
            );
        } else {
            eprintln!("SKIP relinking {name}: no ld.lld");
        }
    }
    (n, all)
}

fn tmp(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("nocompiler-text-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn committed_binaries_round_trip() {
    let dir = tmp("committed");
    let mut total = 0;
    for e in [
        "examples/elf/sum.elf",
        "examples/elf/hello.elf",
        "examples/elf/sum.link1.elf",
        "examples/elf/sum.link2.elf",
        "examples/demo/elf/sum.b.elf",
        "examples/demo/elf/cobs.b.elf",
    ] {
        let bytes = std::fs::read(root().join(e)).unwrap();
        let (n, all) = round_trip(e, &bytes, &dir);
        assert!(all, "{e}: a function below L1");
        total += n;
    }
    eprintln!("committed binaries: {total} functions round-trip");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn corpus_round_trips() {
    let have = |c: &str| {
        Command::new(c)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    };
    if !have("clang") || lld().is_none() {
        eprintln!("SKIP corpus_round_trips: needs clang and ld.lld");
        return;
    }
    let programs: &[(&str, &[&str])] = &[
        ("frames", &["crates/nocompiler/tests/cc/frames.c"]),
        ("fnptr", &["crates/nocompiler/tests/cc/fnptr.c"]),
        ("loops", &["crates/nocompiler/tests/cc/loops.c"]),
        ("recur", &["crates/nocompiler/tests/cc/recur.c"]),
        ("structs", &["crates/nocompiler/tests/cc/structs.c"]),
        ("switch", &["crates/nocompiler/tests/cc/switch.c"]),
        ("hello", &["examples/hello.c"]),
        (
            "cobs",
            &["examples/demo/src/cobs.c", "examples/demo/src/cobs_start.c"],
        ),
    ];
    let dir = tmp("corpus");
    let mut total = 0;
    for (name, srcs) in programs {
        let out = dir.join(format!("{name}.elf"));
        let args: Vec<String> = srcs
            .iter()
            .map(|s| root().join(s).display().to_string())
            .collect();
        nocompiler::cc::build(&args, &out).unwrap();
        let bytes = std::fs::read(&out).unwrap();
        let (n, all) = round_trip(name, &bytes, &dir);
        eprintln!(
            "{name}: {n} functions at L1 or above round-trip{}",
            if all { ", relinked byte for byte" } else { "" }
        );
        total += n;
    }
    eprintln!("corpus: {total} functions");
    assert!(total >= 40, "only {total} functions");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn what_the_text_refuses() {
    let cases = [
        (
            "func f\n  beq a0, zero, $x\n  ret\n",
            "$x is not an enclosing",
        ),
        ("func f\n  block $b\n  ret\n", "not closed"),
        ("func f\n  li a0, 1\n  ret\n", "unknown instruction `li`"),
        (
            "func f\n  addi a0, a0, %pcrel_lo(d)\n  ret\n",
            "without an earlier %pcrel_hi",
        ),
        ("func f\n  auipc a0, 4\n  ret\n", "%pcrel_hi"),
        ("func f\n  jal ra, g\n  ret\n", "`call f`"),
        ("func f\n  addi a0, a0, 1\n", "does not conform"),
        (
            "func f\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret\n",
            "declare it",
        ),
    ];
    for (src, want) in cases {
        let e = assemble(src).expect_err(src);
        assert!(e.contains(want), "`{src}`: {e}");
    }
}
