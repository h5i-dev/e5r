//! Load every `.sla` we can find, assert it is self-consistent, and report how
//! much of each file the model accounts for.
//!
//! The committed fixtures under `tests/data` are always read. A real Ghidra
//! tree is read too when one is on the machine: set `E5R_SLA_DIR` to a
//! directory to search, or let the test look in the usual install locations.
//! Following the repository convention, a missing corpus makes the test report
//! and return rather than fail, so a fresh checkout still runs what it can.

use std::path::{Path, PathBuf};

use e5r_sla::{Inconsistency, Sla};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

fn find_sla(dir: &Path, out: &mut Vec<PathBuf>) {
    // Depth is bounded by the directory tree, and a Ghidra install is about
    // six levels deep, so a plain recursion is fine here.
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            find_sla(&p, out);
        } else if p.extension().is_some_and(|x| x == "sla") {
            out.push(p);
        }
    }
}

/// Everything to read: the fixtures, plus any Ghidra tree we can find.
fn corpus() -> Vec<PathBuf> {
    let mut out = Vec::new();
    find_sla(&fixtures(), &mut out);

    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(v) = std::env::var("E5R_SLA_DIR") {
        roots.extend(v.split(':').filter(|s| !s.is_empty()).map(PathBuf::from));
    }
    if let Ok(home) = std::env::var("HOME") {
        roots.push(PathBuf::from(&home).join(".local/share/ghidra-cli/ghidra"));
        roots.push(PathBuf::from(&home).join("ghidra"));
    }
    roots.push(PathBuf::from("/opt/ghidra"));
    for r in roots {
        if r.is_dir() {
            find_sla(&r, &mut out);
        }
    }
    out.sort();
    out.dedup();
    out
}

#[test]
fn every_sla_loads_and_is_self_consistent() {
    let files = corpus();
    assert!(
        !files.is_empty(),
        "the committed fixtures should always be found"
    );

    let mut total_payload = 0usize;
    let mut total_interpreted = 0usize;
    let mut worst: Option<(f64, PathBuf)> = None;
    let mut unknown_ids: Vec<(u32, usize)> = Vec::new();
    let mut failures: Vec<String> = Vec::new();

    for path in &files {
        let sla = match Sla::open(path) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{}: {e}", path.display()));
                continue;
            }
        };
        assert!(
            sla.version_is_known(),
            "{}: unexpected format version",
            path.display()
        );

        let problems = sla.check();
        if !problems.is_empty() {
            // Print a bounded sample; a wall of identical lines helps nobody.
            let sample: Vec<&Inconsistency> = problems.iter().take(5).collect();
            failures.push(format!(
                "{}: {} inconsistencies, first: {sample:?}",
                path.display(),
                problems.len()
            ));
        }

        total_payload += sla.coverage.total;
        total_interpreted += sla.coverage.interpreted;
        let f = sla.coverage.fraction();
        if worst.as_ref().is_none_or(|(w, _)| f < *w) {
            worst = Some((f, path.clone()));
        }
        for u in &sla.coverage.unknown {
            match unknown_ids.iter_mut().find(|(id, _)| *id == u.id) {
                Some((_, b)) => *b += u.bytes,
                None => unknown_ids.push((u.id, u.bytes)),
            }
        }
    }

    unknown_ids.sort_by_key(|(_, b)| std::cmp::Reverse(*b));
    let pct = 100.0 * total_interpreted as f64 / total_payload.max(1) as f64;
    println!(
        "{} files, {total_payload} payload bytes, {total_interpreted} interpreted ({pct:.2}%), \
         {} raw",
        files.len(),
        total_payload - total_interpreted
    );
    if let Some((f, p)) = &worst {
        println!("least covered: {} at {:.2}%", p.display(), f * 100.0);
    }
    println!(
        "uninterpreted element ids by bytes: {:?}",
        &unknown_ids[..unknown_ids.len().min(12)]
    );

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn the_minimal_fixture_reads_the_way_its_source_says() {
    let sla = Sla::open(fixtures().join("minimal.sla")).expect("fixture loads");
    let p = &sla.program;

    // `define endian = little; define alignment = 1;`
    assert!(!p.big_endian);
    assert_eq!(p.alignment, 1);

    // Four spaces: OTHER and unique are implicit, ram and register declared.
    let names: Vec<&str> = p.spaces.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names, ["OTHER", "unique", "ram", "register"]);
    assert_eq!(p.default_space.as_deref(), Some("ram"));
    let ram = p.spaces.iter().find(|s| s.name == "ram").unwrap();
    assert_eq!(ram.size, 8);

    // `define register offset=0x0 size=8 [ sp r0 ];`
    let sp = p
        .symbols
        .iter()
        .find(|s| s.name.as_deref() == Some("sp"))
        .expect("sp exists");
    match sp.body {
        e5r_sla::SymbolBody::Varnode { offset, size, .. } => {
            assert_eq!((offset, size), (0, 8));
        }
        _ => panic!("sp should be a varnode"),
    }
    let r0 = p
        .symbols
        .iter()
        .find(|s| s.name.as_deref() == Some("r0"))
        .unwrap();
    match r0.body {
        e5r_sla::SymbolBody::Varnode { offset, size, .. } => {
            assert_eq!((offset, size), (8, 8));
        }
        _ => panic!("r0 should be a varnode"),
    }

    // One instruction subtable holding the single `:nop` constructor.
    assert_eq!(p.constructor_count(), 1);
    assert!(sla.check().is_empty());
}

#[test]
fn the_token_fixture_reads_its_fields_and_pcode() {
    let sla = Sla::open(fixtures().join("tokens.sla")).expect("fixture loads");
    let p = &sla.program;

    // `op = (8,15)` of a little-endian 16-bit token: byte 1, no shift.
    let op = p
        .symbols
        .iter()
        .find(|s| s.name.as_deref() == Some("op"))
        .expect("op field");
    match &op.body {
        e5r_sla::SymbolBody::Value { field: Some(f) } => {
            let f = f.token().expect("op is cut from an instruction token");
            assert_eq!((f.start_bit, f.end_bit), (8, 15));
            assert_eq!((f.start_byte, f.end_byte, f.shift), (1, 1, 0));
            assert!(!f.signed);
        }
        _ => panic!("op should be a token field value"),
    }
    // `imm = (0,7) signed`
    let imm = p
        .symbols
        .iter()
        .find(|s| s.name.as_deref() == Some("imm"))
        .unwrap();
    match &imm.body {
        e5r_sla::SymbolBody::Value { field: Some(f) } => {
            assert!(f.token().expect("a token field").signed);
        }
        _ => panic!("imm should be a token field value"),
    }
    // `attach variables [ rs rd ] [ r0 .. sp ]` gives sixteen entries.
    let rd = p
        .symbols
        .iter()
        .find(|s| s.name.as_deref() == Some("rd"))
        .unwrap();
    match &rd.body {
        e5r_sla::SymbolBody::VarnodeList { entries, .. } => assert_eq!(entries.len(), 16),
        _ => panic!("rd should be an attached varnode list"),
    }

    // Four constructors; `ldi` spans two tokens, so it is four bytes long.
    assert_eq!(p.constructor_count(), 4);
    let table = p.subtables().next().unwrap();
    let ctors = match &table.body {
        e5r_sla::SymbolBody::Subtable { constructors, .. } => constructors,
        _ => unreachable!(),
    };
    let lengths: Vec<u64> = ctors.iter().map(|c| c.length).collect();
    assert_eq!(lengths, [2, 2, 4, 2]);
    // They are on consecutive source lines, which is how the line attribute
    // was identified in the first place.
    let lines: Vec<u64> = ctors.iter().map(|c| c.line).collect();
    assert_eq!(lines, [17, 18, 19, 20]);

    // `:add rd, rs ... { rd = rd + rs; }` is one INT_ADD (p-code opcode 19).
    let add = &ctors[1];
    assert_eq!(add.templates.len(), 1);
    let ops = &add.templates[0].ops;
    assert_eq!(ops.len(), 1);
    assert_eq!(ops[0].opcode, 19);
    assert!(ops[0].output.is_some());
    assert_eq!(ops[0].inputs.len(), 2);

    assert!(sla.check().is_empty());
}

#[test]
fn decision_patterns_are_masks_over_the_instruction_bytes() {
    let sla = Sla::open(fixtures().join("tokens.sla")).unwrap();
    let table = sla.program.subtables().next().unwrap();
    let d = match &table.body {
        e5r_sla::SymbolBody::Subtable {
            decision: Some(d), ..
        } => d,
        _ => panic!("the instruction table should have a decision tree"),
    };
    // Four constructors differing in the low two bits of `op`, which is byte 1
    // of the stream, so the split is on absolute bits 14 and 15.
    assert_eq!(d.number, 4);
    assert_eq!((d.start_bit, d.num_bits), (14, 2));
    assert_eq!(d.children.len(), 4);

    // `:add is op=0x01` constrains one byte at offset 1 to 0x01.
    let (_, pat) = &d.children[1].pairs[0];
    let b = &pat.instruction[0];
    assert_eq!((b.offset, b.bytes), (1, 1));
    assert_eq!(b.words[0].mask, 0xff00_0000);
    assert_eq!(b.words[0].value, 0x0100_0000);
}
