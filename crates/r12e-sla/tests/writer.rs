//! The writer measured against the only oracle there is for it: the files
//! Ghidra's own compiler produced.
//!
//! Reading a format and writing it are different claims. A reader can be
//! sloppy about which of two encodings a field used and still produce the
//! right model; a writer that is sloppy the same way produces a file nothing
//! else will read. So the gate here is byte equality of the payload: decode
//! every shipped `.sla`, encode the tree straight back, and require the same
//! bytes. Across the corpus that is 95 MB of exact agreement about tag forms,
//! chunk counts and value types, in the direction the reader cannot check.
//!
//! As elsewhere, a missing corpus reports and returns rather than failing, so
//! a fresh checkout still runs the fixtures.

use std::path::{Path, PathBuf};

use r12e_sla::{Level, Sla, deflate, emit, encode, inflate};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data")
}

fn find_sla(dir: &Path, out: &mut Vec<PathBuf>) {
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

fn corpus() -> Vec<PathBuf> {
    let mut out = Vec::new();
    find_sla(&fixtures(), &mut out);
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(v) = std::env::var("R12E_SLA_DIR") {
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

/// The headline claim about the encoder: it is the exact inverse of the
/// decoder over every file the reference compiler ever produced here.
#[test]
fn every_sla_payload_re_encodes_to_the_same_bytes() {
    let files = corpus();
    assert!(!files.is_empty(), "fixtures should always be found");

    let mut total = 0usize;
    let mut matched = 0usize;
    let mut bytes = 0usize;
    let mut mismatches: Vec<String> = Vec::new();

    for path in &files {
        let raw = std::fs::read(path).expect("readable");
        let payload = match inflate::inflate_zlib(&raw[4..], inflate::DEFAULT_LIMIT) {
            Ok(p) => p,
            Err(e) => {
                mismatches.push(format!("{}: inflate: {e}", path.display()));
                continue;
            }
        };
        let tree = match r12e_sla::decode::decode(&payload) {
            Ok(t) => t,
            Err(e) => {
                mismatches.push(format!("{}: decode: {e}", path.display()));
                continue;
            }
        };
        total += 1;
        let again = encode::encode(&tree).expect("a tree that was read can be written");
        if again == payload {
            matched += 1;
            bytes += payload.len();
        } else {
            // Name the first byte that differs: a wrong chunk count shows up
            // at the first value that needs it, and the offset says which.
            let at = again
                .iter()
                .zip(&payload)
                .position(|(a, b)| a != b)
                .unwrap_or(payload.len().min(again.len()));
            mismatches.push(format!(
                "{}: first difference at {at} (ours {} bytes, theirs {})",
                path.display(),
                again.len(),
                payload.len()
            ));
        }
    }

    println!("re-encoded {matched}/{total} payloads byte for byte, {bytes} bytes");
    assert!(mismatches.is_empty(), "{mismatches:#?}");
}

/// The container as a whole: our compressor, our decompressor, our tree.
#[test]
fn every_sla_survives_a_whole_container_round_trip() {
    let files = corpus();
    let mut total = 0usize;
    let mut ours = 0usize;
    let mut theirs = 0usize;
    for path in &files {
        let Ok(sla) = Sla::open(path) else { continue };
        let written = sla.to_bytes(Level::Fixed).expect("writes");
        assert_eq!(&written[..4], &[b's', b'l', b'a', sla.format_version]);
        let back = Sla::parse(&written).expect("reads back");
        assert_eq!(back.payload_len, sla.payload_len, "{}", path.display());
        assert_eq!(
            back.program.symbols.len(),
            sla.program.symbols.len(),
            "{}",
            path.display()
        );
        assert!(back.check().is_empty(), "{}", path.display());
        total += 1;
        ours += written.len();
        theirs += std::fs::metadata(path)
            .map(|m| m.len() as usize)
            .unwrap_or(0);
    }
    // Not a gate, a measurement: the fixed Huffman tables cost size against
    // zlib's dynamic ones and the number belongs in the record.
    println!(
        "{total} files rewritten; {ours} bytes against the reference compiler's {theirs} ({:.2}x)",
        ours as f64 / theirs.max(1) as f64
    );
}

/// Stored blocks are the control: if the Huffman path ever looks wrong, this
/// says whether the problem is the compressor or everything before it.
#[test]
fn stored_blocks_are_a_working_fallback() {
    let files = corpus();
    for path in files.iter().take(8) {
        let Ok(sla) = Sla::open(path) else { continue };
        let written = sla.to_bytes(Level::Stored).expect("writes");
        let back = Sla::parse(&written).expect("reads back");
        assert_eq!(back.payload_len, sla.payload_len);
    }
}

/// An external check on the compressor. Our inflater and our deflater sharing
/// a misreading of RFC 1951 would pass every test above, so the streams are
/// also handed to a zlib that is not ours.
#[test]
fn a_foreign_zlib_reads_what_we_write() {
    let Ok(out) = std::process::Command::new("python3")
        .arg("-c")
        .arg("import sys,zlib; sys.stdout.buffer.write(zlib.decompress(sys.stdin.buffer.read()))")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
    else {
        println!("no python3 on this machine, skipping the foreign zlib check");
        return;
    };
    drop(out);

    let mut checked = 0usize;
    for path in corpus().iter().take(12) {
        let Ok(sla) = Sla::open(path) else { continue };
        let payload = encode::encode(&sla.tree).expect("writes");
        for level in [Level::Fixed, Level::Stored] {
            let z = deflate::deflate_zlib(&payload, level);
            let got = python_inflate(&z).expect("python zlib accepts our stream");
            assert_eq!(got, payload, "{} at {level:?}", path.display());
            checked += 1;
        }
    }
    println!("{checked} streams decompressed by python's zlib");
}

fn python_inflate(data: &[u8]) -> Option<Vec<u8>> {
    use std::io::Write;
    let mut child = std::process::Command::new("python3")
        .arg("-c")
        .arg("import sys,zlib; sys.stdout.buffer.write(zlib.decompress(sys.stdin.buffer.read()))")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(data).ok()?;
    let out = child.wait_with_output().ok()?;
    out.status.success().then_some(out.stdout)
}

/// The structured writer, against the same oracle. This is the stronger claim
/// of the two: the tree that comes out of [`emit`] was rebuilt from spaces,
/// symbols, constructors and templates, so byte equality here says the model
/// holds everything the file did, in the order the file had it, with the value
/// types the file used.
#[test]
fn every_sla_rebuilds_from_the_model() {
    let files = corpus();
    let mut total = 0usize;
    let mut exact = 0usize;
    let mut bytes = 0usize;
    let mut differed: Vec<String> = Vec::new();
    let mut refused: Vec<String> = Vec::new();

    for path in &files {
        let Ok(sla) = Sla::open(path) else { continue };
        total += 1;
        let original = encode::encode(&sla.tree).expect("re-encodes");
        match emit::tree(&sla.program) {
            Ok(t) => {
                let got = encode::encode(&t).expect("encodes");
                if got == original {
                    exact += 1;
                    bytes += got.len();
                } else {
                    let at = got
                        .iter()
                        .zip(&original)
                        .position(|(a, b)| a != b)
                        .unwrap_or(original.len().min(got.len()));
                    differed.push(format!(
                        "{}: differs at {at} (ours {} theirs {})",
                        path.display(),
                        got.len(),
                        original.len()
                    ));
                }
            }
            Err(e) => refused.push(format!("{}: {e}", path.display())),
        }
    }

    println!(
        "rebuilt {exact}/{total} files byte for byte from the model, {bytes} bytes; \
         {} differed, {} refused",
        differed.len(),
        refused.len()
    );
    for d in differed.iter().take(10) {
        println!("  {d}");
    }
    for r in refused.iter().take(10) {
        println!("  {r}");
    }
    // A ratchet: every file the model can rebuild must rebuild exactly. A file
    // it refuses is a gap the coverage number already reports.
    assert!(differed.is_empty(), "{differed:#?}");
}

/// Where a rebuild differs, said in terms of the tree rather than a byte
/// offset. Kept because "differs at byte 10797" is not a bug report and this
/// is what turns one into a bug report.
fn first_difference(
    a: &r12e_sla::Node,
    b: &r12e_sla::Node,
    path: &mut Vec<String>,
) -> Option<String> {
    if a.id != b.id {
        return Some(format!("{}: element {} vs {}", path.join("/"), a.id, b.id));
    }
    if a.attrs != b.attrs {
        return Some(format!(
            "E{} at {}: attrs {:?} vs {:?}",
            a.id,
            path.join("/"),
            a.attrs,
            b.attrs
        ));
    }
    if a.children.len() != b.children.len() {
        return Some(format!(
            "E{} at {}: {} children vs {}; ids {:?} vs {:?}",
            a.id,
            path.join("/"),
            a.children.len(),
            b.children.len(),
            a.children.iter().map(|c| c.id).collect::<Vec<_>>(),
            b.children.iter().map(|c| c.id).collect::<Vec<_>>()
        ));
    }
    for (i, (x, y)) in a.children.iter().zip(&b.children).enumerate() {
        path.push(format!("E{}[{i}]", x.id));
        if let Some(d) = first_difference(x, y, path) {
            return Some(d);
        }
        path.pop();
    }
    None
}

#[test]
#[ignore = "diagnostic: prints where a rebuild first differs"]
fn report_rebuild_differences() {
    for path in corpus() {
        let Ok(sla) = Sla::open(&path) else { continue };
        let Ok(t) = emit::tree(&sla.program) else {
            continue;
        };
        let mut trail = Vec::new();
        if let Some(d) = first_difference(&t, &sla.tree, &mut trail) {
            println!("{}\n    {d}", path.display());
        }
    }
}
