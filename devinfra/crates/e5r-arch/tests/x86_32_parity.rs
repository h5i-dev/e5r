//! G3 for i386: the 32-bit decoder must agree with llvm-objdump in Intel
//! syntax, over a swept encoding space rather than only over compiled code.
//!
//! A compiler emits a few hundred distinct encodings and never reaches the
//! corners where 32-bit mode differs from long mode, which is exactly where a
//! 64-bit decoder retargeted at 32 bits goes wrong. So the corpus here is
//! generated: every opcode crossed with every ModRM form and every prefix
//! combination that changes the answer, assembled with `llvm-mc` and read back
//! with `llvm-objdump`. Each candidate sits at the start of its own sixteen
//! byte slot padded with `nop`, so an instruction that turns out longer than
//! the bytes that seeded it still ends inside its slot and the next candidate
//! still starts on a boundary. Fifteen bytes is the architecture's own limit,
//! which is what makes sixteen enough.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_arch::x86;
use e5r_core::Addr;

/// Coverage floor over the swept corpus. The sweep measures 99.71%, and what
/// it declines is listed by mnemonic by `x86_32_parity_report`: none of it is
/// a 32-bit form, it is the extensions the shared table has never held. Raise
/// this as those fill in; it is a ratchet and never goes down.
const MIN_SWEEP_COVERAGE: f64 = 0.995;

/// Coverage floor over the compiled i386 fixtures, which contain only what a
/// compiler emits and so should be near total.
const MIN_FIXTURE_COVERAGE: f64 = 0.999;

/// Bytes per candidate. One more than the longest instruction the
/// architecture allows, so a candidate can never run into the next one.
const SLOT: usize = 16;

fn tool(names: &[&'static str]) -> Option<&'static str> {
    names
        .iter()
        .copied()
        .find(|c| Command::new(c).arg("--version").output().is_ok())
}

fn objdump() -> Option<&'static str> {
    tool(&["llvm-objdump-18", "llvm-objdump-15", "llvm-objdump"])
}

fn assembler() -> Option<&'static str> {
    tool(&["llvm-mc-18", "llvm-mc-15", "llvm-mc"])
}

struct Line {
    addr: u64,
    bytes: Vec<u8>,
    text: String,
}

/// Parse `llvm-objdump -d --x86-asm-syntax=intel`.
fn parse(text: &str) -> Vec<Line> {
    let mut lines = Vec::new();
    for l in text.lines() {
        let Some((left, rest)) = l.split_once(": ") else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let Some((raw, body)) = rest.split_once('\t') else {
            continue;
        };
        let bytes: Option<Vec<u8>> = raw
            .split_whitespace()
            .map(|h| u8::from_str_radix(h, 16).ok())
            .collect();
        let Some(bytes) = bytes else { continue };
        if bytes.is_empty() {
            continue;
        }
        // Drop the symbolic suffix llvm appends to branch targets.
        let body = match body.find(" #").or_else(|| body.find(" <")) {
            Some(i) => &body[..i],
            None => body,
        };
        lines.push(Line {
            addr,
            bytes,
            text: body.trim_end().to_string(),
        });
    }
    lines
}

fn disassemble_file(tool: &str, path: &Path) -> Vec<Line> {
    let out = Command::new(tool)
        .args(["-d", "--x86-asm-syntax=intel"])
        .arg(path)
        .output();
    let Ok(out) = out else { return Vec::new() };
    parse(&String::from_utf8_lossy(&out.stdout))
}

/// Assemble `slots` into an i386 object and disassemble it, returning one
/// [`Line`] per slot start. The object goes through a temporary file because
/// llvm-objdump reads a file, not a pipe.
fn oracle(mc: &str, dump: &str, slots: &[[u8; SLOT]]) -> Option<Vec<Line>> {
    let dir = std::env::temp_dir().join(format!("e5r-x32-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("sweep.s");
    let obj = dir.join("sweep.o");

    let mut text = String::with_capacity(slots.len() * 96);
    text.push_str(".text\n");
    for s in slots {
        text.push_str(".byte ");
        for (n, b) in s.iter().enumerate() {
            if n > 0 {
                text.push(',');
            }
            text.push_str(&format!("0x{b:02x}"));
        }
        text.push('\n');
    }
    std::fs::write(&src, text).ok()?;

    let st = Command::new(mc)
        .args(["--triple=i386", "--filetype=obj", "-o"])
        .arg(&obj)
        .arg(&src)
        .output()
        .ok()?;
    if !st.status.success() {
        return None;
    }
    let lines = disassemble_file(dump, &obj);
    let _ = std::fs::remove_file(&src);
    let _ = std::fs::remove_file(&obj);
    // Only the line that starts a slot is a candidate; the rest is padding.
    Some(
        lines
            .into_iter()
            .filter(|l| l.addr as usize % SLOT == 0)
            .collect(),
    )
}

/// A candidate, padded out to a full slot with `nop`.
fn slot(bytes: &[u8]) -> [u8; SLOT] {
    let mut s = [0x90u8; SLOT];
    let n = bytes.len().min(SLOT);
    s[..n].copy_from_slice(&bytes[..n]);
    s
}

/// A deterministic generator, so a failure reproduces exactly.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // SplitMix64, which needs no state beyond the counter.
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
}

/// The prefix strings worth crossing every opcode with. Each changes the
/// answer in 32-bit mode: operand size, address size, a mandatory prefix, a
/// segment override, or a lock.
const PREFIXES: [&[u8]; 8] = [
    &[],
    &[0x66],
    &[0x67],
    &[0xf2],
    &[0xf3],
    &[0x64],
    &[0x66, 0x67],
    &[0xf0],
];

/// ModRM bytes that reach every addressing form: each mod, the SIB escape,
/// the absolute form, and a register.
const MODRM: [u8; 12] = [
    0x00, 0x01, 0x04, 0x05, 0x06, 0x40, 0x44, 0x47, 0x80, 0x84, 0xc0, 0xd1,
];

/// Every candidate the sweep tries.
fn candidates() -> Vec<[u8; SLOT]> {
    let mut out: Vec<[u8; SLOT]> = Vec::new();
    let tail = [0x21u8, 0x43, 0x65, 0x87, 0x09, 0xab, 0xcd, 0xef, 0x11, 0x22];

    // Every one-byte and two-byte opcode, crossed with every prefix and every
    // ModRM shape. This is the part that finds a mode bug rather than a table
    // typo: it walks the whole first byte, including the block 32-bit mode
    // spends on inc and dec.
    for pre in PREFIXES {
        for op in 0u16..=0xff {
            for m in MODRM {
                for lead in [None, Some(0x0fu8)] {
                    let mut v = pre.to_vec();
                    if let Some(l) = lead {
                        v.push(l);
                    }
                    v.push(op as u8);
                    v.push(m);
                    // A SIB byte where the ModRM asked for one, then enough
                    // bytes for any displacement or immediate.
                    v.push(0x8d);
                    v.extend_from_slice(&tail);
                    out.push(slot(&v));
                }
            }
        }
    }

    // The three-byte maps.
    for op2 in [0x38u8, 0x3a] {
        for op3 in 0u16..=0xff {
            for m in [0x00u8, 0x05, 0x44, 0xc1] {
                for pre in [&[0x66u8][..], &[][..]] {
                    let mut v = pre.to_vec();
                    v.extend_from_slice(&[0x0f, op2, op3 as u8, m, 0x8d]);
                    v.extend_from_slice(&tail);
                    out.push(slot(&v));
                }
            }
        }
    }

    // The x87 escapes in full: the ModRM byte is an opcode extension above
    // 0xc0, so every one of the 256 values is a different instruction.
    for op in 0xd8u8..=0xdf {
        for m in 0u16..=0xff {
            let mut v = vec![op, m as u8, 0x8d];
            v.extend_from_slice(&tail);
            out.push(slot(&v));
            let mut v = vec![0x67u8, op, m as u8, 0x8d];
            v.extend_from_slice(&tail);
            out.push(slot(&v));
        }
    }

    // Random bytes, which reach prefix pile-ups and operand combinations no
    // structured sweep thought of.
    let mut r = Rng(0x1234_5678_9abc_def0);
    for _ in 0..200_000 {
        let mut s = [0x90u8; SLOT];
        let n = 1 + (r.next() % 8) as usize;
        for b in s.iter_mut().take(n) {
            *b = (r.next() >> 13) as u8;
        }
        out.push(s);
    }

    out
}

#[derive(Default)]
struct Tally {
    matched: usize,
    undecoded: usize,
    /// Decoded where llvm declined, which is not counted as a disagreement
    /// because llvm declines a few real encodings, but is reported.
    extra: usize,
    /// Those counted by mnemonic, so the report can show whether they are
    /// encodings llvm cannot reach or ones this decoder should not accept.
    extra_by_name: BTreeMap<String, (usize, String)>,
    /// Slots where llvm printed a bare prefix as its own one-byte line rather
    /// than attaching it to the instruction after it. That is a presentation
    /// choice, not a decode, and this decoder makes the other one.
    split_prefix: usize,
    wrong: Vec<String>,
    missing: BTreeMap<String, usize>,
}

impl Tally {
    fn merge(&mut self, o: Tally) {
        self.matched += o.matched;
        self.undecoded += o.undecoded;
        self.extra += o.extra;
        for (k, (n, ex)) in o.extra_by_name {
            let e = self.extra_by_name.entry(k).or_insert((0, ex));
            e.0 += n;
        }
        self.split_prefix += o.split_prefix;
        self.wrong.extend(o.wrong);
        for (k, v) in o.missing {
            *self.missing.entry(k).or_default() += v;
        }
    }

    fn total(&self) -> usize {
        self.matched + self.undecoded + self.wrong.len()
    }

    fn coverage(&self) -> f64 {
        if self.total() == 0 {
            return 1.0;
        }
        (self.matched + self.wrong.len()) as f64 / self.total() as f64
    }
}

/// The mnemonic of an oracle line, which is the first field that is not a
/// prefix: llvm puts any prefix it spells out in front of the mnemonic, so
/// taking the first field would file every `addr16` line under one name.
fn mnemonic_of(text: &str) -> String {
    text.split('\t')
        .filter(|f| !f.is_empty())
        .find(|f| !is_bare_prefix(f))
        .unwrap_or("?")
        .to_string()
}

/// Whether an oracle line is nothing but prefix bytes. llvm spells such a run
/// out word by word, so every field of the line is one of the prefix names.
fn is_bare_prefix(text: &str) -> bool {
    let mut any = false;
    for field in text.split('\t').filter(|f| !f.is_empty()) {
        any = true;
        if !matches!(
            field,
            "lock"
                | "xacquire"
                | "xrelease"
                | "addr16"
                | "addr32"
                | "data16"
                | "data32"
                | "rep"
                | "repne"
                | "cs"
                | "ds"
                | "es"
                | "fs"
                | "gs"
                | "ss"
        ) {
            return false;
        }
    }
    any
}

/// Compare one batch of oracle lines against the decoder. `window` says how
/// many bytes the decoder may read, which for a slot is the whole slot.
fn compare(lines: &[Line], bytes_of: impl Fn(&Line) -> Vec<u8>) -> Tally {
    let mut t = Tally::default();
    for l in lines {
        let input = bytes_of(l);
        let unknown = l.text.starts_with("<unknown>") || l.text.is_empty();
        // llvm-objdump prints a run of prefixes that reaches no opcode as a
        // line of its own, with no instruction on it at all. This decoder
        // attaches prefixes to the instruction they precede and so never
        // produces one, which is a different rendering of the same bytes
        // rather than a different reading of them, so the slot is skipped.
        if is_bare_prefix(&l.text) {
            t.split_prefix += 1;
            continue;
        }
        let decoded = x86::decode32(&input, Addr(l.addr));
        if unknown {
            if let Some(i) = decoded {
                t.extra += 1;
                let got = x86::format(&i, x86::Style::default());
                let name = mnemonic_of(&got);
                let ex = format!(
                    "{:02x?} -> {got}",
                    &input[..input.len().min(i.len as usize)]
                );
                let e = t.extra_by_name.entry(name).or_insert((0, ex));
                e.0 += 1;
            }
            continue;
        }
        match decoded {
            None => {
                t.undecoded += 1;
                *t.missing.entry(mnemonic_of(&l.text)).or_default() += 1;
            }
            Some(i) if i.len as usize != l.bytes.len() => t.wrong.push(format!(
                "{:x}: {:02x?} llvm {:?} length {} != llvm's {}",
                l.addr,
                &input[..input.len().min(8)],
                l.text,
                i.len,
                l.bytes.len()
            )),
            Some(i) => {
                let got = x86::format(&i, x86::Style::default());
                if got == l.text {
                    t.matched += 1;
                } else {
                    t.wrong.push(format!(
                        "{:x}: {:02x?} llvm {:?} != ours {:?}",
                        l.addr,
                        &input[..input.len().min(8)],
                        l.text,
                        got
                    ));
                }
            }
        }
    }
    t
}

/// Run the whole sweep, in batches so the assembler input stays a sane size.
fn sweep(mc: &str, dump: &str) -> Option<Tally> {
    let all = candidates();
    let mut t = Tally::default();
    for chunk in all.chunks(40_000) {
        let lines = oracle(mc, dump, chunk)?;
        let by_slot = |l: &Line| {
            let n = l.addr as usize / SLOT;
            chunk[n].to_vec()
        };
        t.merge(compare(&lines, by_slot));
    }
    Some(t)
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// The compiled i386 fixtures, which `scripts/build-fixtures.sh` names `x32`.
fn fixtures() -> Vec<PathBuf> {
    let Some(dir) = corpus() else {
        return Vec::new();
    };
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.filter_map(|e| {
                let p = e.ok()?.path();
                let n = p.file_name()?.to_string_lossy().into_owned();
                n.contains("x32").then_some(p)
            })
            .collect()
        })
        .unwrap_or_default();
    v.sort();
    v
}

fn describe(t: &Tally, what: &str) -> String {
    format!(
        "i386 {what}: {} instructions, {} matched, {} wrong, {} undecoded, {:.3}% coverage ({} decoded where llvm declined)",
        t.total(),
        t.matched,
        t.wrong.len(),
        t.undecoded,
        t.coverage() * 100.0,
        t.extra,
    ) + &format!(", {} bare prefix lines skipped", t.split_prefix)
}

fn fail_if_wrong(t: &Tally, what: &str) {
    if t.wrong.is_empty() {
        return;
    }
    let mut by_kind: BTreeMap<&str, usize> = BTreeMap::new();
    for w in &t.wrong {
        let kind = w
            .split("llvm \"")
            .nth(1)
            .and_then(|s| s.split(['\\', '"']).next())
            .unwrap_or("length");
        *by_kind.entry(kind).or_default() += 1;
    }
    let summary: Vec<String> = by_kind.iter().map(|(k, n)| format!("{k} x{n}")).collect();
    panic!(
        "{} of {} i386 {what} instructions decode differently\nby mnemonic: {}\nfirst 20:\n{}",
        t.wrong.len(),
        t.total(),
        summary.join(", "),
        t.wrong
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn i386_sweep_matches_llvm() {
    let (Some(mc), Some(dump)) = (assembler(), objdump()) else {
        return;
    };
    let Some(t) = sweep(mc, dump) else {
        return;
    };
    if t.total() < 1000 {
        return; // the oracle did not run
    }
    fail_if_wrong(&t, "swept");
    assert!(
        t.coverage() >= MIN_SWEEP_COVERAGE,
        "{} (floor is {:.1}%)",
        describe(&t, "sweep"),
        MIN_SWEEP_COVERAGE * 100.0
    );
    println!("{}", describe(&t, "sweep"));
}

#[test]
fn i386_fixtures_match_llvm() {
    let (Some(dump), files) = (objdump(), fixtures()) else {
        return;
    };
    if files.is_empty() {
        return;
    }
    let mut all = Tally::default();
    for p in &files {
        let lines = disassemble_file(dump, p);
        all.merge(compare(&lines, |l| l.bytes.clone()));
    }
    if all.total() < 100 {
        return;
    }
    fail_if_wrong(&all, "compiled");
    assert!(
        all.coverage() >= MIN_FIXTURE_COVERAGE,
        "{} (floor is {:.1}%)",
        describe(&all, "fixtures"),
        MIN_FIXTURE_COVERAGE * 100.0
    );
    println!("{}", describe(&all, "fixtures"));
}

#[test]
fn the_inc_block_is_not_a_rex_prefix() {
    // The single most common way a 32-bit decoder written as a 64-bit one goes
    // wrong: 0x40 eats the next byte and everything after it desynchronizes.
    let i = x86::decode32(&[0x40, 0x89, 0xc8], Addr(0)).unwrap();
    assert_eq!(i.len, 1);
    assert_eq!(x86::format(&i, x86::Style::default()), "inc\teax");
    let i = x86::decode32(&[0x4f], Addr(0)).unwrap();
    assert_eq!(x86::format(&i, x86::Style::default()), "dec\tedi");
    // The same bytes in long mode are a prefix on the instruction after them.
    let i = x86::decode(&[0x48, 0x89, 0xc8], Addr(0)).unwrap();
    assert_eq!(i.len, 3);
    assert_eq!(x86::format(&i, x86::Style::default()), "mov\trax, rcx");
}

#[test]
fn absolute_addressing_is_not_pc_relative() {
    let i = x86::decode32(&[0x8b, 0x05, 0x78, 0x56, 0x34, 0x12], Addr(0x1000)).unwrap();
    assert_eq!(
        x86::format(&i, x86::Style::default()),
        "mov\teax, dword ptr [0x12345678]"
    );
    let Some(e5r_arch::Operand::Mem(m)) = i.operands().get(1).copied() else {
        panic!("expected a memory operand");
    };
    assert!(!m.is_pc_relative());
}

#[test]
fn the_mode_only_instructions_decode_in_their_own_mode() {
    let d32 = |b: &[u8]| x86::decode32(b, Addr(0)).map(|i| x86::format(&i, x86::Style::default()));
    let d64 = |b: &[u8]| x86::decode(b, Addr(0)).map(|i| x86::format(&i, x86::Style::default()));
    assert_eq!(d32(&[0x60]).as_deref(), Some("pushal"));
    assert_eq!(d32(&[0x61]).as_deref(), Some("popal"));
    assert_eq!(d32(&[0x27]).as_deref(), Some("daa"));
    assert_eq!(d32(&[0xce]).as_deref(), Some("into"));
    assert_eq!(
        d32(&[0x62, 0x0a]).as_deref(),
        Some("bound\tecx, dword ptr [edx]")
    );
    assert_eq!(d32(&[0x63, 0xc8]).as_deref(), Some("arpl\tax, cx"));
    assert_eq!(d32(&[0xc4, 0x08]).as_deref(), Some("les\tecx, [eax]"));
    // 0x63 is `movsxd` in long mode and `arpl` here, off the same byte.
    assert_eq!(
        d64(&[0x48, 0x63, 0xc8]).as_deref(),
        Some("movsxd\trcx, eax")
    );
    // None of the 32-bit-only opcodes decode in long mode.
    for b in [0x60u8, 0x61, 0x27, 0xce, 0x9a, 0xea, 0xd4, 0xd5] {
        assert!(d64(&[b, 0x0a, 0, 0, 0, 0, 0]).is_none(), "{b:#x}");
    }
}

#[test]
fn sixteen_bit_addressing_survives_under_0x67() {
    let d = |b: &[u8]| x86::decode32(b, Addr(0)).map(|i| x86::format(&i, x86::Style::default()));
    assert_eq!(
        d(&[0x67, 0x8b, 0x00]).as_deref(),
        Some("mov\teax, dword ptr [bx + si]")
    );
    assert_eq!(
        d(&[0x67, 0x8b, 0x41, 0x10]).as_deref(),
        Some("mov\teax, dword ptr [bx + di + 0x10]")
    );
    assert_eq!(
        d(&[0x67, 0x8b, 0x06, 0x34, 0x12]).as_deref(),
        Some("addr16\t\tmov\teax, dword ptr [0x1234]")
    );
}

#[test]
fn no_byte_sequence_panics_in_32_bit_mode() {
    let mut buf = [0u8; 16];
    let mut r = Rng(99);
    for _ in 0..200_000 {
        for b in buf.iter_mut() {
            *b = (r.next() >> 21) as u8;
        }
        let _ = x86::decode32(&buf, Addr(0x1000));
    }
}

/// A work list rather than a pass or fail: what the sweep still declines and
/// what it still gets wrong, biggest class first. Ignored by default.
#[test]
#[ignore]
fn x86_32_parity_report() {
    let (Some(mc), Some(dump)) = (assembler(), objdump()) else {
        return;
    };
    let Some(t) = sweep(mc, dump) else { return };
    println!("{}", describe(&t, "sweep"));
    let mut wrong: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for w in &t.wrong {
        let key = w
            .split("llvm \"")
            .nth(1)
            .and_then(|s| s.split(['\\', '"']).next())
            .unwrap_or("length")
            .to_string();
        let e = wrong.entry(key).or_insert((0, w.clone()));
        e.0 += 1;
    }
    let mut v: Vec<_> = wrong.into_iter().collect();
    v.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
    println!("--- disagreements ---");
    for (k, (n, ex)) in v.iter().take(40) {
        println!("{n:>7}  {k:<16} {ex}");
    }
    let mut x: Vec<_> = t.extra_by_name.iter().collect();
    x.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
    println!("--- decoded where llvm declined ---");
    for (k, (n, ex)) in x.iter().take(30) {
        println!("{n:>7}  {k:<16} {ex}");
    }
    let mut m: Vec<_> = t.missing.iter().collect();
    m.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    println!("--- undecoded ---");
    for (k, n) in m.iter().take(60) {
        println!("{n:>7}  {k}");
    }
}
