//! M2: how much of a real instruction set lifts, and what does not.
//!
//! The decode gates measure agreement with objdump. This measures the other
//! half: every instruction the engine decodes is lifted, and what comes out is
//! counted. A lift that produces nothing, or that quietly drops a `define
//! pcodeop`, would pass every parity test and be useless, so the number that
//! matters here is how many instructions lift *completely*, with the rest
//! broken out by what stopped them.
//!
//! Nothing here asserts that the p-code is correct. Proving that needs an
//! oracle that runs the instructions, which is M5's emulator gate and not this
//! one. What is asserted is that lifting is total, honest and bounded: it
//! terminates, it does not panic, it reports what it could not model, and the
//! fraction it models completely does not fall.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_sleigh::{Decoder, Spec, pcode};

fn ghidra() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("E5R_GHIDRA") {
        let p = PathBuf::from(p);
        return p.is_dir().then_some(p);
    }
    for guess in [
        "../ghidra",
        "../../ghidra",
        concat!(env!("HOME"), "/Ref/ghidra"),
        "/opt/ghidra",
    ] {
        let p = PathBuf::from(guess);
        if p.join("Ghidra/Processors").is_dir() {
            return Some(p);
        }
    }
    None
}

fn language(rel: &str) -> Option<Spec> {
    let p = ghidra()?.join("Ghidra/Processors").join(rel);
    p.is_file()
        .then(|| e5r_sleigh::parse_file(&p).expect("the specification parses"))
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

/// Every instruction address and encoding objdump found in a file.
fn encodings(tool: &str, args: &[&str], path: &Path) -> Vec<(u64, Vec<u8>)> {
    let Ok(out) = Command::new(tool).args(args).arg(path).output() else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lines = Vec::new();
    for l in text.lines() {
        let Some((left, rest)) = l.split_once(':') else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let mut bytes = Vec::new();
        let mut saw_text = false;
        for tok in rest.split_whitespace() {
            let hex = !tok.is_empty() && tok.bytes().all(|b| b.is_ascii_hexdigit());
            if hex && tok.len() == 2 {
                bytes.push(u8::from_str_radix(tok, 16).unwrap());
            } else if hex && bytes.is_empty() && matches!(tok.len(), 4 | 8) {
                for i in (0..tok.len()).step_by(2) {
                    bytes.push(u8::from_str_radix(&tok[i..i + 2], 16).unwrap());
                }
                bytes.reverse();
                saw_text = true;
                break;
            } else {
                saw_text = true;
                break;
            }
        }
        if !bytes.is_empty() && saw_text {
            lines.push((addr, bytes));
        }
    }
    lines
}

fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

fn llvm_objdump() -> Option<String> {
    ["llvm-objdump", "llvm-objdump-18", "llvm-objdump-15"]
        .into_iter()
        .find(|n| have(n))
        .map(str::to_string)
}

fn files(dir: &Path, pred: impl Fn(&str) -> bool) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.file_name().and_then(|n| n.to_str()).is_some_and(&pred))
        .collect();
    out.sort();
    out
}

/// What lifting a corpus found.
#[derive(Default)]
struct Tally {
    lifted: usize,
    complete: usize,
    empty: usize,
    ops: usize,
    /// What stopped a lift being complete, by reason, most common first.
    reasons: BTreeMap<String, usize>,
}

impl Tally {
    fn add(&mut self, p: &pcode::Pcode) {
        self.lifted += 1;
        self.ops += p.ops.len();
        if p.is_complete() {
            self.complete += 1;
        }
        if p.ops.is_empty() {
            self.empty += 1;
        }
        for r in &p.unsupported {
            *self.reasons.entry(r.clone()).or_default() += 1;
        }
    }

    fn report(&self, what: &str) {
        eprintln!(
            "{what}: {} lifted, {} complete ({:.1}%), {} produced no operations, {} operations, {:.1} per instruction",
            self.lifted,
            self.complete,
            100.0 * self.complete as f64 / self.lifted.max(1) as f64,
            self.empty,
            self.ops,
            self.ops as f64 / self.lifted.max(1) as f64,
        );
        let mut worst: Vec<_> = self.reasons.iter().collect();
        worst.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
        for (r, n) in worst.iter().take(10) {
            eprintln!("  x{n} {r}");
        }
    }
}

/// The fraction of decoded instructions that lift with nothing unmodelled.
/// These only rise.
///
/// A `define pcodeop` used to count against this, because it lifted to an
/// `Unimplemented` that lost the operation's name and its arguments. It now
/// lifts to `Opcode::Other` carrying both, which is what the specification
/// said: a named operation with no p-code. What is left over is `cpool`,
/// `newobject` and the delay-slot directives, and the corpus has none of them,
/// so all three floors are at one.
mod floor {
    pub const AARCH64: f64 = 1.0;
    pub const RISCV64: f64 = 1.0;
    pub const X86_64: f64 = 1.0;
}

#[test]
fn aarch64_lifts() {
    let (Some(spec), Some(dir)) = (language("AARCH64/data/languages/AARCH64.slaspec"), corpus())
    else {
        return;
    };
    if !have("objdump") {
        return;
    }
    let mut t = Tally::default();
    for path in files(&dir, |n| n.contains(".a64.") && !n.ends_with(".out")) {
        let mut d = Decoder::new(&spec);
        for (addr, bytes) in encodings("objdump", &["-d", "--show-raw-insn"], &path) {
            let Ok(insn) = d.decode(&bytes, addr) else {
                continue;
            };
            t.add(&pcode::lift(&spec, &insn));
        }
    }
    t.report("AArch64");
    assert!(t.lifted > 10_000, "the corpus must be worth measuring");
    let rate = t.complete as f64 / t.lifted as f64;
    assert!(
        rate >= floor::AARCH64,
        "complete lifts {rate:.4} fell below the floor {:.4}",
        floor::AARCH64
    );
    // A lifter that quietly produced nothing would pass every completeness
    // check above, since there would be nothing to be incomplete about. The
    // guard against that is how much p-code an average instruction produces.
    //
    // Some instructions genuinely lift to nothing and should: of the 790 here,
    // 769 are `nop` and the rest are `bti` and the pointer authentication
    // hints, whose bodies in this specification are empty. That is the
    // specification's answer, not a hole in the lifter.
    let density = t.ops as f64 / t.lifted as f64;
    assert!(
        density >= 4.0,
        "{density:.1} operations per instruction is too few to be a real lift"
    );
}

#[test]
fn riscv64_lifts() {
    let Some(spec) = language("RISCV/data/languages/riscv.lp64d.slaspec") else {
        return;
    };
    let (Some(objdump), Some(objects)) = (llvm_objdump(), riscv_objects()) else {
        return;
    };
    let mut t = Tally::default();
    for path in &objects {
        let mut d = Decoder::new(&spec);
        for (addr, bytes) in encodings(&objdump, &["-d", "-M", "no-aliases"], path) {
            let Ok(insn) = d.decode(&bytes, addr) else {
                continue;
            };
            t.add(&pcode::lift(&spec, &insn));
        }
    }
    t.report("RISC-V 64");
    assert!(t.lifted > 500, "the corpus must be worth measuring");
    let rate = t.complete as f64 / t.lifted as f64;
    assert!(
        rate >= floor::RISCV64,
        "complete lifts {rate:.4} fell below the floor {:.4}",
        floor::RISCV64
    );
}

#[test]
fn x86_64_lifts() {
    let (Some(spec), Some(dir)) = (language("x86/data/languages/x86-64.slaspec"), corpus()) else {
        return;
    };
    let Some(objdump) = llvm_objdump() else {
        return;
    };
    let mut t = Tally::default();
    for path in files(&dir, |n| n.contains(".x64.") && n.ends_with(".o")) {
        let mut d = Decoder::new(&spec);
        for (name, value) in [
            ("addrsize", 2u64),
            ("opsize", 1),
            ("rexprefix", 0),
            ("longMode", 1),
        ] {
            d.set_context(name, value);
        }
        for (addr, bytes) in encodings(&objdump, &["-d", "--x86-asm-syntax=intel"], &path) {
            let Ok(insn) = d.decode(&bytes, addr) else {
                continue;
            };
            t.add(&pcode::lift(&spec, &insn));
        }
    }
    t.report("x86-64");
    assert!(t.lifted > 2_000, "the corpus must be worth measuring");
    let rate = t.complete as f64 / t.lifted as f64;
    assert!(
        rate >= floor::X86_64,
        "complete lifts {rate:.4} fell below the floor {:.4}",
        floor::X86_64
    );
}

fn riscv_objects() -> Option<Vec<PathBuf>> {
    if !have("clang") {
        return None;
    }
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/portable");
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join("riscv-pcode");
    std::fs::create_dir_all(&out).ok()?;
    let mut objects = Vec::new();
    for src in files(&src_dir, |n| n.ends_with(".c")) {
        let base = src.file_stem()?.to_string_lossy().to_string();
        for opt in ["O0", "O2"] {
            let obj = out.join(format!("{base}.{opt}.rv64.o"));
            let ok = Command::new("clang")
                .args([
                    "--target=riscv64-linux-gnu",
                    "-march=rv64gc",
                    &format!("-{opt}"),
                    "-ffreestanding",
                    "-c",
                    "-o",
                ])
                .arg(&obj)
                .arg(&src)
                .output()
                .is_ok_and(|o| o.status.success());
            if ok && obj.is_file() {
                objects.push(obj);
            }
        }
    }
    (!objects.is_empty()).then_some(objects)
}

/// Lifting must be a function of the decode, and nothing else.
#[test]
fn lifting_the_same_instruction_twice_gives_the_same_p_code() {
    let Some(spec) = language("RISCV/data/languages/riscv.lp64d.slaspec") else {
        return;
    };
    let mut d = Decoder::new(&spec);
    let insn = d
        .decode(&[0x33, 0x05, 0xb5, 0x00], 0x1000)
        .expect("decodes");
    assert_eq!(pcode::lift(&spec, &insn), pcode::lift(&spec, &insn));
}
