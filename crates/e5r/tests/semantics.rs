//! The Lean semantics against the processor (CONTRIBUTING.md: an external
//! oracle wherever one exists).
//!
//! Random straight-line programs over every instruction of the profile, with
//! interesting operands (0, -1, 1, the extremes, random), are assembled with
//! clang, linked with ld.lld and run under qemu-riscv64. The same ELF is run
//! by the executable Lean semantics (`E5R.runToEcall`, the `exec` every proof
//! is about). Both dump 512 bytes: a scratch area the program loaded from and
//! stored to, and every register. They must be identical.
//!
//! The same Lean run checks `E5R.decode` against this crate's decoder on a
//! sample of the corpus `tests/decode.rs` checks against llvm-mc.
//!
//! Needs clang, ld.lld, qemu-riscv64 and lake (CLANG, LLD, QEMU_RISCV64,
//! LAKE override them); skips, loudly, when one is missing. E5R_SEM_PROGRAMS
//! sets the number of programs (default 48).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

fn tool(var: &str, names: &[&str]) -> Option<String> {
    let cands: Vec<String> = match std::env::var(var) {
        Ok(v) => vec![v],
        Err(_) => names.iter().map(|s| s.to_string()).collect(),
    };
    cands.into_iter().find(|c| {
        Command::new(c)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    })
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len() as u64) as usize]
    }
}

const REGS: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];
/// s11 holds the scratch buffer's address and is never a destination.
const BASE: usize = 27;

fn rd(r: &mut Rng) -> &'static str {
    loop {
        let i = r.below(32) as usize;
        if i != BASE {
            return REGS[i];
        }
    }
}
fn rs(r: &mut Rng) -> &'static str {
    REGS[r.below(32) as usize]
}

fn value(r: &mut Rng) -> i64 {
    match r.below(10) {
        0 => 0,
        1 => -1,
        2 => 1,
        3 => i64::MIN,
        4 => i64::MAX,
        5 => i32::MIN as i64,
        6 => 0x8000_0000,
        7 => r.below(64) as i64,
        _ => r.next() as i64,
    }
}

fn instr(r: &mut Rng, label: &mut usize) -> String {
    const R: &[&str] = &[
        "add",
        "sub",
        "sll",
        "slt",
        "sltu",
        "xor",
        "srl",
        "sra",
        "or",
        "and",
        "mul",
        "mulh",
        "mulhsu",
        "mulhu",
        "div",
        "divu",
        "rem",
        "remu",
        "sh1add",
        "sh2add",
        "sh3add",
        "andn",
        "orn",
        "xnor",
        "max",
        "maxu",
        "min",
        "minu",
        "rol",
        "ror",
        "addw",
        "subw",
        "sllw",
        "srlw",
        "sraw",
        "mulw",
        "divw",
        "divuw",
        "remw",
        "remuw",
        "add.uw",
        "sh1add.uw",
        "sh2add.uw",
        "sh3add.uw",
        "rolw",
        "rorw",
    ];
    const I: &[&str] = &["addi", "slti", "sltiu", "xori", "ori", "andi", "addiw"];
    const SH: &[&str] = &["slli", "srli", "srai", "rori", "slli.uw"];
    const SHW: &[&str] = &["slliw", "srliw", "sraiw", "roriw"];
    const U: &[&str] = &[
        "clz", "ctz", "cpop", "clzw", "ctzw", "cpopw", "sext.b", "sext.h", "zext.h", "rev8",
        "orc.b",
    ];
    const LD: &[(&str, u64)] = &[
        ("lb", 1),
        ("lh", 2),
        ("lw", 4),
        ("ld", 8),
        ("lbu", 1),
        ("lhu", 2),
        ("lwu", 4),
    ];
    const ST: &[(&str, u64)] = &[("sb", 1), ("sh", 2), ("sw", 4), ("sd", 8)];
    const BR: &[&str] = &["beq", "bne", "blt", "bge", "bltu", "bgeu"];
    match r.below(20) {
        0..=6 => format!("{} {}, {}, {}", r.pick(R), rd(r), rs(r), rs(r)),
        7 | 8 => format!(
            "{} {}, {}, {}",
            r.pick(I),
            rd(r),
            rs(r),
            r.below(4096) as i64 - 2048
        ),
        9 => format!("{} {}, {}, {}", r.pick(SH), rd(r), rs(r), r.below(64)),
        10 => format!("{} {}, {}, {}", r.pick(SHW), rd(r), rs(r), r.below(32)),
        11 => format!("{} {}, {}", r.pick(U), rd(r), rs(r)),
        12 => format!("lui {}, {}", rd(r), r.below(1 << 20)),
        13 => format!("auipc {}, {}", rd(r), r.below(1 << 20)),
        14 | 15 => {
            let (op, w) = LD[r.below(LD.len() as u64) as usize];
            format!("{op} {}, {}(s11)", rd(r), w * r.below(256 / w))
        }
        16 | 17 => {
            let (op, w) = ST[r.below(ST.len() as u64) as usize];
            format!("{op} {}, {}(s11)", rs(r), w * r.below(256 / w))
        }
        18 => {
            *label += 1;
            let skipped = format!("addi {}, {}, {}", rd(r), rs(r), r.below(100));
            format!(
                "{} {}, {}, .L{label}\n  {skipped}\n.L{label}:",
                r.pick(BR),
                rs(r),
                rs(r)
            )
        }
        _ => {
            *label += 1;
            let skipped = format!("addi {}, {}, 1", rd(r), rs(r));
            format!("jal {}, .L{label}\n  {skipped}\n.L{label}:", rd(r))
        }
    }
}

fn program(seed: u64) -> String {
    let mut r = Rng(seed.wrapping_mul(0x9e3779b97f4a7c15) | 1);
    let mut s = String::from(".text\n.globl _start\n_start:\n  lla s11, buf\n");
    for (i, name) in REGS.iter().enumerate().skip(1) {
        if i != BASE {
            writeln!(s, "  li {name}, {}", value(&mut r)).unwrap();
        }
    }
    let mut label = 0;
    for _ in 0..80 {
        writeln!(s, "  {}", instr(&mut r, &mut label)).unwrap();
    }
    for (i, name) in REGS.iter().enumerate() {
        writeln!(s, "  sd {name}, {}(s11)", 256 + 8 * i).unwrap();
    }
    s.push_str("  li a7, 64\n  li a0, 1\n  mv a1, s11\n  li a2, 512\n  ecall\n");
    s.push_str("  li a7, 93\n  li a0, 0\n  ecall\n");
    s.push_str(".data\n.balign 8\nbuf:\n");
    for _ in 0..32 {
        writeln!(s, "  .dword {:#x}", r.next()).unwrap();
    }
    s.push_str("  .zero 256\n");
    s
}

fn lean_bytes(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(|x| x.to_string()).collect();
    format!("ByteArray.mk #[{}]", v.join(", "))
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn lean_semantics_agree_with_qemu() {
    let clang = tool("CLANG", &["clang"]);
    let lld = tool("LLD", &["ld.lld", "ld.lld-20", "ld.lld-19", "ld.lld-18"]);
    let qemu = tool("QEMU_RISCV64", &["qemu-riscv64", "qemu-riscv64-static"]);
    let lake = tool("LAKE", &["lake"]);
    let (Some(clang), Some(lld), Some(qemu), Some(lake)) = (clang, lld, qemu, lake) else {
        eprintln!(
            "SKIPPED lean_semantics_agree_with_qemu: needs clang, ld.lld, qemu-riscv64 and lake"
        );
        return;
    };
    let n: u64 = std::env::var("E5R_SEM_PROGRAMS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(48);
    let dir = std::env::temp_dir().join(format!("e5r-semantics-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut lean = String::from("import E5R\nopen E5R\n\n");
    let mut want = Vec::new();
    for p in 0..n {
        let asm = dir.join(format!("p{p}.S"));
        let obj = dir.join(format!("p{p}.o"));
        let elf = dir.join(format!("p{p}.elf"));
        std::fs::write(&asm, program(p)).unwrap();
        let ok = Command::new(&clang)
            .args([
                "--target=riscv64-unknown-elf",
                "-march=rv64im_zba_zbb",
                "-mabi=lp64",
                "-mno-relax",
                "-c",
            ])
            .arg(&asm)
            .arg("-o")
            .arg(&obj)
            .status()
            .unwrap()
            .success();
        assert!(ok, "clang failed on {}", asm.display());
        let ok = Command::new(&lld)
            .args(["-static", "-e", "_start"])
            .arg(&obj)
            .arg("-o")
            .arg(&elf)
            .status()
            .unwrap()
            .success();
        assert!(ok, "ld.lld failed on {}", obj.display());
        let out = Command::new(&qemu).arg(&elf).output().unwrap();
        assert!(out.status.success(), "qemu failed on {}", elf.display());
        assert_eq!(
            out.stdout.len(),
            512,
            "program {p} wrote {} bytes",
            out.stdout.len()
        );
        want.push(
            out.stdout
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>(),
        );

        let bytes = std::fs::read(&elf).unwrap();
        let bin = e5r::load(&bytes).expect("generated programs are RV64 without C");
        let e = e5r::elf::Elf::parse(&bytes).unwrap();
        let data = e.section(".data").expect(".data");
        let words: Vec<String> = bin.text.iter().map(|w| format!("0x{w:08x}#32")).collect();
        writeln!(
            lean,
            "def code{p} : Code := ⟨0x{:x}#64, #[{}]⟩",
            bin.text_addr,
            words.join(", ")
        )
        .unwrap();
        writeln!(
            lean,
            "def mem{p} : Word → Byte := memOf 0x{:x}#64 ({})",
            data.addr,
            lean_bytes(e.bytes(data))
        )
        .unwrap();
        writeln!(
            lean,
            "#eval IO.println (match runToEcall code{p} 100000 {{ regs := fun _ => 0, pc := 0x{:x}#64, mem := mem{p}, trace := [], exit := none }} with\n  | some s => s!\"P{p} \" ++ hexBytes (readBytes s.mem (s.reg 27) 512)\n  | none => \"P{p} FAULT\")\n",
            e.entry
        )
        .unwrap();
    }
    // Decoder cross-check: about 300 words per major opcode, spread over the
    // other 25 bits, in chunks small enough to elaborate quickly.
    let mut cases = Vec::new();
    for opc in [
        0x13u32, 0x1b, 0x03, 0x23, 0x33, 0x3b, 0x63, 0x67, 0x73, 0x37, 0x17, 0x6f,
    ] {
        for x in (0..(1u32 << 25)).step_by(111_863) {
            let w = opc | x << 7;
            cases.push(match e5r::isa::decode(w) {
                Some(i) => format!("(0x{w:08x}#32, some ({}))", i.lean()),
                None => format!("(0x{w:08x}#32, none)"),
            });
        }
    }
    let chunks: Vec<&[String]> = cases.chunks(64).collect();
    for (k, c) in chunks.iter().enumerate() {
        writeln!(
            lean,
            "def dcases{k} : List (BitVec 32 × Option Instr) := [\n  {}]",
            c.join(",\n  ")
        )
        .unwrap();
    }
    let all: Vec<String> = (0..chunks.len()).map(|k| format!("dcases{k}")).collect();
    writeln!(
        lean,
        "def dcases : List (BitVec 32 × Option Instr) := {}",
        all.join(" ++ ")
    )
    .unwrap();
    writeln!(lean, "#eval IO.println s!\"DECODE {{(dcases.filter fun (w, e) => decode w != e).length}} of {{dcases.length}}\"").unwrap();
    let file = dir.join("Semantics.lean");
    std::fs::write(&file, &lean).unwrap();
    let out = Command::new(&lake)
        .args(["env", "lean"])
        .arg(&file)
        .current_dir(root().join("lean"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "lean failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let mut bad = Vec::new();
    for (p, w) in want.iter().enumerate() {
        let got = stdout
            .lines()
            .find_map(|l| l.strip_prefix(&format!("P{p} ")))
            .unwrap_or("missing");
        if got != w {
            bad.push(format!(
                "program {p} ({}): lean {}, qemu {}",
                dir.join(format!("p{p}.S")).display(),
                &got[..got.len().min(80)],
                &w[..80]
            ));
        }
    }
    let decode_line = stdout
        .lines()
        .find(|l| l.starts_with("DECODE"))
        .unwrap_or("DECODE missing");
    eprintln!("{n} programs compared; {decode_line}");
    assert!(
        decode_line.starts_with("DECODE 0 of"),
        "the Lean and Rust decoders disagree: {decode_line}"
    );
    assert!(
        bad.is_empty(),
        "{} programs differ:\n{}",
        bad.len(),
        bad.join("\n")
    );
    let _ = std::fs::remove_dir_all(&dir);
}
