//! Shared by the oracle tests: tool lookup and the random program generator.
#![allow(dead_code)]

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn tool(var: &str, names: &[&str]) -> Option<String> {
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

pub struct Rng(u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    pub fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len() as u64) as usize]
    }
}

pub const REGS: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];
/// s11 holds the scratch buffer's address and is never a destination.
pub const BASE: usize = 27;

pub fn rd(r: &mut Rng) -> &'static str {
    loop {
        let i = r.below(32) as usize;
        if i != BASE {
            return REGS[i];
        }
    }
}
pub fn rs(r: &mut Rng) -> &'static str {
    REGS[r.below(32) as usize]
}

pub fn value(r: &mut Rng) -> i64 {
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

pub fn instr(r: &mut Rng, label: &mut usize) -> String {
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

/// A random straight-line program over the whole profile. `end` is appended
/// after every register has been stored to `buf + 256`.
pub fn program(seed: u64, end: &str, data_extra: &str) -> String {
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
    s.push_str(end);
    s.push_str(".data\n.balign 8\n");
    s.push_str(data_extra);
    s.push_str("buf:\n");
    for _ in 0..32 {
        writeln!(s, "  .dword {:#x}", r.next()).unwrap();
    }
    s.push_str("  .zero 256\n");
    s.push_str("buf_end:\n");
    s
}

pub fn lean_bytes(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(|x| x.to_string()).collect();
    format!("ByteArray.mk #[{}]", v.join(", "))
}

pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}
