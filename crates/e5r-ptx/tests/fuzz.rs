//! Deterministic fuzzing of the lexer, parser, round trip and Lean export.
//!
//! Three generators, each with a fixed seed so a failure reproduces:
//!
//! * random token soup from the PTX vocabulary and arbitrary characters,
//!   which must never panic;
//! * well-formed random kernels built from the subset's grammar, which must
//!   be accepted, round-trip, and export to the same Lean text twice;
//! * the well-formed kernels with one token deleted, duplicated or replaced,
//!   which must either be refused with a line number or round-trip.
//!
//! `E5R_FUZZ_CASES` raises the number of cases (default 3000 per generator).

use e5r_ptx::{export_lean, parse_module, roundtrip};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a>(&mut self, v: &[&'a str]) -> &'a str {
        v[self.below(v.len())]
    }
}

fn cases() -> usize {
    std::env::var("E5R_FUZZ_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3000)
}

const VOCAB: &[&str] = &[
    ".version",
    "8.0",
    ".target",
    "sm_86",
    ".address_size",
    "64",
    ".visible",
    ".entry",
    "k",
    "(",
    ")",
    "{",
    "}",
    "[",
    "]",
    "<",
    ">",
    ",",
    ";",
    ":",
    "@",
    "!",
    "+",
    "-",
    ".param",
    ".reg",
    ".u32",
    ".s32",
    ".b32",
    ".u64",
    ".s64",
    ".b64",
    ".pred",
    ".f32",
    "%r1",
    "%rd1",
    "%p1",
    "%tid.x",
    "%laneid",
    "add.u32",
    "ld.global.u32",
    "st.global.u32",
    "bra",
    "L",
    "ret",
    "0x",
    "0",
    "-1",
    "99999999999999999999999999999999999999999",
    "//",
    "/*",
    "*/",
    "\n",
    "é",
    "\0",
    "mov.u32",
    "setp.lt.u32",
    "selp.b32",
    "cvt.u64.u32",
    "mul.wide.s32",
    "%r<4>",
    "1U",
];

#[test]
fn token_soup_never_panics() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..cases() {
        let n = r.below(80);
        let mut s = String::new();
        if r.below(2) == 0 {
            s.push_str(".version 8.0\n.target sm_86\n.address_size 64\n");
        }
        for _ in 0..n {
            s.push_str(r.pick(VOCAB));
            s.push(if r.below(4) == 0 { '\n' } else { ' ' });
        }
        if let Err(e) = roundtrip(&s) {
            assert!(
                e.starts_with("line ") || e.contains(": "),
                "no location: {e}"
            );
        }
    }
}

/// A random kernel in the subset. Registers are declared with the types
/// they are used at, so the parser must accept it.
fn kernel(r: &mut Rng) -> String {
    let t32 = ["u32", "s32"];
    let t64 = ["u64", "s64"];
    let mut body = vec![
        "ld.param.u64 \t%rd1, [k_p];".to_string(),
        "ld.param.u32 \t%r1, [k_n];".to_string(),
    ];
    let reg32 = |r: &mut Rng| format!("%r{}", r.below(8));
    let reg64 = |r: &mut Rng| format!("%rd{}", r.below(8));
    let imm = |r: &mut Rng| {
        ["0", "1", "-1", "4294967295", "0x7fffffff", "-2147483648"][r.below(6)].to_string()
    };
    let n = 1 + r.below(30);
    for _ in 0..n {
        let s = match r.below(16) {
            0 => format!(
                "add.{} \t{}, {}, {}",
                r.pick(&t32),
                reg32(r),
                reg32(r),
                reg32(r)
            ),
            1 => format!(
                "sub.{} \t{}, {}, {}",
                r.pick(&t64),
                reg64(r),
                reg64(r),
                reg64(r)
            ),
            2 => format!(
                "mul.lo.{} \t{}, {}, {}",
                r.pick(&t32),
                reg32(r),
                reg32(r),
                imm(r)
            ),
            3 => format!(
                "mul.wide.{} \t{}, {}, {}",
                r.pick(&t32),
                reg64(r),
                reg32(r),
                reg32(r)
            ),
            4 => format!(
                "mad.lo.{} \t{}, {}, {}, {}",
                r.pick(&t32),
                reg32(r),
                reg32(r),
                reg32(r),
                reg32(r)
            ),
            5 => format!("and.b32 \t{}, {}, {}", reg32(r), reg32(r), imm(r)),
            6 => format!("shl.b64 \t{}, {}, {}", reg64(r), reg64(r), reg32(r)),
            7 => format!(
                "shr.{} \t{}, {}, {}",
                r.pick(&t32),
                reg32(r),
                reg32(r),
                r.below(40)
            ),
            8 => format!(
                "mov.u32 \t{}, %{}.{}",
                reg32(r),
                r.pick(&["tid", "ntid", "ctaid", "nctaid"]),
                r.pick(&["x", "y", "z"])
            ),
            9 => format!(
                "setp.{}.{} \t%p{}, {}, {}",
                r.pick(&["eq", "ne", "lt", "ge"]),
                r.pick(&t32),
                r.below(3),
                reg32(r),
                reg32(r)
            ),
            10 => format!(
                "selp.b64 \t{}, {}, {}, %p{}",
                reg64(r),
                reg64(r),
                imm(r),
                r.below(3)
            ),
            11 => format!(
                "cvt.{}.{} \t{}, {}",
                r.pick(&t64),
                r.pick(&t32),
                reg64(r),
                reg32(r)
            ),
            12 => format!(
                "ld.global.{} \t{}, [{}+{}]",
                r.pick(&t32),
                reg32(r),
                reg64(r),
                4 * r.below(9)
            ),
            13 => format!("st.global.{} \t[{}], {}", r.pick(&t64), reg64(r), reg64(r)),
            14 => format!("@%p{} bra \tL{}", r.below(3), r.below(3)),
            _ => format!("not.b32 \t{}, {}", reg32(r), reg32(r)),
        };
        let g = match r.below(6) {
            0 => format!("@%p{} ", r.below(3)),
            1 => format!("@!%p{} ", r.below(3)),
            _ => String::new(),
        };
        let g = if s.starts_with('@') { String::new() } else { g };
        body.push(format!("{g}{s};"));
    }
    let mut out = String::from(
        ".version 8.0\n.target sm_86\n.address_size 64\n\n.visible .entry k(\n\t.param .u64 k_p,\n\t.param .u32 k_n\n)\n{\n\t.reg .pred \t%p<3>;\n\t.reg .b32 \t%r<8>;\n\t.reg .b64 \t%rd<8>;\n\n",
    );
    let mut labels: Vec<usize> = (0..3).map(|_| r.below(body.len() + 1)).collect();
    labels.sort();
    for (i, s) in body.iter().enumerate() {
        for (l, _) in labels.iter().enumerate().filter(|(_, at)| **at == i) {
            out.push_str(&format!("L{l}:\n"));
        }
        out.push('\t');
        out.push_str(s);
        out.push('\n');
    }
    for (l, _) in labels
        .iter()
        .enumerate()
        .filter(|(_, at)| **at == body.len())
    {
        out.push_str(&format!("L{l}:\n"));
    }
    out.push_str("\tret;\n}\n");
    out
}

#[test]
fn grammar_kernels_round_trip_and_export_deterministically() {
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    for _ in 0..cases() {
        let src = kernel(&mut r);
        let m = roundtrip(&src).unwrap_or_else(|e| panic!("{e}\n{src}"));
        assert_eq!(m, parse_module(&e5r_ptx::print::module(&m)).unwrap());
        let a = export_lean(&src, "T", "h").unwrap();
        let b = export_lean(&src, "T", "h").unwrap();
        assert_eq!(a, b);
    }
}

#[test]
fn mutated_kernels_are_refused_with_a_line_or_round_trip() {
    let mut r = Rng(0x0123_4567_89ab_cdef);
    let (mut refused, mut accepted) = (0, 0);
    for _ in 0..cases() {
        let src = kernel(&mut r);
        let mut toks: Vec<String> = src
            .split_inclusive([' ', '\t', '\n', ',', ';', '[', ']'])
            .map(str::to_string)
            .collect();
        let i = r.below(toks.len());
        match r.below(3) {
            0 => {
                toks.remove(i);
            }
            1 => {
                let t = toks[i].clone();
                toks.insert(i, t);
            }
            _ => toks[i] = format!("{} ", r.pick(VOCAB)),
        }
        let s: String = toks.concat();
        match roundtrip(&s) {
            Ok(_) => accepted += 1,
            Err(e) => {
                assert!(
                    e.starts_with("line ") || e.starts_with("k: ") || e.starts_with("round trip"),
                    "{e}"
                );
                assert!(
                    !e.starts_with("round trip"),
                    "parser and printer disagree: {e}\n{s}"
                );
                refused += 1;
            }
        }
    }
    assert!(
        refused > 0 && accepted > 0,
        "{refused} refused, {accepted} accepted"
    );
}
