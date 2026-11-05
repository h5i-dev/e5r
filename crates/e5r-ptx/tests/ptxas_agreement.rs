//! The parser accepts only PTX that ptxas accepts.
//!
//! Every instruction form the subset could be asked about (each opcode with
//! each type, register and immediate operands, special registers, guards,
//! offsets) is put in a one-instruction kernel. If the parser accepts it,
//! ptxas must assemble it: a proof about text no assembler accepts would be a
//! proof about nothing. The converse is not required (the subset is
//! smaller than PTX), but the forms the parser refuses that ptxas accepts are
//! counted so the test also fails if the parser stops accepting the subset.
//!
//! ptxas is the oracle. Without it (CI has no CUDA) the test returns early.

use e5r_ptx::parse_module;
use std::process::Command;

fn ptxas() -> Option<String> {
    let p = std::env::var("PTXAS").unwrap_or_else(|_| "/usr/local/cuda/bin/ptxas".into());
    Command::new(&p).arg("--version").output().ok()?;
    Some(p)
}

fn kernel(body: &str) -> String {
    format!(
        ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k(\n\t.param .u64 k_p,\n\t.param .u32 k_n\n)\n{{\n\t.reg .pred %p<3>;\n\t.reg .b32 %r<9>;\n\t.reg .b64 %rd<9>;\n\t.reg .f32 %f<9>;\n\t.reg .f64 %fd<9>;\n\t.shared .align 8 .b8 sm[64];\nL:\n\t{body};\n\tret;\n}}\n"
    )
}

const TYS: [&str; 6] = ["u32", "s32", "b32", "u64", "s64", "b64"];

fn reg(t: &str, i: u32) -> String {
    if t.ends_with("32") {
        format!("%r{i}")
    } else {
        format!("%rd{i}")
    }
}

fn forms() -> Vec<String> {
    let mut v = Vec::new();
    let imms = [
        "0",
        "-1",
        "4294967295",
        "0x7fffffff",
        "4294967296",
        "-2147483649",
    ];
    v.push("bfi.b32 %r1, %r2, %r3, 14, 4".into());
    v.push("bfi.b32 %r1, %r2, %r3, 32, 0".into());
    v.push("bfi.b32 %r1, %r2, %r3, 0, 32".into());
    for t in TYS {
        let (d, a, b, c) = (reg(t, 1), reg(t, 2), reg(t, 3), reg(t, 4));
        for op in ["add", "sub", "mul.lo", "and", "or", "xor"] {
            v.push(format!("{op}.{t} {d}, {a}, {b}"));
            for i in imms {
                v.push(format!("{op}.{t} {d}, {a}, {i}"));
            }
            v.push(format!("{op}.{t} {d}, %tid.x, {b}"));
        }
        for op in ["shl", "shr"] {
            v.push(format!("{op}.{t} {d}, {a}, %r3"));
            v.push(format!("{op}.{t} {d}, {a}, {b}"));
            for i in ["0", "31", "40", "64", "-1", "4294967296"] {
                v.push(format!("{op}.{t} {d}, {a}, {i}"));
            }
        }
        v.push(format!("mad.lo.{t} {d}, {a}, {b}, {c}"));
        v.push(format!("mad.lo.{t} {d}, {a}, 3, {c}"));
        v.push(format!("not.{t} {d}, {a}"));
        v.push(format!("mov.{t} {d}, {a}"));
        for i in imms {
            v.push(format!("mov.{t} {d}, {i}"));
        }
        for s in ["%tid.x", "%ntid.y", "%ctaid.z", "%nctaid.x"] {
            v.push(format!("mov.{t} {d}, {s}"));
        }
        v.push(format!("selp.{t} {d}, {a}, {b}, %p1"));
        v.push(format!("selp.{t} {d}, 1, 0, %p1"));
        for c in ["eq", "ne", "lt", "le", "gt", "ge", "lo", "ls", "hi", "hs"] {
            v.push(format!("setp.{c}.{t} %p1, {a}, {b}"));
            v.push(format!("setp.{c}.{t} %p1, {a}, 5"));
        }
        for s in TYS {
            v.push(format!("cvt.{t}.{s} {d}, {}", reg(s, 2)));
            v.push(format!("cvt.{t}.{s} {d}, %tid.x"));
        }
        for sp in ["global", "param"] {
            v.push(format!("ld.{sp}.{t} {d}, [%rd5]"));
            v.push(format!("ld.{sp}.{t} {d}, [k_p]"));
            v.push(format!("ld.{sp}.{t} {d}, [k_n]"));
            v.push(format!("st.{sp}.{t} [%rd5], {a}"));
        }
        for off in [
            "+0",
            "+4",
            "+-4",
            "+0x7fffffff",
            "+0x80000000",
            "+-0x80000000",
            "+-0x80000001",
        ] {
            v.push(format!("ld.global.{t} {d}, [%rd5{off}]"));
            v.push(format!("st.global.{t} [%rd5{off}], {a}"));
        }
        v.push(format!("st.global.{t} [%rd5], 7"));
    }
    for t in ["u32", "s32", "b32", "u64"] {
        v.push(format!("mul.wide.{t} %rd1, %r2, %r3"));
        v.push(format!("mul.wide.{t} %rd1, %r2, 4"));
        v.push(format!("mul.wide.{t} %rd1, %r2, -1"));
    }
    // M4: shared memory, atomics, barriers
    for t in TYS {
        let (d, a, b) = (reg(t, 1), reg(t, 2), reg(t, 3));
        for addr in ["[%r5]", "[%rd5]", "[sm]", "[sm+8]", "[%r5+-4]"] {
            v.push(format!("ld.shared.{t} {d}, {addr}"));
            v.push(format!("st.shared.{t} {addr}, {a}"));
        }
        v.push(format!("st.shared.{t} [sm], 3"));
        for sp in ["global", "shared"] {
            let addr = if sp == "global" { "[%rd5]" } else { "[%r5]" };
            for op in ["add", "min", "max", "exch", "and", "or", "xor", "inc"] {
                v.push(format!("atom.{sp}.{op}.{t} {d}, {addr}, {b}"));
                v.push(format!("atom.{sp}.{op}.{t} {d}, {addr}, 1"));
                v.push(format!("red.{sp}.{op}.{t} {addr}, {b}"));
            }
            v.push(format!("atom.{sp}.cas.{t} {d}, {addr}, {a}, {b}"));
            v.push(format!("atom.{sp}.cas.{t} {d}, {addr}, 0, 1"));
        }
        v.push(format!("atom.add.{t} {d}, [%rd5], {b}"));
        v.push(format!("atom.global.add.{t} {d}, [%rd5+4], {b}"));
    }
    for t in ["u32", "b32", "u64", "b64", "s32", "s64"] {
        v.push(format!("mov.{t} {}, sm", reg(t, 1)));
    }
    v.push("add.u32 %r1, sm, 4".into());
    v.push("ld.global.u32 %r1, [sm]".into());
    for b in [
        "bar.sync 0",
        "bar.sync 1",
        "bar.sync 0, 32",
        "barrier.sync 0",
        "bar.cta.sync 0",
    ] {
        v.push(b.into());
    }
    v.push("@%p1 bar.sync 0".into());
    v.push("cvta.to.global.u64 %rd1, %rd2".into());
    v.push("cvta.to.global.u64 %rd1, %r2".into());
    // floating point: every modifier combination, orders, literals, and
    // register kinds the type rules allow or refuse
    for t in ["f32", "f64"] {
        let r = |i: u32| {
            if t == "f32" {
                format!("%f{i}")
            } else {
                format!("%fd{i}")
            }
        };
        let (d, a, b, c) = (r(1), r(2), r(3), r(4));
        let lit = if t == "f32" {
            "0f3F800000"
        } else {
            "0d3FF0000000000000"
        };
        let mods = [
            "",
            ".rn",
            ".rz",
            ".rm",
            ".rp",
            ".rn.ftz",
            ".rn.sat",
            ".rn.ftz.sat",
            ".ftz.rn",
            ".sat.ftz",
            ".ftz",
            ".approx",
            ".full",
            ".approx.ftz",
            ".rni",
        ];
        for m in mods {
            for op in ["add", "sub", "mul", "div"] {
                v.push(format!("{op}{m}.{t} {d}, {a}, {b}"));
            }
            v.push(format!("fma{m}.{t} {d}, {a}, {b}, {c}"));
            for op in ["sqrt", "rcp", "neg", "abs"] {
                v.push(format!("{op}{m}.{t} {d}, {a}"));
            }
        }
        for m in ["", ".ftz", ".NaN", ".ftz.NaN", ".NaN.ftz", ".xorsign.abs"] {
            v.push(format!("min{m}.{t} {d}, {a}, {b}"));
            v.push(format!("max{m}.{t} {d}, {a}, {b}"));
        }
        for cmp in [
            "eq", "ne", "lt", "le", "gt", "ge", "equ", "neu", "ltu", "leu", "gtu", "geu", "num",
            "nan", "lo", "hs",
        ] {
            v.push(format!("setp.{cmp}.{t} %p1, {a}, {b}"));
            v.push(format!("setp.{cmp}.ftz.{t} %p1, {a}, {b}"));
            v.push(format!("setp.{cmp}.{t} %p1, {a}, {lit}"));
        }
        v.push(format!("add.rn.{t} {d}, {a}, {lit}"));
        v.push(format!("add.rn.{t} {d}, {a}, 1"));
        v.push(format!("add.rn.{t} {d}, {a}, 0f3F800000"));
        v.push(format!("add.rn.{t} {d}, {a}, 0d3FF0000000000000"));
        v.push(format!("mov.{t} {d}, {a}"));
        v.push(format!("mov.{t} {d}, {lit}"));
        v.push(format!("selp.{t} {d}, {a}, {b}, %p1"));
        v.push(format!("ld.global.{t} {d}, [%rd5]"));
        v.push(format!("st.global.{t} [%rd5], {a}"));
        v.push(format!("st.global.{t} [%rd5], {lit}"));
        let (bt, ir) = if t == "f32" {
            ("b32", "%r2")
        } else {
            ("b64", "%rd2")
        };
        v.push(format!("mov.{bt} {d}, {ir}"));
        v.push(format!("mov.{bt} {ir}, {a}"));
        v.push(format!("add.u{} {ir}, {a}, {ir}", &bt[1..]));
        v.push(format!("add.rn.{t} {d}, {ir}, {a}"));
        for it in TYS {
            let ireg = reg(it, 2);
            for m in [
                "", ".rn", ".rz", ".rm", ".rp", ".rni", ".rzi", ".rn.ftz", ".rn.sat", ".rmi.ftz",
                ".rpi.sat",
            ] {
                v.push(format!("cvt{m}.{t}.{it} {d}, {ireg}"));
                v.push(format!("cvt{m}.{it}.{t} {}, {a}", reg(it, 1)));
            }
        }
        for m in [
            "", ".rni", ".rzi", ".rmi", ".rpi", ".rn", ".rni.ftz", ".rzi.sat", ".ftz",
        ] {
            v.push(format!("cvt{m}.{t}.{t} {d}, {a}"));
        }
    }
    for m in ["", ".ftz", ".sat", ".ftz.sat", ".rn", ".rz"] {
        v.push(format!("cvt{m}.f64.f32 %fd1, %f2"));
    }
    for m in [
        "",
        ".rn",
        ".rz",
        ".rm",
        ".rp",
        ".rn.ftz",
        ".rz.sat",
        ".rp.ftz.sat",
        ".rni",
    ] {
        v.push(format!("cvt{m}.f32.f64 %f1, %fd2"));
    }
    for g in ["", "@%p1 ", "@!%p1 "] {
        v.push(format!("{g}bra L"));
        v.push(format!("{g}bra.uni L"));
        v.push(format!("{g}mov.u32 %r1, %r2"));
        v.push(format!("{g}ret"));
        v.push(format!("{g}exit"));
    }
    v
}

#[test]
fn parser_acceptance_implies_ptxas_acceptance() {
    let Some(ptxas) = ptxas() else {
        eprintln!("ptxas not installed: skipped");
        return;
    };
    let dir = std::env::temp_dir().join(format!("e5r-ptxas-agree-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (mut accepted, mut gaps, mut wrong) = (0, 0, Vec::new());
    for (i, f) in forms().iter().enumerate() {
        let src = kernel(f);
        let ours = parse_module(&src).is_ok();
        let path = dir.join(format!("f{i}.ptx"));
        std::fs::write(&path, &src).unwrap();
        let theirs = Command::new(&ptxas)
            .args(["-arch=sm_86", "-o"])
            .arg(dir.join("f.cubin"))
            .arg(&path)
            .output()
            .unwrap()
            .status
            .success();
        match (ours, theirs) {
            (true, true) => accepted += 1,
            (true, false) => wrong.push(f.clone()),
            (false, true) => gaps += 1,
            (false, false) => {}
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "accepted by the parser, refused by ptxas: {wrong:#?}"
    );
    eprintln!("{accepted} forms accepted by both, {gaps} accepted only by ptxas");
    // The subset itself: if this drops, the parser lost forms it used to take.
    assert!(accepted >= 300, "only {accepted} forms accepted");
}
