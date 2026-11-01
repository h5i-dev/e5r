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
        ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k(\n\t.param .u64 k_p,\n\t.param .u32 k_n\n)\n{{\n\t.reg .pred %p<3>;\n\t.reg .b32 %r<9>;\n\t.reg .b64 %rd<9>;\nL:\n\t{body};\n\tret;\n}}\n"
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
    v.push("cvta.to.global.u64 %rd1, %rd2".into());
    v.push("cvta.to.global.u64 %rd1, %r2".into());
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
