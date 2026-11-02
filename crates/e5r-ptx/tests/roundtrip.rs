//! The benchmarks round-trip, the subset's edges are refused with a reason,
//! and no prefix or byte flip of a benchmark makes the parser panic.

use e5r_ptx::{parse_module, roundtrip};
use std::path::PathBuf;

fn benchmarks() -> Vec<(PathBuf, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../verification/ptx/benchmarks");
    let mut out = Vec::new();
    for dir in ["correct", "buggy"] {
        let mut files: Vec<_> = std::fs::read_dir(root.join(dir))
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "ptx"))
            .collect();
        files.sort();
        for f in files {
            let text = std::fs::read_to_string(&f).unwrap();
            out.push((f, text));
        }
    }
    assert!(out.len() >= 6, "benchmarks missing");
    out
}

#[test]
fn every_benchmark_round_trips() {
    for (f, src) in benchmarks() {
        let m = roundtrip(&src).unwrap_or_else(|e| panic!("{}: {e}", f.display()));
        assert_eq!(m.kernels.len(), 1, "{}", f.display());
    }
}

#[test]
fn lean_export_names_every_statement() {
    for (f, src) in benchmarks() {
        let m = parse_module(&src).unwrap();
        let lean = e5r_ptx::export_lean(&src, "Ptx.Kernels.T", "test").unwrap();
        let n = m.kernels[0].body.len();
        assert!(
            lean.contains(&format!("/- {} -/", n - 1)),
            "{}",
            f.display()
        );
        assert!(!lean.contains(&format!("/- {n} -/")), "{}", f.display());
    }
}

const HEAD: &str = ".version 8.0\n.target sm_80\n.address_size 64\n";

fn kernel(body: &str) -> String {
    format!(
        "{HEAD}.visible .entry k(\n\t.param .u64 k_p\n)\n{{\n\t.reg .pred %p<2>;\n\t.reg .b32 %r<4>;\n\t.reg .b64 %rd<4>;\n{body}\n}}\n"
    )
}

fn refused(body: &str, why: &str) {
    match parse_module(&kernel(body)) {
        Ok(_) => panic!("accepted: {body}"),
        Err(e) => assert!(e.contains(why), "{body}: {e} (wanted {why})"),
    }
}

#[test]
fn subset_edges_are_refused() {
    refused("\tadd.f32 %r1, %r2, %r3;\n\tret;", "no rounding modifier");
    refused("\tadd.rn.f32 %r1, %r2, %r3;\n\tret;", "used at .f32");
    refused("\tdiv.approx.f32 %r1, %r2, %r3;\n\tret;", "approximate instructions");
    refused("\tsin.approx.f32 %r1, %r2;\n\tret;", "unsupported instruction");
    refused("\tadd.rn.f16 %r1, %r2, %r3;\n\tret;", "unsupported instruction");
    refused("\tadd.ftz.rn.f32 %r1, %r2, %r3;\n\tret;", "out of order");
    refused("\tld.local.u32 %r1, [%rd1];\n\tret;", "unsupported ld");
    refused(
        "\tld.shared.u32 %r1, [nosuch];\n\tret;",
        "nosuch is not a .shared variable",
    );
    refused("\tmov.u32 %r1, nosuch;\n\tret;", "nosuch is not a .shared variable");
    refused(
        "\tatom.global.inc.u32 %r1, [%rd1], 1;\n\tret;",
        "unsupported instruction",
    );
    refused(
        "\tatom.add.u32 %r1, [%rd1], 1;\n\tret;",
        "unsupported instruction",
    );
    refused(
        "\tatom.relaxed.gpu.global.add.u32 %r1, [%rd1], 1;\n\tret;",
        "unsupported instruction",
    );
    refused(
        "\tatom.global.add.u32 %r1, [%r2], 1;\n\tret;",
        "not a 64-bit register",
    );
    refused(
        "\tatom.global.and.u32 %r1, [%rd1], 1;\n\tret;",
        "not a PTX instruction type",
    );
    refused(
        "\tred.global.exch.b32 [%rd1], 1;\n\tret;",
        "unsupported instruction",
    );
    refused("\tbar.sync 1;\n\tret;", "only bar.sync 0");
    refused("\tbar.sync 0, 64;\n\tret;", "thread count");
    refused("\t@%p1 bar.sync 0;\n\tret;", "predicated bar.sync");
    refused("\tbarrier.sync 0;\n\tret;", "unsupported instruction");
    refused("\tbar.arrive 0, 64;\n\tret;", "unsupported instruction");
    refused(
        "\tadd.u32 %r1, %r1, nosuch;\n\tret;",
        "variable nosuch outside mov",
    );
    refused(
        "\tadd.u32 %r1, %r9, %r2;\n\tret;",
        "undeclared register %r9",
    );
    refused("\tadd.u64 %r1, %r2, %r3;\n\tret;", "not a 64-bit register");
    refused(
        "\tmov.u32 %r1, %laneid;\n\tret;",
        "undeclared register %laneid",
    );
    refused(
        "\tmov.u64 %rd1, %tid.x;\n\tret;",
        "special registers are 32-bit",
    );
    refused(
        "\tsetp.lt.b32 %p1, %r1, %r2;\n\tret;",
        "not a PTX instruction type",
    );
    refused(
        "\tsetp.lo.s32 %p1, %r1, %r2;\n\tret;",
        "not a PTX instruction type",
    );
    refused(
        "\tand.u32 %r1, %r1, %r2;\n\tret;",
        "not a PTX instruction type",
    );
    refused(
        "\tadd.b32 %r1, %r1, %r2;\n\tret;",
        "not a PTX instruction type",
    );
    refused(
        "\tcvt.u64.b32 %rd1, %r2;\n\tret;",
        "not a PTX instruction type",
    );
    refused("\tadd.u32 %r1, %tid.x, 1;\n\tret;", "outside mov/cvt");
    refused(
        "\tadd.u32 %r1, %r2, 0x1FFFFFFFF;\n\tret;",
        "does not fit 32 bits",
    );
    refused(
        "\tshl.b64 %rd1, %rd2, 4294967296;\n\tret;",
        "does not fit 32 bits",
    );
    refused(
        "\tadd.s64 %rd1, %rd2, 18446744073709551616;\n\tret;",
        "does not fit 64 bits",
    );
    refused(
        "\tld.global.u32 %r1, [%rd1+0x80000000];\n\tret;",
        "does not fit 32 signed bits",
    );
    refused("L:\n\t@%p1 bra.uni L;\n\tret;", "predicated bra.uni");
    refused(
        "\tsetp.eq.u32 %r1, %r1, %r2;\n\tret;",
        "not a .pred register",
    );
    refused("\tbra $L_nowhere;\n\tret;", "undefined label");
    refused(
        "\tld.param.u32 %r1, [k_p];\n\tret;",
        "ld.param.u32 of parameter k_p",
    );
    refused(
        "\tld.global.u32 %r1, [%r2];\n\tret;",
        "not a 64-bit register",
    );
    refused(
        "\tst.param.u32 [k_p], %r1;\n\tret;",
        "unsupported instruction",
    );
}

fn kernel_sh(decls: &str, body: &str) -> String {
    format!(
        "{HEAD}.visible .entry k(\n\t.param .u64 k_p\n)\n{{\n\t.reg .pred %p<2>;\n\t.reg .b32 %r<4>;\n\t.reg .b64 %rd<4>;\n{decls}\n{body}\n}}\n"
    )
}

#[test]
fn shared_declarations() {
    let ok = |d: &str, b: &str| {
        roundtrip(&kernel_sh(d, b)).unwrap_or_else(|e| panic!("{d} {b}: {e}"));
    };
    let bad = |d: &str, b: &str, why: &str| match parse_module(&kernel_sh(d, b)) {
        Ok(_) => panic!("accepted: {d} {b}"),
        Err(e) => assert!(e.contains(why), "{d} {b}: {e} (wanted {why})"),
    };
    ok(
        "\t.shared .align 4 .b8 s[4096];",
        "\tmov.u32 %r1, s;\n\tld.shared.u32 %r2, [%r1+4];\n\tst.shared.u32 [s+8], %r2;\n\tbar.sync 0;\n\tret;",
    );
    ok(
        "\t.shared .u32 t[16];\n\t.shared .u64 c;",
        "\tmov.u64 %rd1, c;\n\tatom.shared.add.u64 %rd2, [%rd1], 1;\n\tred.shared.max.s32 [t], %r1;\n\tatom.shared.cas.b32 %r1, [t+4], 0, 1;\n\tret;",
    );
    let m = roundtrip(&kernel_sh("\t.shared .align 8 .b8 s[12];\n\t.shared .u16 h[3];", "\tret;")).unwrap();
    assert_eq!(m.kernels[0].shared[0].size(), 12);
    assert_eq!(m.kernels[0].shared[0].alignment(), 8);
    assert_eq!(m.kernels[0].shared[1].size(), 6);
    assert_eq!(m.kernels[0].shared[1].alignment(), 2);
    bad("\t.shared .f32 s[4];", "\tret;", "unsupported .shared element type");
    bad("\t.shared .align 3 .b8 s[4];", "\tret;", "bad .align");
    bad("\t.shared .b8 s[];", "\tret;", "without a size");
    bad("\t.shared .b8 s[0];", "\tret;", "bad .shared array size");
    bad("\t.shared .b8 s[65536];", "\tret;", "exceeds 48 KB");
    bad("\t.shared .u32 s;\n\t.shared .u32 s;", "\tret;", "declared twice");
    bad("\t.shared .u32 k_p;", "\tret;", "declared twice");
    bad("\t.shared .u32 s;", "\tmov.s32 %r1, s;\n\tret;", "mov.s32 of the address");
    bad("\t.shared .u32 s;", "\tld.global.u32 %r1, [s];\n\tret;", "needs a register address");
    bad("\t.shared .u32 s;", "\tld.shared.u32 %r1, [%p1];\n\tret;", "not a 32- or 64-bit register");
}

#[test]
fn written_offsets_survive() {
    let src = kernel(
        "\tld.param.u64 %rd1, [k_p];\n\tld.global.u32 %r1, [%rd1+0];\n\tst.global.u32 [%rd1+-4], %r1;\n\tret;",
    );
    roundtrip(&src).unwrap();
    let hex = kernel("\tmov.u32 %r1, 0x10;\n\tret;");
    let m = roundtrip(&hex).unwrap();
    assert_eq!(
        m.kernels[0].body[0].instr,
        e5r_ptx::ast::Instr::Mov(
            e5r_ptx::ast::Ty::U32,
            "%r1".into(),
            e5r_ptx::ast::Operand::Imm(16)
        )
    );
}

#[test]
fn malformed_input_never_panics() {
    for (_, src) in benchmarks() {
        let bytes = src.as_bytes();
        for cut in (0..bytes.len()).step_by(7) {
            if let Ok(s) = std::str::from_utf8(&bytes[..cut]) {
                let _ = roundtrip(s);
            }
        }
        for i in (0..bytes.len()).step_by(5) {
            for b in *b"%[-0;@" {
                let mut v = bytes.to_vec();
                v[i] = b;
                if let Ok(s) = std::str::from_utf8(&v) {
                    let _ = roundtrip(s);
                }
            }
        }
    }
}
