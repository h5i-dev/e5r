//! Explicit by-value ABI bytes. Syntax/alignment follow the public NVIDIA PTX
//! ISA kernel-function-parameters and addresses-as-operands specifications.
use e5r_ptx::{ast::*, interp::*, roundtrip};
use std::{collections::HashMap, path::Path, process::Command};

const SOURCE: &str = ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry aggregate(\n.param .align 8 .b8 a[32],\n.param .u32 n,\n.param .align 8 .b8 b[24]\n)\n{\n.reg .b64 %rd<3>;\n.reg .b32 %r;\nld.param.u64 %rd0, [a];\nld.param.u64 %rd1, [a+24];\nld.param.u32 %r, [n];\nld.param.u64 %rd2, [b+16];\nret;\n}\n";

fn launch() -> Launch {
    Launch {
        grid: Dim3 { x: 1, y: 1, z: 1 },
        block: Dim3 { x: 1, y: 1, z: 1 },
        params: HashMap::from([("n".into(), 0xabcdef0123456789), ("a".into(), u64::MAX)]),
        byte_params: HashMap::from([
            ("a".into(), (0u8..32).collect()),
            ("b".into(), (64u8..88).collect()),
            ("n".into(), vec![255; 8]),
        ]),
        sym: HashMap::new(),
        alloc: Vec::new(),
    }
}

#[test]
fn mixed_abi_order_and_every_byte_survive_roundtrip() {
    let m = roundtrip(SOURCE).unwrap();
    let k = &m.kernels[0];
    assert_eq!(k.params, [("n".into(), Ty::U32)]);
    assert_eq!(
        k.aggregate_params,
        [
            AggregateParam {
                name: "a".into(),
                align: 8,
                size: 32
            },
            AggregateParam {
                name: "b".into(),
                align: 8,
                size: 24
            },
        ]
    );
    assert_eq!(
        k.param_decls,
        [
            ParamDecl::Aggregate(0),
            ParamDecl::Scalar(0),
            ParamDecl::Aggregate(1)
        ]
    );
    let exported = e5r_ptx::lean::kernel_def(k);
    assert!(exported.contains("aggregateParams := [⟨\"a\", 8, 32⟩, ⟨\"b\", 8, 24⟩]"));
    assert!(exported.contains("paramOrder := [.aggregate 0, .scalar 0, .aggregate 1]"));
    roundtrip(&SOURCE.replace("[a]", "[a+0]")).unwrap();
    roundtrip(&SOURCE.replace("a[32]", "a[4068]")).unwrap();
}

#[test]
fn byte_loads_are_little_endian_and_scalar_bits_are_independent() {
    let m = roundtrip(SOURCE).unwrap();
    let k = &m.kernels[0];
    let c = launch().ctx(Dim3::default(), Dim3::default());
    let mut s = TState::default();
    let mut g = Mem::default();
    let mut sh = Mem::default();
    for _ in 0..4 {
        assert_eq!(
            step(k, &Allocs::default(), &c, &mut s, &mut g, &mut sh),
            Res::Ok(None)
        );
    }
    assert_eq!(s.r["%rd0"], 0x0706050403020100);
    assert_eq!(s.r["%rd1"], 0x1f1e1d1c1b1a1918);
    assert_eq!(s.r["%rd2"], 0x5756555453525150);
    assert_eq!(s.r["%r"], 0x23456789);
    assert!(g.bytes.is_empty() && sh.bytes.is_empty());
    let mut absent = c.clone();
    absent.byte_params.clear();
    assert_eq!(param_value(k, &absent, Ty::U64, "a", 24), Some(0));
    for (i, byte) in c.byte_params["a"].iter().enumerate() {
        assert_eq!(
            param_value(k, &c, Ty::U32, "a", (i / 4 * 4) as i128).unwrap() >> (8 * (i % 4)) & 255,
            *byte as u64
        );
    }
}

#[test]
fn bad_bounds_alignment_declarations_and_scalar_offsets_are_refused() {
    for (from, to) in [
        ("[a+24]", "[a+25]"),
        ("[a+24]", "[a+32]"),
        ("[a+24]", "[a-8]"),
        ("[a+24]", "[missing]"),
        ("[n]", "[n+4]"),
        (".align 8 .b8 a", ".align 4 .b8 a"),
        (".align 8 .b8 a", ".align 3 .b8 a"),
        ("a[32]", "a[0]"),
        ("a[32]", "a[4096]"),
        ("a[32]", "a[4069]"),
        (".b8 a", ".u8 a"),
        (".b8 a", ".b16 a"),
        (".u32 n", ".u32 a"),
        (".b8 b", ".b8 a"),
        (".b8 a", ".b8 %a"),
        (".b8 a", ".b8 .a"),
    ] {
        assert!(
            roundtrip(&SOURCE.replace(from, to)).is_err(),
            "accepted {from} -> {to}"
        );
    }
    let mut k = roundtrip(SOURCE).unwrap().kernels.remove(0);
    let c = launch().ctx(Dim3::default(), Dim3::default());
    for off in [-8, 1, 28, 32, i128::MAX] {
        assert_eq!(param_value(&k, &c, Ty::U64, "a", off), None);
        k.body[0].instr = Instr::Ld(
            Space::Param,
            Ty::U64,
            "%rd0".into(),
            Address::Param("a".into(), Some(off)),
        );
        assert!(matches!(
            step(
                &k,
                &Allocs::default(),
                &c,
                &mut TState::default(),
                &mut Mem::default(),
                &mut Mem::default()
            ),
            Res::Fault(_)
        ));
    }
    k.aggregate_params[0].align = 4;
    assert_eq!(param_value(&k, &c, Ty::U64, "a", 0), None);
}

#[test]
fn aggregate_abi_roundtrip_assembles_with_ptxas() {
    let assembler = std::env::var("PTXAS").unwrap_or_else(|_| "/usr/local/cuda/bin/ptxas".into());
    if Command::new(&assembler).arg("--version").output().is_err() {
        eprintln!("ptxas unavailable; aggregate ABI oracle not exercised");
        return;
    }
    let dir = std::env::temp_dir().join(format!("e5r-ptx-aggregate-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("aggregate.ptx");
    std::fs::write(&input, e5r_ptx::print::module(&roundtrip(SOURCE).unwrap())).unwrap();
    let output = Command::new(&assembler)
        .args(["-arch=sm_86", "-o"])
        .arg(dir.join("out.cubin"))
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    for align in [1, 2, 4, 8, 16, 32, 64, 128] {
        let src = format!(
            ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k(.param .align {align} .b8 a[32]) {{ ret; }}\n"
        );
        std::fs::write(&input, e5r_ptx::print::module(&roundtrip(&src).unwrap())).unwrap();
        let output = Command::new(&assembler)
            .args(["-arch=sm_86", "-o"])
            .arg(dir.join("out.cubin"))
            .arg(&input)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "alignment {align}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn exported_aggregate_loads_replay_in_lean() {
    if Command::new("lake").arg("--version").output().is_err() {
        eprintln!("lake unavailable; aggregate export replay not exercised");
        return;
    }
    let project = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../verification/ptx");
    let build = Command::new("lake")
        .current_dir(&project)
        .env("LEAN_NUM_THREADS", "2")
        .args(["build", "Ptx.Examples.AggregateParam"])
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let m = roundtrip(SOURCE).unwrap();
    let mut proof = String::from("import Ptx.Examples.AggregateParam\nopen Ptx\n");
    proof.push_str(&e5r_ptx::lean::kernel_def(&m.kernels[0]));
    proof.push_str(
        "\nexample : aggregate.aggregateParams = [⟨\"a\", 8, 32⟩, ⟨\"b\", 8, 24⟩] := rfl\n",
    );
    proof.push_str(
        "example : aggregate.paramOrder = [.aggregate 0, .scalar 0, .aggregate 1] := rfl\n",
    );
    let c = launch().ctx(Dim3::default(), Dim3::default());
    for (name, off, t) in [
        ("a", 0, Ty::U64),
        ("a", 24, Ty::U64),
        ("b", 16, Ty::U64),
        ("n", 0, Ty::U32),
    ] {
        let expected = param_value(&m.kernels[0], &c, t, name, off).unwrap();
        proof.push_str(&format!("example : paramValue aggregate Examples.AggregateParam.ctx .{} \"{name}\" {off} = some {expected} := by decide\n", t.name()));
    }
    let path =
        std::env::temp_dir().join(format!("e5r-aggregate-replay-{}.lean", std::process::id()));
    std::fs::write(&path, proof).unwrap();
    let output = Command::new("lake")
        .current_dir(project)
        .env("LEAN_NUM_THREADS", "2")
        .args(["env", "lean"])
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(
        output.status.success(),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
