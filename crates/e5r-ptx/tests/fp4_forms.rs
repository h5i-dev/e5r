//! Prerequisite forms appearing unchanged in the pinned FP4 PTX.
//! Specification: NVIDIA PTX ISA 9.2 clz/min/cvt/special registers/default RN.
use e5r_ptx::{ast::*, interp::*, roundtrip};
use std::collections::HashMap;
fn program(body: &str) -> String {
    format!(
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k(){{\n.reg .b16 %h<3>;\n.reg .b32 %r<5>, %v;\n.reg .f32 %f<3>;\n{body};\nret;\n}}\n"
    )
}
fn run(body: &str, input: u64, tid: Dim3, block: Dim3) -> TState {
    let m = roundtrip(&program(body)).unwrap();
    let c = Ctx {
        tid,
        ntid: block,
        ctaid: Dim3::default(),
        nctaid: Dim3 { x: 1, y: 1, z: 1 },
        params: HashMap::new(),
        byte_params: HashMap::new(),
        sym: HashMap::new(),
    };
    let al = Allocs {
        global: vec![],
        shared: vec![],
    };
    let mut state = TState::default();
    state.r.insert("%r1".into(), input);
    state.r.insert("%h1".into(), input);
    for _ in 0..m.kernels[0].body.len() - 1 {
        assert!(matches!(
            step(
                &m.kernels[0],
                &al,
                &c,
                &mut state,
                &mut Mem::default(),
                &mut Mem::default()
            ),
            Res::Ok(_)
        ));
    }
    state
}
#[test]
fn clz_and_signed_min_ignore_upper_bits_and_cover_zero() {
    for (value, count) in [
        (0, 32),
        (1, 31),
        (0x8000_0000, 0),
        (0xffff_ffff, 0),
        (0x0000_1000, 19),
        (0x1234_5678_0000_0010, 27),
    ] {
        let s = run(
            "clz.b32 %r0, %r1; min.s32 %r2, %r1, 0",
            value,
            Dim3::default(),
            Dim3 { x: 64, y: 1, z: 1 },
        );
        assert_eq!(s.r["%r0"], count);
        assert_eq!(s.r["%r2"], (value as u32 as i32).min(0) as u32 as u64);
    }
}
#[test]
fn laneid_linearizes_all_three_dimensions() {
    for (block, tid, expected) in [
        (Dim3 { x: 64, y: 1, z: 1 }, Dim3 { x: 35, y: 0, z: 0 }, 3),
        (Dim3 { x: 8, y: 8, z: 2 }, Dim3 { x: 3, y: 5, z: 1 }, 11),
    ] {
        assert_eq!(
            run("mov.u32 %r0, %laneid", 0, tid, block).r["%r0"],
            expected
        );
    }
}
#[test]
fn unsigned_and_signed_u16_float_conversions_chop_the_source() {
    for value in [0, 2, 0x7fff, 0x8000, 0xffff, 0xffff_ffff_ffff_8001] {
        let s = run(
            "cvt.rn.f32.u16 %f0, %h1; cvt.rn.f32.s16 %f1, %h1",
            value,
            Dim3::default(),
            Dim3 { x: 64, y: 1, z: 1 },
        );
        assert_eq!(s.r["%f0"], (value as u16 as f32).to_bits() as u64);
        assert_eq!(s.r["%f1"], (value as u16 as i16 as f32).to_bits() as u64);
    }
}
#[test]
fn grouped_declarations_and_default_rounding_remain_distinct() {
    let implicit = roundtrip(&program(
        "mov.f32 %f1, 0f00000000; sub.ftz.f32 %f0, 0f3f800000, %f1",
    ))
    .unwrap();
    assert!(
        implicit.kernels[0]
            .decls
            .iter()
            .any(|x| matches!(x, Decl::RegGroup(_, 2)))
    );
    assert!(matches!(
        implicit.kernels[0].body[1].instr,
        Instr::FBinDefault(FBin::Sub, true, false, Ty::F32, _, _, _)
    ));
    assert!(
        e5r_ptx::lean::module(&implicit, "M", "test").contains(".fbinDefault .sub true false .f32")
    );
    let explicit = roundtrip(&program("sub.rn.ftz.f32 %f0, 0f3f800000, 0f00000000")).unwrap();
    assert!(matches!(
        explicit.kernels[0].body[0].instr,
        Instr::FBin(_, RMode::Rn, ..)
    ));
    assert_ne!(
        implicit.kernels[0].body[1].instr,
        explicit.kernels[0].body[0].instr
    );
    for value in [0, 2] {
        let s = run(
            "cvt.rn.f32.u16 %f1, %h1; sub.ftz.f32 %f0, 0f3f800000, %f1",
            value,
            Dim3::default(),
            Dim3 { x: 64, y: 1, z: 1 },
        );
        assert_eq!(s.r["%f0"], (1.0f32 - value as f32).to_bits() as u64);
    }
}
#[test]
fn invalid_widths_and_unimplemented_variants_still_reject() {
    for body in [
        "clz.b64 %r0, %r1",
        "clz.b32 %h0, %r1",
        "clz.b32 %r0, %h1",
        "min.u16 %h0, %h1, 1",
        "div.f32 %f0, %f1, %f2",
        "fma.f32 %f0, %f1, %f2, %f1",
    ] {
        assert!(roundtrip(&program(body)).is_err(), "accepted {body}");
    }
    assert!(
        roundtrip(&program("mov.u32 %r0, %laneid").replace("%r<5>, %v", "%r<5>, %r1")).is_err()
    );
}
#[test]
fn prerequisite_forms_assemble_with_ptxas() {
    use std::process::Command;
    let assembler = std::env::var("PTXAS").unwrap_or_else(|_| "/usr/local/cuda/bin/ptxas".into());
    if Command::new(&assembler).arg("--version").output().is_err() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("e5r-fp4-forms-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("forms.ptx");
    let m=roundtrip(&program("mov.u32 %r1, %laneid; clz.b32 %r0, %r1; min.s32 %r2, %r1, 7; mov.u16 %h1, 2; cvt.rn.f32.u16 %f1, %h1; sub.ftz.f32 %f0, 0f3f800000, %f1; mul.ftz.f32 %f2, %f0, 0f00000000")).unwrap();
    std::fs::write(&path, e5r_ptx::print::module(&m)).unwrap();
    let result = Command::new(assembler)
        .args(["-arch=sm_86", "-o"])
        .arg(dir.join("forms.cubin"))
        .arg(path)
        .output()
        .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}
