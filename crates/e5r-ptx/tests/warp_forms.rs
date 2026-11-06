//! NVIDIA PTX ISA 9.2 warp/NC/volatile forms; no foreign implementation source.
//! These are frontend and fail-closed legacy-domain tests, not FP4 proofs.
use e5r_ptx::{ast::*, interp::*, roundtrip};
use std::collections::HashMap;
fn program(body: &str) -> String {
    format!(
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k(){{ .reg .pred %p; .reg .b32 %r<2>; .reg .f32 %f; .reg .b64 %rd; .shared .align 4 .b8 s[128]; {body}; ret; }}"
    )
}
#[test]
fn source_qualifiers_and_mask_spelling_survive_export() {
    for mask in ["-1", "4294967295", "0xffffffff"] {
        let src = program(&format!(
            "bar.warp.sync {mask}; ld.global.nc.f32 %f, [%rd]; st.volatile.shared.u32 [s], %r0; ld.volatile.shared.u32 %r1, [s]"
        ));
        let m = roundtrip(&src).unwrap();
        let k = &m.kernels[0];
        assert!(k.requires_warp_domain());
        assert!(matches!(k.body[0].instr, Instr::WarpBar(-1 | 4294967295)));
        assert!(matches!(k.body[1].instr, Instr::LdGlobalNCF32(..)));
        assert!(matches!(k.body[2].instr, Instr::StVolatileShared32(..)));
        assert!(matches!(k.body[3].instr, Instr::LdVolatileShared32(..)));
        let lean = e5r_ptx::lean::module(&m, "M", "test");
        for token in [
            ".warpBar",
            ".ldGlobalNCF32",
            ".stVolatileShared32",
            ".ldVolatileShared32",
        ] {
            assert!(lean.contains(token), "lost {token}");
        }
        assert_eq!(k.body.len(), 5);
    }
}
#[test]
fn partial_dynamic_predicated_and_other_qualifiers_stay_unsupported() {
    for body in [
        "bar.warp.sync 1",
        "bar.warp.sync 0",
        "bar.warp.sync 4294967296",
        "bar.warp.sync %r0",
        "@%p bar.warp.sync -1",
        "@!%p bar.warp.sync -1",
        "ld.global.nc.f64 %rd, [%rd]",
        "ld.global.nc.f32 %rd, [%rd]",
        "ld.global.nc.f32 %f, [s]",
        "ld.volatile.shared.u64 %rd, [s]",
        "ld.acquire.cta.shared.u32 %r0, [s]",
        "st.volatile.shared.u32 [s], %rd",
    ] {
        assert!(roundtrip(&program(body)).is_err(), "accepted {body}");
    }
}
fn ctx() -> Ctx {
    Ctx {
        tid: Dim3::default(),
        ntid: Dim3 { x: 64, y: 1, z: 1 },
        ctaid: Dim3::default(),
        nctaid: Dim3 { x: 1, y: 1, z: 1 },
        params: HashMap::new(),
        byte_params: HashMap::new(),
        sym: HashMap::from([("s".into(), 128)]),
    }
}
#[test]
fn legacy_interpreter_refuses_warp_and_nc_instead_of_erasing_semantics() {
    for body in ["bar.warp.sync -1", "ld.global.nc.f32 %f, [%rd]"] {
        let m = roundtrip(&program(body)).unwrap();
        assert!(
            matches!(step(&m.kernels[0], &Allocs {global:vec![],shared:vec![]}, &ctx(), &mut TState::default(), &mut Mem::default(), &mut Mem::default()), Res::Fault(msg) if msg.contains("warp-aware readonly"))
        );
    }
}
#[test]
fn volatile_shared_reads_the_executed_store_and_retains_canaries() {
    let m = roundtrip(&program(
        "st.volatile.shared.u32 [s], 0xdeadbeef; ld.volatile.shared.u32 %r1, [s]",
    ))
    .unwrap();
    let al = Allocs {
        global: vec![],
        shared: vec![Region {
            base: 128,
            size: 128,
        }],
    };
    let mut s = TState::default();
    let mut shared = Mem::default();
    let mut global = Mem::default();
    shared.wr(127, 1, 0xa5);
    shared.wr(132, 1, 0x5a);
    assert!(matches!(
        step(&m.kernels[0], &al, &ctx(), &mut s, &mut global, &mut shared),
        Res::Ok(_)
    ));
    assert!(matches!(
        step(&m.kernels[0], &al, &ctx(), &mut s, &mut global, &mut shared),
        Res::Ok(_)
    ));
    assert_eq!(s.r["%r1"], 0xdeadbeef);
    assert_eq!(shared.rd(127, 1), 0xa5);
    assert_eq!(shared.rd(132, 1), 0x5a);
    assert!(!m.kernels[0].requires_warp_domain());
}
#[test]
fn ptxas_accepts_retained_forms() {
    use std::process::Command;
    let assembler = std::env::var("PTXAS").unwrap_or_else(|_| "/usr/local/cuda/bin/ptxas".into());
    if Command::new(&assembler).arg("--version").output().is_err() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("e5r-warp-forms-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let m=roundtrip(&program("mov.u64 %rd, 0; ld.global.nc.f32 %f, [%rd]; st.volatile.shared.u32 [s], %r0; bar.warp.sync -1; ld.volatile.shared.u32 %r1, [s]")).unwrap();
    std::fs::write(dir.join("test.ptx"), e5r_ptx::print::module(&m)).unwrap();
    let r = Command::new(assembler)
        .args(["-arch=sm_86", "-o"])
        .arg(dir.join("test.cubin"))
        .arg(dir.join("test.ptx"))
        .output()
        .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
    assert!(r.status.success(), "{}", String::from_utf8_lossy(&r.stderr));
}
