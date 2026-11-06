//! Immediate bit insertion: independent per-bit reference, parser boundaries,
//! and interpreter behavior. GPU and Lean cross-check live in the demo.
use e5r_ptx::{interp::*, parse_module, roundtrip};
use std::collections::HashMap;

fn program(pos: &str, len: &str) -> String {
    format!(
        ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k() {{ .reg .b32 %r<4>; bfi.b32 %r0, %r1, %r2, {pos}, {len}; ret; }}"
    )
}
#[test]
fn all_admitted_fields_preserve_other_bits_and_handle_empty_ranges() {
    let c = Ctx {
        tid: Dim3::default(),
        ntid: Dim3::default(),
        ctaid: Dim3::default(),
        nctaid: Dim3::default(),
        params: HashMap::new(),
        byte_params: HashMap::new(),
        sym: HashMap::new(),
    };
    let values = [0u32, 1, 0xffff_ffff, 0x1234_5678, 0xaaaa_5555];
    for pos in 0..=32 {
        for len in 0..=32 - pos {
            let m = roundtrip(&program(&pos.to_string(), &len.to_string())).unwrap();
            for a in values {
                for b in values {
                    let mut expected = b;
                    for i in 0..len {
                        if pos + i >= 32 {
                            break;
                        }
                        expected = (expected & !(1 << (pos + i))) | (((a >> i) & 1) << (pos + i));
                    }
                    let mut s = TState::default();
                    s.r.insert("%r1".into(), a as u64);
                    s.r.insert("%r2".into(), b as u64);
                    assert!(matches!(
                        step(
                            &m.kernels[0],
                            &Allocs::default(),
                            &c,
                            &mut s,
                            &mut Mem::default(),
                            &mut Mem::default()
                        ),
                        Res::Ok(None)
                    ));
                    assert_eq!(
                        s.r["%r0"], expected as u64,
                        "a={a:x} b={b:x} pos={pos} len={len}"
                    );
                }
            }
        }
    }
}
#[test]
fn unsupported_forms_fail_closed() {
    for (pos, len) in [
        ("256", "4"),
        ("-1", "4"),
        ("%r1", "4"),
        ("14", "%r2"),
        ("1", "32"),
        ("31", "4"),
        ("255", "0"),
    ] {
        assert!(parse_module(&program(pos, len)).is_err());
    }
    assert!(parse_module(&program("14", "4").replace("bfi.b32", "bfi.b64")).is_err());
    assert!(parse_module(&program("14", "4").replace("%r2, 14", "%tid.x, 14")).is_err());
    assert!(parse_module(&program("14", "4").replace(".b32 %r<4>", ".b64 %r<4>")).is_err());
}
