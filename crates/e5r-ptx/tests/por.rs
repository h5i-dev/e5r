//! Predicate OR truth table, guards, aliasing and typing boundaries.
use e5r_ptx::{interp::*, parse_module, roundtrip};
use std::collections::HashMap;

fn program(body: &str) -> String {
    format!(
        ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k() {{ .reg .pred %p<4>; .reg .b32 %r<2>; {body} ret; }}"
    )
}

#[test]
fn predicate_or_truth_table_and_guards() {
    let c = Ctx {
        tid: Dim3::default(),
        ntid: Dim3::default(),
        ctaid: Dim3::default(),
        nctaid: Dim3::default(),
        params: HashMap::new(),
        byte_params: HashMap::new(),
        sym: HashMap::new(),
    };
    for a in [false, true] {
        for b in [false, true] {
            for initial_d in [false, true] {
                for (guard, execute) in [("", true), ("@%p3 ", true), ("@!%p3 ", false)] {
                    for d in ["%p0", "%p1", "%p2"] {
                        let text = program(&format!("{guard}or.pred {d}, %p1, %p2;"));
                        let m = roundtrip(&text).unwrap();
                        assert!(
                            e5r_ptx::export_lean(&text, "T", "test")
                                .unwrap()
                                .contains(".por")
                        );
                        let mut s = TState::default();
                        s.p.insert("%p0".into(), initial_d);
                        s.p.insert("%p1".into(), a);
                        s.p.insert("%p2".into(), b);
                        s.p.insert("%p3".into(), true);
                        s.r.insert("%r0".into(), 0x1234);
                        let old = s.clone();
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
                        assert_eq!(s.pc, 1);
                        assert_eq!(s.r, old.r);
                        for p in ["%p0", "%p1", "%p2", "%p3"] {
                            let expected = if execute && p == d { a || b } else { old.p[p] };
                            assert_eq!(s.p[p], expected, "a={a} b={b} d={d} guard={guard}");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn predicate_or_refuses_data_immediates_negations_and_undeclared_registers() {
    for body in [
        "or.pred %r0, %p1, %p2;",
        "or.pred %p0, %r1, %p2;",
        "or.pred %p0, %p1, %r1;",
        "or.pred %p0, 1, %p2;",
        "or.pred %p0, %p1, 0;",
        "or.pred %p0, !%p1, %p2;",
        "or.pred %p4, %p1, %p2;",
        "@%r0 or.pred %p0, %p1, %p2;",
        "and.pred %p0, %p1, %p2;",
        "xor.pred %p0, %p1, %p2;",
    ] {
        assert!(parse_module(&program(body)).is_err(), "accepted {body}");
    }
}
