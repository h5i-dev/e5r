//! Narrow PTX integer operands: NVIDIA PTX ISA §9.4.1 (relaxed ld/st/cvt
//! operand widths), §9.7.8 (logic/shift), and §9.7.9 (data movement).
use e5r_ptx::{interp::*, parse_module, roundtrip};
use std::collections::HashMap;

fn program(body: &str) -> String {
    format!(".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k() {{ .reg .pred %p; .reg .b16 %h<4>; .reg .b32 %r<4>; .reg .b64 %rd<4>; {body}; ret; }}")
}

fn execute(body: &str, a: u64, b: u64) -> TState {
    let m = roundtrip(&program(body)).unwrap();
    let c = Ctx {
        tid: Dim3::default(),
        ntid: Dim3::default(),
        ctaid: Dim3::default(),
        nctaid: Dim3::default(),
        params: HashMap::new(),
        byte_params: HashMap::new(),
        sym: HashMap::new(),
    };
    let mut s = TState::default();
    for r in ["%h1", "%r1", "%rd1"] {
        s.r.insert(r.into(), a);
    }
    for r in ["%h2", "%r2", "%rd2"] {
        s.r.insert(r.into(), b);
    }
    for _ in 0..m.kernels[0].body.len() - 1 {
        assert_eq!(
            step(
                &m.kernels[0],
                &Allocs::default(),
                &c,
                &mut s,
                &mut Mem::default(),
                &mut Mem::default()
            ),
            Res::Ok(None)
        );
    }
    s
}

#[test]
fn narrow_operations_truncate_before_comparing_shifting_and_converting() {
    let values = [
        0,
        1,
        0x7f,
        0x80,
        0xff,
        0x100,
        0x7fff,
        0x8000,
        0xffff,
        0x1ffff,
        u64::MAX,
    ];
    for a in values {
        for b in values {
            let x = a as u16;
            let y = b as u16;
            for (op, expected) in [("and", x & y), ("or", x | y), ("xor", x ^ y)] {
                assert_eq!(
                    execute(&format!("{op}.b16 %h0, %h1, %h2"), a, b).r["%h0"],
                    expected as u64
                );
            }
            let n = b as u32;
            let left = if n >= 16 { 0 } else { x << n };
            let right = if n >= 16 { 0 } else { x >> n };
            let signed_right = ((x as i16) >> n.min(15)) as u16;
            assert_eq!(execute("shl.b16 %h0, %h1, %r2", a, b).r["%h0"], left as u64);
            assert_eq!(
                execute("shr.u16 %h0, %h1, %r2", a, b).r["%h0"],
                right as u64
            );
            assert_eq!(
                execute("shr.s16 %h0, %h1, %r2", a, b).r["%h0"],
                signed_right as u64
            );
            let s = execute("setp.lt.s16 %p, %h1, %h2; selp.u16 %h0, %h1, %h2, %p", a, b);
            assert_eq!(
                s.r["%h0"],
                if (x as i16) < (y as i16) {
                    x as u64
                } else {
                    y as u64
                }
            );
        }
        assert_eq!(
            execute("cvt.u16.u32 %r0, %r1", a, 0).r["%r0"],
            a as u16 as u64
        );
        assert_eq!(
            execute("cvt.u32.s16 %r0, %r1", a, 0).r["%r0"],
            a as u16 as i16 as i32 as u32 as u64
        );
        assert_eq!(
            execute("cvt.u64.s16 %rd0, %rd1", a, 0).r["%rd0"],
            a as u16 as i16 as i64 as u64
        );
    }
}

#[test]
fn unsigned_loads_zero_extend_and_stores_touch_only_their_bytes() {
    for (ty, bytes) in [("u8", 1), ("u16", 2), ("b16", 2)] {
        for d in ["%h0", "%r0", "%rd0"] {
            let source = program(&format!(
                "ld.global.{ty} {d}, [%rd1]; st.global.{ty} [%rd2], {d}"
            ));
            let m = roundtrip(&source).unwrap();
            let c = Launch {
                grid: Dim3::default(),
                block: Dim3::default(),
                params: HashMap::new(),
                byte_params: HashMap::new(),
                sym: HashMap::new(),
                alloc: vec![],
            }
            .ctx(Dim3::default(), Dim3::default());
            let al = Allocs {
                global: vec![
                    Region {
                        base: 0x1000,
                        size: 16,
                    },
                    Region {
                        base: 0x2000,
                        size: 16,
                    },
                ],
                shared: vec![],
            };
            let mut s = TState::default();
            s.r.insert("%rd1".into(), 0x1001 + (bytes - 1) as u64);
            s.r.insert("%rd2".into(), 0x2004);
            s.r.insert(d.into(), u64::MAX);
            let mut g = Mem::default();
            for i in 0..16 {
                g.bytes.insert(0x1000 + i, 0xff);
                g.bytes.insert(0x2000 + i, 0xa5);
            }
            for _ in 0..2 {
                assert!(matches!(
                    step(&m.kernels[0], &al, &c, &mut s, &mut g, &mut Mem::default()),
                    Res::Ok(Some(_))
                ));
            }
            assert_eq!(s.r[d], if bytes == 1 { 255 } else { 65535 });
            for i in 0..16 {
                assert_eq!(
                    g.bytes[&(0x2000 + i)],
                    if (4..4 + bytes as u64).contains(&i) {
                        255
                    } else {
                        0xa5
                    }
                );
            }
            if bytes == 2 {
                s.pc = 0;
                s.r.insert("%rd1".into(), 0x1001);
                assert!(matches!(
                    step(&m.kernels[0], &al, &c, &mut s, &mut g, &mut Mem::default()),
                    Res::Fault(_)
                ));
            }
        }
    }
}

#[test]
fn unsupported_narrow_forms_fail_closed() {
    for body in [
        "add.u8 %r0, %r1, %r2",
        "add.u16 %h0, %h1, %h2",
        "ld.global.s16 %r0, [%rd1]",
        "ld.global.s8 %r0, [%rd1]",
        "atom.global.add.u16 %h0, [%rd1], %h1",
        "atom.global.and.b16 %h0, [%rd1], %h1",
        "cvt.s16.u32 %r0, %r1",
        "mov.u8 %r0, 1",
        "cvt.u8.u32 %r0, %r1",
        "and.b16 %r0, %r1, %r2",
        "setp.lt.b16 %p, %h1, %h2",
        "mov.u16 %h0, 65536",
        "mov.u16 %h0, -32769",
        "shl.b16 %h0, %h1, %h2",
    ] {
        assert!(parse_module(&program(body)).is_err(), "{body}");
    }
    assert!(parse_module(&program("mov.u16 %h0, 1").replace(".b16 %h", ".u8 %h")).is_err());
    let k = roundtrip(&program(
        "cvt.u16.u32 %h0, %r1; and.b16 %h0, %h0, 255; setp.ne.s16 %p, %h0, 0",
    ))
    .unwrap()
    .kernels
    .remove(0);
    let lean = e5r_ptx::lean::kernel_def(&k);
    assert!(
        lean.contains(".cvt .u16 .u32")
            && lean.contains(".and .b16")
            && lean.contains(".setp .ne .s16")
    );
}

#[test]
fn aggregate_byte_and_half_loads_keep_alignment_and_bounds() {
    let source = ".version 8.0\n.target sm_86\n.address_size 64\n.visible .entry k(.param .align 2 .b8 data[3]) { .reg .b32 %r<2>; ld.param.u8 %r0, [data+1]; ld.param.u16 %r1, [data]; ret; }";
    let m = roundtrip(source).unwrap();
    let c = Launch {
        grid: Dim3::default(),
        block: Dim3::default(),
        params: HashMap::new(),
        byte_params: HashMap::from([("data".into(), vec![0xff, 0x80, 0x42])]),
        sym: HashMap::new(),
        alloc: vec![],
    }
    .ctx(Dim3::default(), Dim3::default());
    let k = &m.kernels[0];
    assert_eq!(
        param_value(k, &c, e5r_ptx::ast::Ty::U8, "data", 1),
        Some(0x80)
    );
    assert_eq!(
        param_value(k, &c, e5r_ptx::ast::Ty::U16, "data", 0),
        Some(0x80ff)
    );
    for bad in ["data+1", "data+2", "data+3", "data-1"] {
        assert!(parse_module(&source.replace("[data]", &format!("[{bad}]"))).is_err());
    }
}
