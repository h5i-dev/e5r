//! Global load-image tests: PTX ISA variable declarations/initializers.
//! The FP4 bytes below are the MIT bitsandbytes pinned emission, a616886c,
//! retained in demos/oss-ptx-int4/bitsandbytes-screen/fp4-fp32.ptx.
use e5r_ptx::{interp::*, roundtrip};
use std::collections::HashMap;

fn module(declarations: &str) -> String {
    format!(
        ".version 9.2\n.target sm_86\n.address_size 64\n{declarations}\n.visible .entry read_table() {{\n.reg .b64 %rd;\n.reg .f32 %f;\nmov.u64 %rd, table;\nld.global.f32 %f, [%rd];\nret;\n}}\n"
    )
}
const TABLE: &str = ".global .align 4 .b8 table[32] = {0, 0, 0, 0, 171, 170, 170, 59, 171, 170, 42, 63, 0, 0, 128, 63, 171, 170, 170, 62, 0, 0, 0, 63, 171, 170, 42, 62, 0, 0, 128, 62};";

#[test]
fn exact_table_bytes_and_zero_data_reach_the_exporter() {
    let m = roundtrip(&module(&format!(
        "{TABLE}\n.global .align 8 .u32 zeros[2];"
    )))
    .unwrap();
    assert_eq!(m.globals.len(), 2);
    assert_eq!(m.globals[1].bytes, [0; 8]);
    let lean = e5r_ptx::lean::module(&m, "G", "test");
    assert!(lean.contains("globals := [⟨\"table\", 4, [0, 0, 0, 0, 171, 170, 170, 59,"));
    assert!(lean.contains("(.sym \"table\")"));
    let mut symbols = HashMap::new();
    symbols.insert("table".into(), 0x1000);
    symbols.insert("zeros".into(), 0x2000);
    let mut memory = Mem::default();
    memory.bytes.insert(0xfff, 0xa5);
    memory.bytes.insert(0x1020, 0xa5);
    memory.bytes.insert(0x2000, 0xa5);
    let regions = initialize_globals(&m, &symbols, &[], &mut memory).unwrap();
    assert_eq!(memory.rd(0x2000, 8), 0);
    let expected = [
        0, 0x3baaaaab, 0x3f2aaaab, 0x3f800000, 0x3eaaaaab, 0x3f000000, 0x3e2aaaab, 0x3e800000,
    ];
    for (i, bits) in expected.iter().enumerate() {
        assert_eq!(memory.rd(0x1000 + i as u64 * 4, 4), *bits);
    }
    assert_eq!(memory.get(0xfff), 0xa5);
    assert_eq!(memory.get(0x1020), 0xa5);
    // Execute real instruction constructors, not a decoder approximation.
    let context = Ctx {
        tid: Dim3::default(),
        ntid: Dim3 { x: 1, y: 1, z: 1 },
        ctaid: Dim3::default(),
        nctaid: Dim3 { x: 1, y: 1, z: 1 },
        params: HashMap::new(),
        byte_params: HashMap::new(),
        sym: symbols,
    };
    let alloc = Allocs {
        global: regions,
        shared: vec![],
    };
    let mut state = TState::default();
    for _ in 0..2 {
        assert!(matches!(
            step(
                &m.kernels[0],
                &alloc,
                &context,
                &mut state,
                &mut memory,
                &mut Mem::default()
            ),
            Res::Ok(_)
        ));
    }
    assert_eq!(state.r["%rd"], 0x1000);
    assert_eq!(state.r["%f"], 0);
}

#[test]
fn unsafe_placements_reject_without_partial_initialization() {
    let m = roundtrip(&module(TABLE)).unwrap();
    for address in [None, Some(0x1001), Some(u64::MAX - 3)] {
        let symbols: HashMap<_, _> = address.map(|a| ("table".into(), a)).into_iter().collect();
        let mut memory = Mem::default();
        memory.bytes.insert(0x1000, 0xa5);
        assert!(initialize_globals(&m, &symbols, &[], &mut memory).is_err());
        assert_eq!(memory.bytes.len(), 1);
        assert_eq!(memory.get(0x1000), 0xa5);
    }
    let symbols = HashMap::from([("table".into(), 0x1000)]);
    let mut memory = Mem::default();
    assert!(
        initialize_globals(
            &m,
            &symbols,
            &[Region {
                base: 0x101f,
                size: 1
            }],
            &mut memory
        )
        .is_err()
    );
    assert!(memory.bytes.is_empty());
}

#[test]
fn malformed_definitions_and_symbol_aliases_fail_closed() {
    for bad in [
        ".global .align 4 .b8 table[2] = {1};",
        ".global .align 4 .b8 table[1] = {1,2};",
        ".global .align 4 .b8 table[1] = {256};",
        ".global .align 4 .b8 table[1] = {-1};",
        ".global .align 4 .b8 table[0];",
        ".global .align 4 .b8 table[1048577];",
        ".global .align 4 .b8 table[2] = {other,0};",
        ".global .align 4 .b8 table[1] = {0}; ret;",
        ".global .align 4 .b8 table[1];\n.global .align 4 .u32 table;",
    ] {
        assert!(roundtrip(&module(bad)).is_err(), "accepted {bad}");
    }
    let clash = module(TABLE).replace(
        ".reg .b64 %rd;",
        ".shared .align 4 .b8 table[4];\n.reg .b64 %rd;",
    );
    assert!(roundtrip(&clash).is_err());
}

#[test]
fn module_load_image_roundtrip_has_an_external_assembler_oracle() {
    use std::process::Command;
    let assembler = std::env::var("PTXAS").unwrap_or_else(|_| "/usr/local/cuda/bin/ptxas".into());
    if Command::new(&assembler).arg("--version").output().is_err() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("e5r-global-image-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let parsed = roundtrip(&module(TABLE)).unwrap();
    let input = dir.join("globals.ptx");
    std::fs::write(&input, e5r_ptx::print::module(&parsed)).unwrap();
    let result = Command::new(assembler)
        .args(["-arch=sm_86", "-o"])
        .arg(dir.join("globals.cubin"))
        .arg(input)
        .output()
        .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    // A changed source initializer must change actual initialized load bytes.
    let wrong = roundtrip(&module(&TABLE.replacen("{0,", "{1,", 1))).unwrap();
    let mut memory = Mem::default();
    initialize_globals(
        &wrong,
        &HashMap::from([("table".into(), 0x1000)]),
        &[],
        &mut memory,
    )
    .unwrap();
    assert_eq!(memory.rd(0x1000, 4), 1);
    assert_ne!(memory.rd(0x1000, 4), parsed.globals[0].bytes[0] as u64);
}
