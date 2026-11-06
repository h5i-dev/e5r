//! Narrow NVCC line information and nounroll metadata support.
use e5r_ptx::{parse_module, roundtrip};

const CORE: &str = ".version 9.2\n.target sm_86\n.address_size 64\n.visible .entry k()\n{\n.reg .b32 %r<2>;\nL:\nmov.u32 %r1, 1;\nret;\n}\n";

fn decorated() -> String {
    CORE.replace("L:\n", "L:\n.loc 1 58 0\n.pragma \"nounroll\";\n")
        + ".file 1 \"/source/kernel.cu\"\n"
}

#[test]
fn metadata_retains_tokens_and_leaves_instructions_and_labels_unchanged() {
    let core = roundtrip(CORE).unwrap();
    let decorated = roundtrip(&decorated()).unwrap();
    assert_eq!(core.kernels, decorated.kernels);
    assert_eq!(decorated.metadata.len(), 3);
    assert_eq!(
        e5r_ptx::lean::module(&core, "M", "test"),
        e5r_ptx::lean::module(&decorated, "M", "test")
    );
    assert_eq!(
        parse_module(&e5r_ptx::print::module(&decorated)).unwrap(),
        decorated
    );
}

#[test]
fn debug_extensions_and_unknown_pragmas_are_rejected() {
    for bad in [
        ".loc 1 58 0 function_name foo",
        ".loc 0 58 0",
        ".loc 1 -1 0",
        ".loc 1 4294967296 0",
        ".loc 2 58 0",
        ".loc 1 58 0;",
        ".pragma \"unroll\";",
        ".pragma \"nounroll\", \"other\";",
        ".pragma \"nounroll\"; ret;",
        ".pragma \"nounroll\"",
        ".section .debug_info {}",
    ] {
        let src = decorated().replace(".loc 1 58 0", bad);
        assert!(roundtrip(&src).is_err(), "accepted {bad}");
    }
    for bad in [
        ".file 1 \"path\" 0 0",
        ".file 1 \"path\";",
        ".file 1 \"path\"\n.file 1 \"other\"",
        ".file 1 \"path\\n\"",
        ".file 1 \"path\nother\"",
        ".file 1 \"unterminated",
    ] {
        let src = decorated().replace(".file 1 \"/source/kernel.cu\"", bad);
        assert!(roundtrip(&src).is_err(), "accepted {bad}");
    }
}

#[test]
fn metadata_cannot_hide_or_split_core_instructions() {
    let missing_add = decorated().replace(".loc 1 58 0", ".loc 1 58 0 add.u32 %r1, %r1, 1;");
    assert!(roundtrip(&missing_add).is_err());
    let split = decorated().replace("mov.u32 %r1, 1;", "mov.u32\n.loc 1 58 0\n%r1, 1;");
    assert!(roundtrip(&split).is_err());
    let module_scope = CORE.to_owned() + ".pragma \"nounroll\";\n";
    assert!(roundtrip(&module_scope).is_err());
    let body_file = decorated().replace("L:\n", "L:\n.file 2 \"path\"\n");
    assert!(roundtrip(&body_file).is_err());
    for token in [".version", ".target", ".address_size"] {
        let before_header = decorated().replace(token, &format!(".file 2 \"path\"\n{token}"));
        assert!(roundtrip(&before_header).is_err());
    }
    let parameter_file = decorated().replace(".entry k()", ".entry k(\n.file 2 \"path\"\n)");
    assert!(roundtrip(&parameter_file).is_err());
}

#[test]
fn quoted_paths_preserve_supported_escapes() {
    let src = decorated().replace("/source/kernel.cu", r#"C:\\source\\a\"b.cu"#);
    roundtrip(&src).unwrap();
}

#[test]
fn metadata_roundtrip_assembles_with_ptxas_when_available() {
    let assembler = std::env::var("PTXAS").unwrap_or_else(|_| "/usr/local/cuda/bin/ptxas".into());
    if std::process::Command::new(&assembler)
        .arg("--version")
        .output()
        .is_err()
    {
        eprintln!("ptxas unavailable; metadata assembler oracle not exercised");
        return;
    }
    let dir = std::env::temp_dir().join(format!("e5r-ptx-metadata-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("metadata.ptx");
    let output = dir.join("metadata.cubin");
    let module = roundtrip(&decorated()).unwrap();
    std::fs::write(&input, e5r_ptx::print::module(&module)).unwrap();
    let result = std::process::Command::new(assembler)
        .args(["-arch=sm_86", "-o"])
        .arg(output)
        .arg(input)
        .output()
        .unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn frozen_normal_ptx_roundtrips_when_requested() {
    let Some(path) = std::env::var_os("E5R_PTX_METADATA_FIXTURE") else {
        eprintln!("E5R_PTX_METADATA_FIXTURE unset; external NVCC fixture not exercised");
        return;
    };
    let src = std::fs::read_to_string(path).unwrap();
    let module = roundtrip(&src).unwrap();
    assert_eq!(module.kernels.len(), 1);
    assert!(
        module
            .metadata
            .iter()
            .any(|(_, text)| text == ".pragma \"nounroll\";")
    );
}
