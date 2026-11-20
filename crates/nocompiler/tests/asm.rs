//! `nocompiler asm` (docs/isa/asm.md): the encoder is the inverse of the
//! decoder, the listing syntax is the inverse of `Instr::asm`, and
//! `disasm` then `asm` gives back every committed example (code, symbols,
//! data, structure). Labels give R3 by construction; malformed nesting and
//! targets are refused.

use nocompiler::asm::{assemble, assemble_one, encode, listing, write_elf};
use nocompiler::isa::decode;
use std::path::PathBuf;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// xorshift, so the test is the same on every run.
fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

#[test]
fn encode_inverts_decode() {
    let mut s = 0x9e3779b97f4a7c15u64;
    let mut n = 0;
    // Random words, and words with each major opcode forced (so that the
    // sparse ones are covered too).
    for k in 0..2_000_000u64 {
        let mut w = rng(&mut s) as u32;
        if k % 2 == 0 {
            let opc = [
                0x37, 0x17, 0x6f, 0x67, 0x63, 0x03, 0x23, 0x13, 0x1b, 0x33, 0x3b,
            ][(k / 2 % 11) as usize];
            w = (w & !0x7f) | opc;
        }
        if let Some(i) = decode(w) {
            assert_eq!(encode(&i), w, "{w:#010x} decodes to {i:?}");
            n += 1;
        }
    }
    assert!(n > 300_000, "only {n} decodable words");
    for w in [0x00000073u32, 0x0805053bu32 /* zext.h */] {
        assert_eq!(encode(&decode(w).unwrap()), w);
    }
}

#[test]
fn listing_syntax_inverts_asm() {
    let mut s = 0x2545f4914f6cdd1du64;
    let mut n = 0;
    for k in 0..1_000_000u64 {
        let mut w = rng(&mut s) as u32;
        if k % 2 == 0 {
            let opc = [
                0x37, 0x17, 0x6f, 0x67, 0x63, 0x03, 0x23, 0x13, 0x1b, 0x33, 0x3b,
            ][(k / 2 % 11) as usize];
            w = (w & !0x7f) | opc;
        }
        let pc = 0x10000 + 4 * (rng(&mut s) % 0x100000);
        if let Some(i) = decode(w) {
            let text = i.asm(pc);
            assert_eq!(assemble_one(&text, pc), Ok(w), "`{text}` at {pc:#x}");
            n += 1;
        }
    }
    assert!(n > 150_000);
}

/// Every committed profile binary: `disasm`, `asm`, and compare.
#[test]
fn committed_examples_round_trip() {
    let elfs = [
        "examples/elf/sum.elf",
        "examples/elf/hello.elf",
        "demo/elf/sum.b.elf",
        "demo/elf/cobs.b.elf",
    ];
    for e in elfs {
        let bytes = std::fs::read(root().join(e)).unwrap();
        let bin = nocompiler::load(&bytes).unwrap();
        let text = listing(&bin);
        let a = assemble(&text).unwrap_or_else(|err| panic!("{e}: {err}"));
        let out = write_elf(&a).unwrap();
        let bin2 = nocompiler::load(&out).unwrap();
        assert_eq!(bin2.text_addr, bin.text_addr, "{e}: .text address");
        assert_eq!(bin2.text, bin.text, "{e}: .text");
        let fs = |b: &nocompiler::Binary| {
            let mut v: Vec<_> = b
                .funcs
                .iter()
                .map(|f| (f.name.clone(), f.entry, f.words.clone()))
                .collect();
            v.sort_by_key(|x| x.1);
            v
        };
        assert_eq!(fs(&bin2), fs(&bin), "{e}: functions");
        assert_eq!(bin2.segments, bin.segments, "{e}: data sections");
        let metas = |b: &nocompiler::Binary| {
            let mut v: Vec<_> = b.check().into_iter().map(|r| r.result.unwrap()).collect();
            v.sort_by_key(|m| m.entry);
            v
        };
        assert_eq!(metas(&bin2), metas(&bin), "{e}: structure, frames, callees");
        assert!(bin2.recorded.is_some(), "{e}: .nocompiler.struct written");
        assert_eq!(listing(&bin2), text, "{e}: the listing of the output");
    }
}

const COUNT: &str = "
count:
  ; a0 = buf, a1 = n, a2 = byte: how many of the n bytes equal it
  li a3, 0
  block @done {
    beqz a1, @done
    loop @next {
      lbu a4, 0(a0)
      bne a4, a2, @skip_inc
      addi a3, a3, 1
      ; (a forward branch to a label that is not an enclosing block)
      addi a0, a0, 1
      addi a1, a1, -1
      bnez a1, @next
    end loop
  end block
  mv a0, a3
  ret
";

#[test]
fn labels_must_name_an_enclosing_block_or_loop() {
    let e = assemble(COUNT).unwrap_err();
    assert!(e.contains("@skip_inc") && e.contains("line 9"), "{e}");
    let ok = COUNT.replace(
        "      lbu a4, 0(a0)\n      bne a4, a2, @skip_inc\n      addi a3, a3, 1\n",
        "      lbu a4, 0(a0)\n      block @skip {\n        bne a4, a2, @skip\n        addi a3, a3, 1\n      end block\n",
    );
    let a = assemble(&ok).unwrap();
    let f = &a.funcs[0];
    assert_eq!(f.entry, nocompiler::asm::DEFAULT_TEXT);
    // `beqz a1, @done` goes to the end of the block, `bnez a1, @next` to the loop head.
    let at = |k: usize| decode(f.words[k]).unwrap().asm(f.entry + 4 * k as u64);
    assert_eq!(at(1), format!("beq a1, zero, {:#x}", f.entry + 4 * 8));
    assert_eq!(at(7), format!("bne a1, zero, {:#x}", f.entry + 4 * 2));
    assert_eq!(a.metas[0].nodes.len(), 1);
    assert_eq!(f.loops.len(), 1);
}

#[test]
fn malformed_sources_are_refused() {
    let cases = [
        ("f:\n  block {\n  ret\n  end loop\n", "closes"),
        ("f:\n  loop {\n  ret\n", "not closed"),
        ("f:\n  block {\n  end block\n  ret\n", "empty"),
        (
            "f 0x11000:\n  11004: 00008067  jalr zero, 0(ra)\n",
            "the listing says 0x11004",
        ),
        (
            "f:\n  11000: 00008068  jalr zero, 0(ra)\n",
            "encodes as 00008067",
        ),
        ("f:\n  addi a0, a0, 4096\n  ret\n", "does not fit"),
        ("f:\n  frob a0\n", "unknown instruction"),
        // Assembles, but breaks a rule: the checker runs on the result.
        ("f:\n  addi a0, a0, 1\n", "does not conform"),
        ("f:\n  addi gp, gp, 1\n  ret\n", "R4"),
    ];
    for (src, want) in cases {
        let e = assemble(src).expect_err(src);
        assert!(e.contains(want), "`{src}`: {e}");
    }
}

#[test]
fn annotations_reach_the_skeleton() {
    let src = "#import Demo.CountSpec\nf:\n  #spec Demo.Count.spec\n  #intro ⟨a, xs⟩ s he ⟨h0, h1⟩\n  li a3, 0\n  block @d {\n    beqz a1, @d\n    loop @l {\n      #inv fun u => ∃ k, u.reg 13 = BitVec.ofNat 64 k\n      #    ∧ k ≤ xs.length\n      #measure fun u => (u.reg 11).toNat\n      addi a1, a1, -1\n      bnez a1, @l\n    end loop\n  end block\n  ret\n";
    let a = assemble(src).unwrap();
    let sk = nocompiler::asm::skeleton(&a, "My.Image", "f.s");
    assert!(
        sk.starts_with("import My.Image\nimport Demo.CountSpec\n"),
        "{sk}"
    );
    assert!(
        sk.contains("theorem f_verified : Verified code f_dom f_entry (Demo.Count.spec) := by"),
        "{sk}"
    );
    assert!(
        sk.contains("  rintro ⟨a, xs⟩ s he ⟨h0, h1⟩\n  nocompiler_auto f_func s he\n"),
        "{sk}"
    );
    assert!(sk.contains(&format!(
        "    loop_inv 0x{:x} (fun u => ∃ k, u.reg 13 = BitVec.ofNat 64 k\n        ∧ k ≤ xs.length)\n      measure (fun u => (u.reg 11).toNat)\n",
        nocompiler::asm::DEFAULT_TEXT + 8
    )), "{sk}");
}

/// The assembled binary runs: hello from its own listing, under qemu.
#[test]
fn assembled_hello_runs() {
    let qemu = std::env::var("QEMU_RISCV64").unwrap_or_else(|_| "qemu-riscv64".into());
    let have = std::process::Command::new(&qemu)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    if !have {
        eprintln!("SKIP assembled_hello_runs: no {qemu} (set QEMU_RISCV64)");
        return;
    }
    let bytes = std::fs::read(root().join("examples/elf/hello.elf")).unwrap();
    let a = assemble(&listing(&nocompiler::load(&bytes).unwrap())).unwrap();
    let dir = std::env::temp_dir().join(format!("nocompiler-asm-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let p = dir.join("hello.elf");
    std::fs::write(&p, write_elf(&a).unwrap()).unwrap();
    use std::os::unix::fs::PermissionsExt as _;
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
    let o = std::process::Command::new(&qemu).arg(&p).output().unwrap();
    let want = std::process::Command::new(&qemu)
        .arg(root().join("examples/elf/hello.elf"))
        .output()
        .unwrap();
    assert!(o.status.success(), "{o:?}");
    assert_eq!(o.stdout, want.stdout);
    let _ = std::fs::remove_dir_all(&dir);
}
