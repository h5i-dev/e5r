# What a result depends on

A theorem such as `Examples.Sum.sum_verified` is checked by the Lean kernel.
Believing what it says about the binary on disk running on a machine means
trusting the following, and nothing else.

## Trusted

| What | Where | How it is checked |
| --- | --- | --- |
| The Lean 4 kernel (v4.35.0) | `lean/lean-toolchain` | The kernel is small and widely used; `lean/Audit.lean` fails the build if a listed theorem uses an axiom beyond `propext`, `Classical.choice` and `Quot.sound` |
| Instruction decoding | `lean/NoCompiler/Isa.lean` | Against llvm-mc (`crates/nocompiler/tests/decode.rs`, through the Rust decoder) and against the Rust decoder directly (`crates/nocompiler/tests/semantics.rs`) |
| Instruction semantics | `lean/NoCompiler/Machine.lean` | Against qemu-riscv64 (`crates/nocompiler/tests/semantics.rs`) and against the official Sail RISC-V model's C emulator (`crates/nocompiler/tests/sail.rs`), each on random programs over every instruction |
| The machine model | `HwStep` in `lean/NoCompiler/Step.lean` | By reading: fetch from memory, decode, execute, or hand ECALL to the environment |
| The environment model | `lean/NoCompiler/Env.lean` | By reading against the Linux syscall ABI; its assumptions are listed in [environment.md](environment.md) |
| The meaning of the definitions a theorem is stated with | `Reach`, `Exec`, `Spec`, `VerifiedImg`, `Preserved`, `Entry` | By reading [spec.md](spec.md) and the files |
| The specification of the function | e.g. `spec` in `lean/Examples/Sum.lean` | By reading: it is the claim |
| That memory holds the image at entry, and the function's writable memory does not overlap the code | `Code.Loaded`, `Protected` | Hypotheses of `VerifiedImg.hw`; the loader maps `.text` read-only and executable |
| That memory holds a data section a proof reads from | `Segment.Loaded` (`lean/NoCompiler/Image.lean`), as a precondition | The loader maps the section; the audit checks the exported bytes are the file's |
| The hardware or emulator implementing RV64IM, Zba and Zbb as the specification says | | Outside nocompiler |

## Not trusted

- **The compiler.** Proofs are about the instructions it emitted. A
  miscompilation makes a proof fail, not succeed.
- **Whoever or whatever wrote the code or the proof.** The kernel checks the
  proof.
- **The `nocompiler` tool** (`crates/nocompiler`): its ELF reader, decoder, profile
  checker, structure recovery and Lean exporter. The exporter writes the raw
  `.text` words and the bytes of every data section. Each `instr_<addr>`
  lemma it writes is proved by `rfl`, that is by the kernel evaluating the
  Lean decoder on the word. `nocompiler-audit` re-reads the ELF file with the Lean
  ELF reader (`lean/NoCompiler/Elf.lean`) and checks that its `.text` is word for
  word the image the proof uses, and every allocated data section
  (`.rodata`, `.data`, `.bss`, ...) byte for byte its exported `Segment`.
- **`.nocompiler.struct`**, and the Rust profile checker: they make proofs easier
  to write. A proof about a binary that breaks the rules is still a proof.
  Where conformance itself is the claim, the Lean checker
  (`lean/NoCompiler/Struct.lean`) decides rules R1 to R3 in the kernel
  (`<name>_checked`), and `Struct.cfi` proves what they mean for control flow.
- **The tactics** (`lean/NoCompiler/Tactic.lean`): a tactic that does the wrong
  thing produces a term the kernel rejects.
- **The program logic** (`Reach.bind`, `Reach.loop`, `VerifiedImg.call`, and
  the rest): proved from the definitions.
- **The adequacy theorems** (`lean/NoCompiler/Adequacy.lean`): proved, once, for
  every program.

## Extensions outside the profile

`lean/NoCompiler/Ext/Rvc.lean` extends the semantics to compressed (RVC) code, for
the comparison in [examples/demo/README.md](../../examples/demo/README.md): `decodeC`,
`CCode.instr` and `execC` are trusted *for the results stated with
`VerifiedC`*, and are checked against llvm-mc (every 16-bit word) and qemu
(the demo's compressed binary). Results about nocompiler binaries (`VerifiedImg`) do
not depend on it. The adequacy theorems are not proved for it.

## Known gaps

- The link between the ELF file and the process image (that the loader maps
  `.text` at its address) is an assumption, `Code.Loaded`.
- The semantics are tested against the Sail model, not proved equal to it.
  The test runs the C emulator generated from Sail (release
  2026-11-16-a2ad4b5) on random programs; it covers what the programs
  exercise, every instruction with chosen and random operands, not every
  state. Proving `NoCompiler.exec` equal to the Lean that Sail's Lean backend
  generates is on the [roadmap](../ROADMAP.md); it needs the Sail toolchain
  (OCaml, opam) built here, and the generated model is large.
