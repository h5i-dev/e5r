# What a result depends on

A theorem such as `Examples.Sum.sum_verified` is checked by the Lean kernel.
Believing what it says about the binary on disk running on a machine means
trusting the following, and nothing else.

## Trusted

| What | Where | How it is checked |
| --- | --- | --- |
| The Lean 4 kernel (v4.35.0) | `lean/lean-toolchain` | The kernel is small and widely used. The axiom audit (`lake exe nocompiler-audit`, `lean/Audit.lean`) checks EVERY declaration of every module under `lean/NoCompiler`, `lean/Examples`, `lean/Demo` (found from the source tree, no list): it fails if one depends on `sorryAx` or on any axiom beyond `propext`, `Classical.choice`, `Quot.sound` other than the bv_decide tier's, and if a source file's module was not built. `lean/AuditControls/run.sh` (CI) shows a new `sorry` theorem fails it, a new `bv_decide` theorem is classified, and the debugging option of `nocompiler_auto` cannot pass. It also fails on any theorem under `Examples.` that concludes `RefinesRel` (alone or in a conjunction), a refinement without A's run (decision 3: state it as `Refines`), unless the project proves `¬ ARuns` of the same A (a vacuity control, `Examples/Refine/Vacuous.lean`); controls `refines-rel`, `refines-rel-and`, `refines` |
| **The bv_decide tier only:** Lean's compiled evaluation of `bv_decide`'s SAT-certificate checker | `bv_decide` (Std), used by `seq_equiv_bv` (`lean/NoCompiler/RefineStraight.lean`) | A theorem proved with `bv_decide` depends on an axiom of native computation (`<thm>._native.bv_decide.ax_*` in Lean 4.35; `Lean.ofReduceBool` / `Lean.trustCompiler` in earlier versions). The audit classifies every declaration automatically and prints the theorems of this tier at run time; every other theorem is in the kernel tier |
| Instruction decoding | `lean/NoCompiler/Isa.lean` | Against llvm-mc (`crates/nocompiler/tests/decode.rs`, through the Rust decoder) and against the Rust decoder directly (`crates/nocompiler/tests/semantics.rs`) |
| Instruction semantics | `lean/NoCompiler/Machine.lean` | Against qemu-riscv64 (`crates/nocompiler/tests/semantics.rs`) and against the official Sail RISC-V model's C emulator (`crates/nocompiler/tests/sail.rs`), each on random programs over every instruction |
| The machine model | `HwStep` in `lean/NoCompiler/Step.lean` | By reading: fetch from memory, decode, execute, or hand ECALL to the environment |
| The environment model | `lean/NoCompiler/Env.lean` | By reading against the Linux syscall ABI; its assumptions are listed in [environment.md](environment.md) |
| The process step | `PStep` in `lean/NoCompiler/Linux/Process.lean` | By reading: the process step (machine `exec` under `Kern.perm`, `ecall` by the Linux layer); `PStep.step` proves each step at the trusted syscalls is a `Step c k.perm` step |
| The meaning of the definitions a theorem is stated with | `Reach`, `Exec`, `Spec`, `VerifiedImg`, `Preserved`, `Entry` | By reading [spec.md](spec.md) and the files |
| `Layout` | `lean/NoCompiler/Module.lean` | By reading: an address per symbol, and the start and length in words of the code image. Check that a theorem's layout is the binary's: the audit compares it with the ELF's symbol table (below) |
| `Module.link` | `lean/NoCompiler/Module.lean` | By reading, or by the audit: the image is, word by word, the word of the function covering the address with its relocations patched (`Reloc.apply`: `auipc`/`jalr` pairs, `%pcrel_hi`, `%pcrel_lo` I and S), zero elsewhere. A wrong `link` makes the audit's comparison with the ELF's `.text` fail; it is trusted only as far as that comparison is (see "Compiled code") |
| `Module.Ok` | `lean/NoCompiler/Module.lean` | By reading: the conditions under which a layout is a linking at all: the image aligned and inside the address space, every function 4-byte aligned, inside the image and disjoint from the others, unique names, every relocation in `auipc` reach and inside its function. A theorem quantified over `M.Ok L` says nothing about layouts outside it |
| `Module.dom` | `lean/NoCompiler/Module.lean` | By reading: the code region of a function and of every function it reaches through calls (the call graph is acyclic in v1). `VerifiedImg`'s "stays in `D`" is relative to it: a function that jumps into code outside it ends the run there |
| `Module.Verified` | `lean/NoCompiler/Module.lean` | By reading: `spec : Layout → Spec α`, and for every layout with `M.Ok L`, `VerifiedImg (M.link L) (M.dom L f) (L.addr f) (spec L)`. The specification may name the layout's addresses (`L.addr "table"`): check what it says at the layout of the binary in question; a constant `fun _ => sp` says the same at every layout |
| `Refines` | `lean/NoCompiler/Refine.lean` | By reading: for entries A may be entered at with `sp.pre` and whose return address is outside B's code, IF A runs safely under `sp.perm` (an `Exec` of A, assumed), then B runs safely under the same permission and every final state of B has a run of A to a final state with the same observations (`Obs`). It assumes A runs; it is about B only relative to A (decision 3 of the review requires a theorem that A runs alongside every use) |
| `Obs` | `lean/NoCompiler/Refine.lean` | By reading: what a caller can see of a final state: the same events and exit status; on return also the pc, a0, a1, the preserved registers, and memory outside the callee's dead stack |
| `Run` | `lean/NoCompiler/Refine.lean` | By reading: some path of `Step`s inside `D` from `s` to `t` (one run exists; `Reach` is every run) |
| `Spec.avoid` | `lean/NoCompiler/Refine.lean` | By reading: `sp` with the extra precondition that the return address is outside a given region. A theorem about `sp.avoid DA` says nothing about entries whose return address lies in `DA` |
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
  (`lean/NoCompiler/Struct.lean`, `Frame.lean`) decides the rules in the kernel
  (`<name>_checked`), and `Struct.cfi` proves what they mean for control flow.
- **A function's level, by default.** `nocompiler export` writes the Rust
  checker's level of each function as a statement, `<name>_level : Prop`
  (`Struct.level … = some .l2`), with the exporter's version and the ELF's
  SHA-256 in the file's header, and proves nothing about it. A theorem that
  needs a level takes `<name>_level` as a hypothesis, never as an axiom (the
  audit fails on any axiom). So the default trusts the Rust checker only for
  level claims, and only where a reader takes such a hypothesis as discharged;
  no `VerifiedImg`, `Verified` or `Refines` theorem depends on a level (the
  step tactics, the explore path and the VC generator use none).
  `nocompiler export --lean-level-check` removes even that: it writes
  `<name>_checked`, the kernel's proof of the same statement. CI keeps it on
  for every committed image.
- **The tactics** (`lean/NoCompiler/Tactic.lean`): a tactic that does the wrong
  thing produces a term the kernel rejects.
- **The program logic** (`Reach.bind`, `Reach.loop`, `VerifiedImg.call`, and
  the rest): proved from the definitions.
- **The adequacy theorems** (`lean/NoCompiler/Adequacy.lean`): proved, once, for
  every program.

## Compiled code

Images in chunk format (`nocompiler export --format chunks`, `lean/NoCompiler/Image.lean`, "Code in chunks") are decoded in Lean (`Chunk.words`, `Segment.bytesOfNat`, `Struct.Cert.ofRuns`): the image a proof is about is the decoded `Code`, and the audit compares that decoded image with the ELF word by word and byte by byte (three of them are in its list: hello, cobs.b, sum.b). The decoders and the exporter are not trusted beyond that comparison. `Code.ofChunks_instr` (the image equals a chunk's own code on the chunk's range) is a theorem. A chunk image has no lemma per instruction: the step tactics get `code.instr pc = some i` from the simproc `chunkInstr` (`lean/NoCompiler/ImageSimp.lean`), which finds the chunk and `i` with compiled code (`evalExpr`) and proves the equation from `Code.ofChunks_instr` and `rfl` on the chunk; the kernel checks that proof, so the compiled code only proposes `i` (a wrong one is a proof the kernel rejects).

Some checks are not done by the kernel but by compiled Lean code (the Lean
compiler and runtime, and the C compiler it uses), and some by native
evaluation inside a proof:

- **The audit program** (`lake exe nocompiler-audit`, `lean/Audit.lean`), a
  compiled Lean executable. It
  - reads each committed ELF file with the Lean ELF reader (`lean/NoCompiler/Elf.lean`);
  - compares its `.text` word by word and every data section byte by byte
    with the image a proof is about (`Code`, `Segment`), for fixed images and
    for the compressed ones;
  - builds the ELF's layout from its symbol table, decides `Module.Ok` there
    (by the `Decidable` instance, evaluated by compiled code), and compares
    `Module.link` and `Module.segments` at that layout with the ELF's
    `.text` and data;
  - runs the axiom audit over every declaration of the project's modules.

  These verdicts are compiled evaluation of the same Lean definitions the
  theorems use, not kernel proofs: a theorem about an image is about the
  committed binary only as far as this program is right. Nothing in the
  theorems themselves depends on it.
- **The bv_decide tier**: the theorems the audit lists depend on Lean's
  compiled evaluation of the SAT certificate checker (an axiom of native
  computation in the theorem).
- **Kernel evaluation is not native**: `decide`, `decide +kernel` and `rfl`
  proofs (the `instr_<addr>` lemmas, `<name>_checked`, the refinement
  certificates) are checked by the kernel's own evaluator and need no axiom.
- **Not trusted at all**: the Rust tools (`crates/nocompiler`), which only
  produce what the kernel or the audit then checks.

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
