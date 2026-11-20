# nocompiler

`nocompiler` is a RISC-V profile whose machine code is proved correct in Lean 4.
Nothing that produced the code or the proof has to be trusted.

**Motivation**

- Compilers, code generators and LLMs write the code that runs. Which of them do you trust?
- A proof about C source says nothing about the emitted bytes. Can the claim be about the bytes?
- Machine-code proofs are usually one-off expert work. Can they be routine?

**Our Answer**

- A subset of RV64: RV64IM + Zba + Zbb, structured control flow, a fixed stack discipline.
- It is ordinary RISC-V. It runs on any RV64 Linux machine and follows the LP64 calling convention.
- One theorem per function, about the bytes: correct, memory-safe, terminating, ABI-preserving.
- The Lean kernel is the only judge. Compilers, tools, tactics and proof authors are untrusted.
- What is trusted is listed in [docs/isa/trust.md](docs/isa/trust.md).
- Functions are checked at levels L0/L1/L2. Each level brings theorems proved once for all programs.

**Potential pushback**

- *"Is the proof actually shorter on the profile?"* → No, as far as we have measured.
  - With equal automation, the profile build and a plain rv64gc build need proofs of the same length.
  - This holds for the leaf functions of the [A/B demo](examples/demo/README.md), and for `sum2` with calls and a frame (4 lines each).
  - We do not claim "easier to prove" on proof length ([v1-results](docs/isa/v1-results.md), criterion 8).
  - What changes is what the proof rests on: kernel-checked structure and frame rules, metadata for the code region, no compressed-instruction semantics, and adequacy theorems.
- *"Why not verify the C source?"* → Then you trust the compiler, or need a verified one.
  - Here the claim is about the instructions that run.
  - A miscompilation makes a proof fail. It cannot make one succeed.
- *"Isn't this NaCl / eBPF / WebAssembly?"* → It borrows from all three ([related work](docs/isa/related-work.md)).
  - NaCl: restrict the code so checking is easy.
  - eBPF: a verifier-style rule set.
  - WebAssembly: structured control flow, applied to real RISC-V with no bytecode and no runtime.
  - Nothing is enforced at load time. The guarantee comes from a proof, not a checker.
- *"Why trust your semantics?"* → They are tested, not proved.
  - The decoder and semantics are hand-written in Lean.
  - They are tested against llvm-mc, qemu-riscv64 and the Sail RISC-V emulator.
  - A proof of equality with Sail is on the [roadmap](docs/ROADMAP.md).
- *"Does it run on real hardware?"* → The binaries are plain static RV64 Linux ELFs.
  - Here they run under qemu-riscv64 and the Sail emulator, not on silicon.
  - The theorems assume a machine that implements RV64IM + Zba + Zbb as specified.
- *"What about libc and the heap?"* → Neither is modelled yet.
  - Code is built `-ffreestanding -nostdlib`.
  - The environment admits four syscalls: `read`, `write`, `exit`, `exit_group` ([environment.md](docs/isa/environment.md)).
  - `mmap`/`brk` are on the roadmap. A heap model is out of scope for v1.

## CLI example

One binary, `nocompiler`.
The core commands check, record and export a binary for proof.
The rest is a binary analysis toolkit ([docs/toolkit/](docs/toolkit/README.md)). Its output never enters a proof.

```sh
cargo build --release -p nocompiler-cli                     # target/release/nocompiler

# The profile (cc needs clang and ld.lld)
nocompiler cc -O2 examples/sum.c -o sum.elf                 # compile into the profile and check
nocompiler check examples/elf/sum.elf                       # the level of every function
nocompiler disasm examples/elf/sum.elf sum                  # the code as a block/loop tree
nocompiler export examples/elf/sum.elf --namespace Examples.Sum.Image -o lean/Examples/Sum/Image.lean
nocompiler module examples/elf/sum.link1.elf --namespace Examples.Link.One   # the relocatable module

# The proofs, and the check that they are about the committed binaries
cd lean && lake build && lake exe nocompiler-audit && cd ..
scripts/core/check-proof-controls.sh                        # every mutated binary must break its proof

# The toolkit (any ELF, PE or Mach-O)
nocompiler funcs /bin/ls
nocompiler diff /bin/true /bin/false
nocompiler repl /bin/ls
```

## Measurements

Every number comes from the repository.

| What | Result | Source |
| --- | --- | --- |
| `sum` proof: profile vs rv64gc | 12 vs 12 lines | same spec and automation; [demo](examples/demo/README.md) |
| `cobs_decode` proof: profile vs rv64gc | 95 vs 95 lines | same; spec lemmas counted once |
| `sum2` proof (2 calls, a frame): profile vs rv64gc | 4 vs 4 lines (+1 on rv64gc) | criterion 8, **not met**; [v1-results](docs/isa/v1-results.md) |
| Lean check time, `cobs_decode` | 27.8 s vs 31.8 s | wall clock, shared machine, ±15% |
| Hand proof → `nocompiler_auto` | `sum2` 193 → 5, `write_all` 84 → 16, `hello` 102 → 18 lines | both on the profile build; criteria 1–2 |
| Corpus conformance | 58 functions: 54 L2, 2 L1, 2 L0 | the C corpus via `nocompiler cc`; criterion 4 |
| Negative controls | 25 mutated binaries and 23 mutated specs all break their proofs | `scripts/core/check-proof-controls.sh`, `check-spec-mutations.py` |
| Round trip `asm(disasm(x))` | identical for 17 + 53 functions | every function at L1 or above; criterion 5 |
| Semantics vs qemu and Sail | identical dumps | 48 random programs per run; `crates/nocompiler/tests/` |
| Relocation | `sum`: one theorem for every layout. `sum2`: one proof text at two links | criterion 3 |
| PTX kernels (experiment) | 102 kernels proved; 20 of 21 mutants refuted | [experiment/docs/ptx.md](experiment/docs/ptx.md) |

All acceptance criteria, open ones included, are in [docs/isa/v1-results.md](docs/isa/v1-results.md).

## What the framework proves, once for every program

nocompiler is a framework, not a verified product.
Its value is the theorems below. Each is proved once and applies to every binary you verify with it.
All are kernel-checked with the standard axioms ([lean/Audit.lean](lean/Audit.lean)).
They trust only what [trust.md](docs/isa/trust.md) lists: the kernel, the RV64 semantics, the machine and environment models.

- **Your theorem holds on the real machine.** `Exec.hw_safe`, `hw_final`, `hw_terminates`, `VerifiedImg.hw` ([Adequacy.lean](lean/NoCompiler/Adequacy.lean)).
  - A proof about a function becomes a statement about the CPU fetching its bytes from memory.
  - It never faults, ends in its postcondition and terminates.
- **The checker's verdict is a theorem.** `Struct.cfi` ([Struct.lean](lean/NoCompiler/Struct.lean)), `Struct.level` ([Frame.lean](lean/NoCompiler/Frame.lean)).
  - If the kernel accepts a function at L1, every control transfer is structured (R1–R3).
  - At L2, the frame rules R4–R6 hold too.
- **Proofs can work on the structure, not the pc.** `SReach.sound`, `SExec.sound` ([SSem.lean](lean/NoCompiler/SSem.lean)).
  - A proof over the block/loop tree implies the machine-level result.
- **Proofs compose.** `VerifiedImg.call`, `VerifiedImg.frame` ([Spec.lean](lean/NoCompiler/Spec.lean)).
  - A caller uses only its callee's spec, never its code.
  - Memory a function may not write is unchanged when it returns.
- **Proofs survive linking.** `VerifiedImg.shift`, `Verified.of_leaf`, `Verified.mono` ([Relocate.lean](lean/NoCompiler/Relocate.lean)).
  - A leaf function's proof holds at every layout.
  - Adding modules keeps existing theorems.
  - Functions with calls: not yet at every layout.
- **An edited binary inherits the original's guarantees.** `Refines.verified`, `Refines.of_lockstep`, `RRegion.ok_of_seqEquiv` ([refine.md](docs/isa/refine.md)).
  - If B refines A, every proof about A is a proof about B.
  - Lockstep certificates and straight-line equivalences are checked in the kernel.
  - Loop-reshaping edits: not yet.

**What you prove per function:** a spec, one invariant per loop, and the facts about your algorithm.
`nocompiler_auto` does the rest. The audit then ties the theorem to the committed ELF, byte for byte.

**Not standard axioms:** some straight-line equivalences use `bv_decide`, whose check runs native code. The audit lists them separately.

**Examples** ([lean/Examples](lean/Examples), [examples/demo](examples/demo/README.md)): `sum`, `sum2` (calls, a frame), `write_all` and `hello` (syscalls), `cobs_decode`.
The demo also proves rv64gc builds. Those proofs trust a compressed-instruction extension and have no adequacy theorem yet.

[Docs](docs/README.md) · [Roadmap](docs/ROADMAP.md) · [Contributing](CONTRIBUTING.md) · Apache-2.0
