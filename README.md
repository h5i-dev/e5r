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

## Formally verified in Lean 4

The kernel checks all of these. They use only the standard axioms, except the `bv_decide` tier below ([lean/Audit.lean](lean/Audit.lean)).
Each also trusts what [trust.md](docs/isa/trust.md) lists: the kernel, the semantics, the machine and environment models, and the spec.

- **Example functions.**
  - `sum_verified`: the sum of an array, as clang `-O2` compiled it.
  - `sum2_verified`: a caller with a frame, proved from `sum`'s spec alone.
  - `write_all_verified` and `hello_verified`: a `write` loop over short writes, and a program that exits.
  - The audit checks each image against the committed ELF, byte for byte.
- **Adequacy** ([Adequacy.lean](lean/NoCompiler/Adequacy.lean)), proved once for all programs.
  - On the real fetch-from-memory machine, the function never faults, ends in its postcondition and terminates.
  - It assumes the image is loaded and writable memory does not overlap the code.
- **Structured control.**
  - `Struct.cfi`: every control transfer of a checked function is structured (R1–R3).
  - `Struct.level … = some .l2` adds the frame rules R4–R6 ([Frame.lean](lean/NoCompiler/Frame.lean)). All 11 committed functions reach L2.
- **Relocatable proofs.**
  - `sum_relocatable` holds at every layout. It comes from the fixed-address proof via `VerifiedImg.shift`.
  - Leaf functions only. `sum2` is proved at two links with one proof text, not at every layout.
  - The audit checks each linked ELF against its module.
- **Refinement** ([refine.md](docs/isa/refine.md)).
  - `Refines sp A B` makes A the spec: where A runs safely, B runs safely and ends as A can.
  - `Refines.verified` turns a proof about A into one about B.
  - Lockstep certificates and straight-line equivalences are checked in the kernel.
  - Loop-reshaping edits are not covered yet.
- **`bv_decide` tier.** Some straight-line equivalences use `bv_decide`. Its check runs native code, so the audit lists these theorems separately.
- **The demo.** Profile builds (`sum_b`, `cobs_b`) and rv64gc builds (`sum_a`, `cobs_a`).
  - The rv64gc proofs also trust the compressed-instruction extension (`Ext/Rvc.lean`).
  - That extension is tested against llvm-mc and qemu. It has no adequacy theorem yet.

[Docs](docs/README.md) · [Roadmap](docs/ROADMAP.md) · [Contributing](CONTRIBUTING.md) · Apache-2.0
