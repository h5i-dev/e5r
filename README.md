# nocompiler

`nocompiler` is a RISC-V profile in which machine code is proved correct in Lean 4, and nothing that produced the code or the proof has to be trusted.

**Motivation**

- Compilers, code generators and now LLMs write the code that runs. Which of them do you trust?
- A proof about the C source says nothing about the bytes the compiler emitted. Can the claim be about the bytes?
- Proofs about machine code are usually written once, by experts, for one binary at one address. Can they be routine?

**Our Answer**

- A subset of RV64 (RV64IM + Zba + Zbb) with structured control flow (a WebAssembly-style block/loop tree) and a fixed stack discipline. It is ordinary RISC-V: it runs unchanged on any RV64 Linux machine, follows the LP64 calling convention and links with ordinary code.
- One theorem per function, about the bytes of the binary: correct for every input its precondition allows, memory-safe, terminating, and it follows the calling convention.
- The Lean kernel is the only judge. The compiler, the tools in this repository, the tactics and whoever wrote the proof are all untrusted. What *is* trusted is listed in [docs/isa/trust.md](docs/isa/trust.md).
- Functions are checked against the profile at levels L0/L1/L2. Each level comes with theorems that are proved once for all programs, so less is left to each function's proof.

**Potential pushback**

- *"Is the proof actually shorter on the profile?"* → Not shown yet. In the [A/B demo](examples/demo/README.md), with the same automation, the proofs about the profile binary and about a plain rv64gc build of the same C are the same length (table below). What the profile changes, so far, is what the proof rests on: a block/loop structure the kernel has checked, no compressed-instruction semantics in the trusted base, and adequacy theorems linking the proof to the machine. The demo's functions are leaf functions without frames. The comparison with calls and frames (criterion 8 of [spec v1](docs/isa/v1.md)) is open, and until it is measured we make no "easier to prove" claim.
- *"Why not verify the C source?"* → Then the compiler, and the C semantics it implements, are part of what you trust, or you need a verified compiler. Here the claim is about the instructions that run. A miscompilation makes a proof fail; it cannot make one succeed.
- *"Isn't this NaCl / eBPF / WebAssembly?"* → It borrows from all three ([related work](docs/isa/related-work.md)). From NaCl, restrict the code so checking is easy. From eBPF, a verifier-style rule set. From WebAssembly, structured control flow, applied here to real RISC-V machine code with no new bytecode and no runtime. Nothing is enforced at load time. A function that breaks the rules still runs, and the guarantee comes from a proof, not from a checker.
- *"Why trust your semantics?"* → The decoder and semantics are hand-written in Lean for the subset. They are tested against llvm-mc (decoding), qemu-riscv64 and the official Sail RISC-V model's emulator (execution, on random programs over every instruction). They are tested, not proved equal to Sail. That proof is on the [roadmap](docs/ROADMAP.md).
- *"Does it run on real hardware?"* → The binaries are plain static RV64 Linux ELFs. In this repository they are run under qemu-riscv64 and the Sail emulator, not on silicon. The theorems assume a machine that implements RV64IM + Zba + Zbb as specified.
- *"What about libc and the heap?"* → Neither is modelled. Code is built `-ffreestanding -nostdlib`, and the environment model admits four syscalls: `read`, `write`, `exit` and `exit_group` ([environment.md](docs/isa/environment.md)). `mmap`/`brk` are on the roadmap. A heap model is out of scope for v1.

## CLI example

One binary, `nocompiler`. The core commands check, record and export a RISC-V binary for proof. The rest are a general binary analysis toolkit ([docs/toolkit/](docs/toolkit/README.md)) whose output is never an input to a proof.

```sh
cargo build --release -p nocompiler-cli                     # target/release/nocompiler

# The profile (cc needs clang and ld.lld)
nocompiler cc -O2 examples/sum.c -o sum.elf                 # compile into the profile, record its structure, check
nocompiler check examples/elf/sum.elf                       # the level of every function: L0, L1 or L2
nocompiler disasm examples/elf/sum.elf sum                  # the code, nested by its block/loop structure
nocompiler export examples/elf/sum.elf --namespace Examples.Sum.Image -o lean/Examples/Sum/Image.lean
nocompiler module examples/elf/sum.link1.elf --namespace Examples.Link.One   # the relocatable module and its layout

# The proofs, and the check that they are about the committed binaries
cd lean && lake build && lake exe nocompiler-audit && cd ..
scripts/core/check-proof-controls.sh                        # every mutated binary must break its proof

# The toolkit (any ELF, PE or Mach-O)
nocompiler funcs /bin/ls
nocompiler diff /bin/true /bin/false
nocompiler repl /bin/ls
```

## Measurements

Each number comes from the repository, with its source.

| What | Result | Conditions, source |
| --- | --- | --- |
| Proof size, `sum`: profile build vs rv64gc build | 12 vs 12 lines (168 vs 159 tokens) | same spec, same automation; [examples/demo](examples/demo/README.md) |
| Proof size, `cobs_decode` (in-place COBS decoding) | 95 vs 95 lines (1412 vs 1413 tokens) | same; specification lemmas shared and counted once |
| Lean check time, `cobs_decode` | 27.8 s vs 31.8 s | wall clock per file, shared machine, ±15%; same source |
| Corpus conformance | 58 functions: 54 at L2, 2 at L1, 2 at L0 | every C file in the repository through `nocompiler cc`, clang 15.0.7; [v1-results](docs/isa/v1-results.md), criterion 4 |
| Negative controls | 25 of 25 mutated binaries break their proofs | `scripts/core/check-proof-controls.sh` |
| Semantics vs qemu-riscv64 and vs Sail | identical register and memory dumps | 48 random programs per run each (default), every instruction of the profile; `crates/nocompiler/tests/{semantics,sail}.rs` |
| Relocation | one proof of `sum`, valid at every layout | two links (`.text` at 0x11190 and 0x40000); leaf functions only, functions with calls open; [v1-results](docs/isa/v1-results.md), criterion 3 |
| PTX kernels (experiment) | 102 `map32` kernels proved; 20 of 21 mutants refuted | [experiment/docs/ptx.md](experiment/docs/ptx.md) |

The full table of the spec v1 acceptance criteria, including the open ones, is in [docs/isa/v1-results.md](docs/isa/v1-results.md).

## Formally verified in Lean 4

All of the following are checked by the kernel with the standard axioms only ([lean/Audit.lean](lean/Audit.lean)). Unless stated otherwise, each trusts what [trust.md](docs/isa/trust.md) lists: the Lean kernel, the decoder and instruction semantics, the machine model `HwStep`, the environment model, and the definitions and specification the theorem is stated with.

- **The example functions.** `Examples.Sum.sum_verified` (the sum of an array, as clang `-O2` compiled it). `Examples.Sum2.sum2_verified` (a caller with a stack frame, proved from `sum`'s specification alone). `Examples.Hello.write_all_verified` (a `write` loop over short writes) and `hello_verified`. The audit checks that each image is byte for byte the committed ELF.
- **Adequacy.** `VerifiedImg.hw` and `Exec.hw_safe`, `hw_final`, `hw_terminates` ([Adequacy.lean](lean/NoCompiler/Adequacy.lean)), proved once for all programs: the machine fetching from memory never faults inside the function, ends in the postcondition, and terminates. These add the assumptions that the image is loaded and that writable memory does not overlap the code.
- **Structured control.** `Struct.cfi`: for a function whose `<name>_checked` the kernel has decided, every control transfer is structured (R1–R3). `Struct.level … = some .l2` adds the frame rules R4–R6 ([Frame.lean](lean/NoCompiler/Frame.lean)) and holds for all 11 functions of the committed images.
- **Relocatable proofs.** `Examples.Link.sum_relocatable : Verified One.module "sum" spec` holds over every layout. It is obtained from the fixed-address proof through `VerifiedImg.shift`, and it covers leaf functions only. `nocompiler-audit` checks that each linked ELF is its module linked at the ELF's layout.
- **The demo.** `sum_b`/`cobs_b` (profile builds, `VerifiedImg`) and `sum_a`/`cobs_a` (rv64gc builds, `VerifiedC`). The `_a` theorems also trust the compressed-instruction extension `Ext/Rvc.lean`, which is tested against llvm-mc and qemu, and they have no adequacy theorem yet.

[Docs](docs/README.md) · [Roadmap](docs/ROADMAP.md) · [Contributing](CONTRIBUTING.md) · Apache-2.0
