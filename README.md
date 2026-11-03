# e5r: Assembly-Level Formal Verification with Lean 4

**e5r** proves properties of the machine code a compiler actually emitted, not
of the source it came from. The input is the assembly: an NVIDIA PTX kernel,
or the bytes of a firmware ELF. The output is a theorem the Lean 4 kernel has
checked, or a counterexample the Lean kernel has replayed, or a verdict that
says neither was obtained. The compiler, the source language and the model or
person who wrote the code are not trusted.

```bash
# Prove a PTX kernel memory-safe, race-free and correct against its spec.
e5r-verify ptx check saxpy_f32.ptx --spec saxpy_f32.json --out result.json
echo $?                                   # 0 proved, 1 refuted, 2 unsupported, 3 unknown

# A kernel the automation cannot handle: supply your own Lean proof.
# The tool writes the statement; your proof must prove exactly that.
e5r-verify ptx check kernel.ptx --spec kernel.json --proof Proof.lean

# Check a proof job against a firmware binary for one RISC-V board.
e5r-verify check verification/rv32/jobs/hifive1-duty.json --out duty.json
e5r-verify verify-result duty.json        # refuses a result whose inputs changed
```

e5r grew out of a binary analysis toolkit (disassembler, decompiler, binary
differ), which still ships as the `e5r` binary and is the development
infrastructure the verifier is built and debugged with. It is described in
[section 7](#7-development-infrastructure-the-e5r-toolkit). No output of it,
decompiled C, recovered control flow or IR, is an input to any proof.

---

## 1. What is proved

"Proved" means checked by the Lean kernel, with only `propext`, `Quot.sound`
and `Classical.choice` among the axioms of every declaration audited. No
`sorry`, `native_decide` or `bv_decide`.

### NVIDIA PTX kernels ([docs/verification-ptx.md](docs/verification-ptx.md))

For a `.ptx` kernel and a JSON spec, `e5r-verify ptx check` proves, for every
launch the spec allows, every initial memory and register content and every
interleaving of the threads:

- memory safety: no fault, no access outside the allocations, no misaligned access;
- termination;
- race freedom;
- functional correctness: every output element is what the spec says, and no
  other byte changes.

| Kernel class | State |
| --- | --- |
| `map32`, elementwise maps over 32-bit arrays (one element per thread, or a grid-stride loop) | Automatic. 102 of 104 model-written kernels proved; the other 2 are outside the instruction subset |
| `reduce32`, `scan32`: block reductions and scans with `.shared`, `bar.sync` and atomics | Automatic. nvcc's tree reduction (every power-of-two block up to 1024), Hillis-Steele scan (every block up to 1024) and atomic reduction proved |
| `accum`: one atomic per element (`add and or xor`, signed and unsigned `min max`, 32 and 64 bit) | Automatic. 16 nvcc kernels proved |
| `.f32` maps, correctly rounded operations (every rounding modifier, `.ftz`, `.sat`) | Automatic, bit-exact up to NaN payloads. nvcc's `fma.rn` saxpy and 16 model-written float kernels proved |
| Anything else in the subset | A supplied Lean proof, checked by `--proof` against the generated statement |

The current numbers from `./scripts/recheck-ptx.sh`: 26 benchmarks proved, 3
refuted, 2 unsupported, all as expected. 0 of 59 mutants proved (58 refuted
with a replayed counterexample, 1 unknown). The Lean model, a Rust
interpreter and an NVIDIA A10G agree on all 1,693 differential-test launches,
bit for bit.

Defects it found that nobody planted: kernels that take the length as `int`
and silently drop every element when `n ≥ 2^31`, and a reduction that returns
before `__syncthreads`. The GPU tests passed all of them.

Not covered, and refused or reported as `unknown` rather than proved:
`atom.exch` and `atom.cas`; float error bounds against exact arithmetic;
float reductions; `.f64` maps; approximate instructions (`sin.approx`,
`rcp.approx`, ...); `add`/`sub`/`mul.f32` without a rounding modifier, which
ptxas may fuse; PTX-to-SASS compilation. The full list and the reasons are in
the doc's "Open" section.

### RISC-V firmware binaries ([docs/firmware-verification.md](docs/firmware-verification.md))

One board: SiFive HiFive1 Rev B (RV32IMAC, M-mode, interrupts, CLINT, UART,
PWM), with the semantics validated against QEMU on a 62,773-step whole-firmware
replay. The proof subject is the flash image built from the ELF bytes.

| Result | State |
| --- | --- |
| A clamp binary, for all 2^32 inputs | Proved |
| The `duty()` contract of an Embassy firmware binary | Proved |
| Soundness of the whole-firmware certificate checker | Proved |
| Whole-firmware safety theorem for the Embassy example | **Not proved**: no certificate small enough yet |

The same machinery has machine-code proofs for parts of the
[RMK](https://github.com/rmk-rs/rmk) keyboard firmware on QEMU `virt`
(memmove, the COBS decoder, the deframer): see
[docs/rmk-checkpoint.md](docs/rmk-checkpoint.md). That is not a proof of RMK.

---

## 2. What you have to trust

A theorem is only as good as its statement and its model of the machine.
e5r keeps both small and says where they are:

- **The Lean kernel** and the statement. For `ptx check` the statement is a
  class theorem plus the definitions generated from your spec, which the
  result prints as `lean_spec` so a person can compare it with the JSON. A
  weak spec proves a weak property.
- **The ISA semantics**, written from the PTX ISA manual and the RISC-V
  specifications, and tested against hardware: the A10G for PTX, QEMU for the
  board. Float rounding is also proved equal to an independent formalization,
  [lean-ieee754](https://github.com/tunnellm/lean-ieee754).
- **Stated assumptions**, for example that PTX's memory model gives
  sequentially consistent results for kernels with no conflicting accesses,
  and that ptxas does not change an instruction with an explicit rounding
  modifier.

Not trusted: the tactics, the proof generator, the counterexample search and
the interpreter. They build proof terms the kernel checks, or counterexamples
the kernel replays.

Each doc has the full list: [PTX](docs/verification-ptx.md#assumptions-and-trusted-base),
[firmware](docs/firmware-verification.md).

---

## 3. Install

The verifier is built from source; release archives carry only the `e5r`
toolkit binary so far.

```bash
cargo build --release -p e5r-verify          # ./target/release/e5r-verify
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

The Lean projects pin their toolchains (`verification/ptx/lean-toolchain`,
core Lean v4.35.0, no Mathlib). PTX differential testing needs an NVIDIA GPU
and the CUDA toolkit; firmware replay needs QEMU. Each doc lists the exact
versions.

---

## 4. Verify a PTX kernel

A spec names the arrays, the output and what each element must become:

```json
{ "schema": "e5r.ptx.spec.v1", "kernel": "saxpy_f32", "class": "map32",
  "element_type": "f32",
  "arrays": ["saxpy_f32_param_1", "saxpy_f32_param_2"],
  "output": "saxpy_f32_param_2", "length": "saxpy_f32_param_3",
  "scalars": ["saxpy_f32_param_0"],
  "element": "fma.rn(saxpy_f32_param_0, saxpy_f32_param_1, saxpy_f32_param_2)",
  "result": "bit_exact",
  "schedule": { "kind": "guarded", "max_threads": "2^32" } }
```

```bash
cd verification/ptx/benchmarks
e5r-verify ptx check correct/float/saxpy_f32.ptx --spec specs/saxpy_f32.json
e5r-verify ptx check buggy/vadd_nobound.ptx --spec specs/vadd.json   # refuted: out-of-bounds load
```

The result is versioned JSON (`e5r.ptx.result.v1`): the verdict, each
property's status, the theorem and its axioms, or the counterexample (fault,
race, wrong value or a changed byte outside the output) with the launch that
triggers it. Only `proved` exits 0. A timeout or a memory cap gives
`unknown`, never `proved`.

---

## 5. Verify a firmware binary

A job file names the ELF, the board, the property and the entry or boot
model. The result is bound to the hashes of all of them and of the
toolchain, and a stale one is refused.

```bash
e5r-verify check verification/rv32/jobs/hifive1-clamp32.json --out clamp.json
e5r-verify bundle verification/rv32/jobs/hifive1-clamp32.json --out clamp-bundle
cd clamp-bundle && ./recheck.sh        # Lean only, offline
```

---

## 6. Recheck everything

```bash
./scripts/recheck-ptx.sh                     # PTX: parser, Lean build, audit, benchmarks, mutants, GPU difftest (~90 min)
./scripts/check-firmware-verification.sh     # firmware: rebuild from source and recheck
```

Lean runs with two threads under a memory cap; see the docs for the
overrides.

---

## 7. Development infrastructure: the `e5r` toolkit

The verifier needs to read binaries, decode instructions and find out what a
compiler did. That tooling is a reverse engineering toolkit in its own right,
and it ships as the `e5r` binary: ELF, PE and Mach-O loaders, x86-64,
AArch64, ARM32 and i386 decoders, a SLEIGH runtime, an IR with dataflow, a
decompiler to C, a binary differ, and an annotation log that merges with
`git merge`. Every command takes `--json`.

```bash
e5r info ./a.out                    # container, architecture, entry, warnings
e5r funcs ./a.out                   # every function, with the evidence for each boundary
e5r disas ./a.out main              # a function, an address, a range, or `all`
e5r decompile ./a.out main          # pseudo-C
e5r xrefs ./a.out 0x4006e8          # who reaches this, and how
e5r diff ./old ./new                # which functions changed, and what changed inside
e5r annotate ./a.out name 0x4006e8 parse_header
e5r ui                              # local read-only dashboard over a project
```

```bash
curl -fsSL https://raw.githubusercontent.com/h5i-dev/e5r/main/install.sh | sh
```

[MANUAL.md](docs/MANUAL.md) is the command reference,
[docs/tutorial.md](docs/tutorial.md) a walkthrough, and
[docs/scorecard.md](docs/scorecard.md) every measured number, including the
bad ones. The decompiler scores 23.4 union on DecBench against IDA's published
47.9 ([docs/decbench.md](docs/decbench.md)); it is a debugging aid here, not
the product.

---

## 8. Build

The checkout is release-only; see [`CLAUDE.md`](CLAUDE.md).

```bash
cargo build --release
./scripts/build-fixtures.sh       # the corpus the toolkit's gates measure against
cargo test --release --workspace
```

---

## 9. Documentation

Verification:

- [docs/verification-ptx.md](docs/verification-ptx.md): PTX kernels: model, classes, spec format, command line, trusted base, open items
- [docs/firmware-verification.md](docs/firmware-verification.md): firmware for the HiFive1 Rev B: scope, guarantees, assumptions, trusted base
- [docs/firmware-verification-install.md](docs/firmware-verification-install.md): installing the firmware toolchain
- [docs/rmk-checkpoint.md](docs/rmk-checkpoint.md): RMK machine-code proofs, replay commands and open boundaries
- [docs/verification-rv32.md](docs/verification-rv32.md): the RV32I research proofs the firmware work grew from

Project:

- [docs/ROADMAP.md](docs/ROADMAP.md): scope, milestones and what will not be built
- [CONTRIBUTING.md](CONTRIBUTING.md): what a change has to measure, and the clean-room rule
- [docs/design/](docs/design/): one document per toolkit subsystem

---

## 10. FAQ

<details>
<summary>Why verify assembly instead of source?</summary>

Because the assembly is what runs. A proof about CUDA C or Rust trusts the
compiler that lowered it, and a proof about a model's intermediate output
trusts the model. Verifying the emitted PTX or firmware bytes removes both
from the trusted base. It also catches what the source hides: the nvcc `vadd`
proof needed three preconditions, each a real limit of the PTX nvcc emitted,
such as a 32-bit signed index that wraps above 2^31 threads.

</details>

<details>
<summary>Who writes the specs and the proofs?</summary>

The spec is written by a person or an agent; it is the one thing a reader has
to check. For the supported classes nobody writes a proof: the class theorem
is proved once in Lean, and `check` discharges the per-kernel obligations
with tactics whose output the kernel checks. Outside the classes, a person or
an agent writes the proof and `--proof` checks that it proves exactly the
statement the tool generated.

</details>

<details>
<summary>Does a proved kernel run correctly on the GPU?</summary>

It runs correctly on the PTX semantics in the model, which agrees with the
A10G on every differential test so far. Compilation from PTX to SASS by ptxas
or the driver is outside the proof, and only the A10G has been tested.

</details>

---

## 11. History

e5r began as a C++ teaching disassembler for x86-64, then became a reverse
engineering toolkit for AI agents, and in October 2026 grew the Lean 4
verifier that is now its main purpose. The old code is in the git history,
and its x86-64 and ELF notes are kept at
[`docs/x86-64-notes.md`](docs/x86-64-notes.md).

---

## 12. License

Apache-2.0. See [LICENSE](LICENSE).
