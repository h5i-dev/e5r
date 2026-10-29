# Binary-level RV32I verification research

The proof subject is a particular loaded ELF image and the instructions fetched
from it. e5r's decompiler, CFG recovery, IR and SLEIGH decoder are not proof
inputs. This is the owner-authorized V0 research exception in the roadmap, not
a claim to verify Rust, its compiler, a CPU or Embassy.

## Reproduce

From the repository root, install Lean using elan and the pinned
`verification/rv32/lean-toolchain`. Install GNU RISC-V binutils 2.42 and QEMU user
8.2.2; install Rust 1.98.1 and its bare-metal target:

```sh
rustup toolchain install 1.98.1 --profile minimal
rustup target add --toolchain 1.98.1 riscv32i-unknown-none-elf
./scripts/check-lean-rv32.sh
CARGO_BUILD_JOBS=1 cargo test --release -p e5r-verify
cargo fmt -p e5r-verify --check
CARGO_BUILD_JOBS=1 cargo clippy --release -p e5r-verify --all-targets -- -D warnings
```

`CROSS_COMPILE` selects the binutils prefix (default
`riscv64-linux-gnu-`); `QEMU_RISCV32` selects the QEMU executable. Tool versions
are checked against `verification/rv32/toolchain.json`. The current machine uses
Ubuntu binutils `2.42-4ubuntu2.10` and qemu-user `1:8.2.2+ds-0ubuntu1.18`, locally
extracted without system installation. To use those downloaded prerequisites:

```sh
tools_root="$HOME/.local/state/e5r-lean-agent-20261028/tools/root"
export PATH="$tools_root/usr/bin:$PATH"
export LD_LIBRARY_PATH="$tools_root/usr/lib/x86_64-linux-gnu${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
./scripts/check-lean-rv32.sh
```

The runner builds serially, checks Lean with one worker and a 4096 MB allocation
budget plus a Linux `/proc` watchdog at 5 GiB resident memory, regenerates all
local Lean modules and audits every theorem. It uses
`decide +kernel`, ordinary kernel reduction. It does not invoke native proof
evaluation or accept unchecked computation results. The original direct
`decide` experiment used excessive elaborator memory and was stopped; direct
kernel reduction checked the assembly theorem in about 22 seconds with 2.1 GiB
peak RSS before limiting Lean to one worker. A direct attempt to prove the
deliberately false mutation control expanded diagnostics beyond the allocation
budget and was stopped. The final control rewrites with the already proved
mutation-rejection theorem and requires Lean to reject the resulting small
`false = true` claim; the watchdog also guards every Lean invocation.

Build artifacts go in `verification/rv32/build/` (ignored). They must not go
under `fixtures/build/`: the corpus-gated workspace tests treat that directory's
existence as "the fixture corpus was built". Generated Lean image/oracle
modules and oleans are ignored. `provenance.json` records full tool versions,
exact fixture build commands, ELF and generated-image hashes and byte lengths.
The runner also enforces the reviewed ELF identities in
`verification/rv32/identities.json`; changing a fixture requires reviewing and
updating those pins.
`axioms.txt` records the theorem audit. `check.log` can be captured by redirecting
the runner's output. Re-running rebuilds the artifacts and rechecks the proofs;
no checked result is inferred from an existing olean or a checksum alone.

## Layout and subjects

| Path | Role |
| --- | --- |
| `crates/e5r-verify` | Strict static ELF export using the existing e5r loader |
| `verification/rv32/Theories/RV32.lean` | Memory, byte fetch, word decoding and instruction execution |
| `verification/rv32/Theories/ELF.lean` | Independent bounded ELF32 memory-image reader |
| `verification/rv32/Projects/ClampSpec.lean` | Shared exact output, access, reachability and frame specification |
| `verification/rv32/Projects/clamp` | Original assembly, linker recipe and proofs |
| `verification/rv32/Projects/rust_clamp` | Original `no_std` source, O1/O2 binary proofs |
| `verification/rv32/Negative.lean` | Kernel-checked fault and image-mismatch controls |
| `verification/rv32/tools` | Deterministic generation, QEMU observation and checking |

Assembly is built with `-march=rv32i -mabi=ilp32` and linked as `elf32lriscv`
with relaxation disabled. Rust is compiled directly with pinned `rustc`, the
`riscv32i-unknown-none-elf` target, `panic=abort`, static relocation and the same
linker script, at optimization levels 1 and 2. This avoids a Cargo dev-profile
fixture build. The generated provenance file contains every argument. With the pinned tools,
O1 and O2 currently produce identical 628-byte ELF artifacts; this is two build
configurations, not evidence from different code layouts. The reviewed SHA-256
identities are:

| Fixture | SHA-256 |
| --- | --- |
| Assembly | `5a761b6c645f001bcecf2b35c9b18556bce4abc040bac33816e958cceae70b8a` |
| Rust O1 and O2 | `f45123ac930aa252fb0a9d8f625ffca00cae05338a1e0c92d60142c1497b7e6c` |

The strict exporter accepts ELF32 little-endian RISC-V ET_EXEC with zero
`e_flags`. It refuses loader warnings, relocations, dynamic/interpreter/TLS
segments, imports, overlapping mappings, empty or oversized segments, writable
executable memory and an unaligned/non-executable entry. File and total mapped
sizes are capped at 64 KiB. It exports zero-filled tails as memory bytes and
annotates each region with its PT_LOAD file offset, file length and memory
length. It never exports an instruction AST or inferred function boundary.

## What is proved

The common precondition is an unsigned input `n < 256`. The entire loaded image
is fixed; the four bytes at `0x2000` are replaced with the little-endian word
`n`. All 32 registers start at zero, the PC is the ELF entry, and the access
trace starts empty. There are no asynchronous events or external memory writes.
This is a small explicit bare-metal entry ABI, not an arbitrary Rust caller ABI.

`Clamp.bounded_safety`, `RustO1.bounded_safety` and
`RustO2.bounded_safety` establish `Clamp.Ensures` for every such natural-number
input. `Ensures` requires existence of a successful execution, with these facts:

- Assembly reaches PC `0x101c` after 1 through 7 instruction transitions;
  each Rust binary reaches PC `0x1000` after 1 through 9 transitions.
- The word stored at `0x2004` is exactly `min(n + 7, 100)`, hence at most 100.
- The data-access trace is exactly a word load from `0x2000` followed by a word
  store to `0x2004` with that value. The accessed byte ranges are consequently
  `0x2000..0x2003` and `0x2004..0x2007` in their declared mappings.
- The final memory is exactly the initial memory with only that output word
  changed, including preservation of all instruction bytes and permissions.
- Register x0 reads as zero, and the endpoint has execute permission and
  contains the actual idle `jal x0, 0` word.

Both sides of the clamp branch are covered. The finite universal statements
are kernel checked over all 256 inputs; they are not random testing.
`Clamp.check_sound` connects their executable Boolean predicate to the explicit
existential proposition above. No statement treats a fault as a successful
execution. The endpoint is an observation boundary before an idle self-loop,
not normal machine shutdown or a proof that firmware globally terminates.
These proofs do not cover all 32-bit inputs, arbitrary initial registers,
arbitrary images or behavior after that boundary.

Each project's `image_fidelity` also establishes that the independent Lean ELF
reader reconstructs exactly the entry and memory image exported by e5r from the
original file-byte literal. The runner parses that literal from the actual Lean
source and compares it with every input ELF byte. SHA-256 supplies a convenient
identity record, not a substitute for this correspondence check.

## Execution model

The whitelist is LUI, AUIPC, ADDI, ADD, SUB, BEQ, BNE, BLT, BGE, BLTU, BGEU,
LW, SW, JAL and JALR. This is a bounded RV32I **subset**, not full RV32I or
RV32IMC. Other integer operations, byte/halfword memory instructions, M, C,
fences, ECALL, privilege/CSR and floating point are unsupported faults.

Values and PCs wrap modulo 2^32. Reads and writes of x0 enforce its special
rule. Immediate extraction/sign extension uses the instruction encoding;
signed and unsigned branch comparisons are distinct. Branch/JAL targets must
be four-byte aligned. JALR clears bit zero before enforcing that alignment.
An untaken conditional branch does not check target alignment. LW/SW require
four-byte alignment, an explicit execution-environment choice permitted by the
ISA. Fetch checks execute permission on all four bytes; loads check read and
stores check write permission. Out-of-map accesses, out-of-address-space bytes,
invalid byte values on reads, alignment, permission, unsupported decoding and exhausted
fuel are errors. Stores return a new memory value only if all four bytes can
be written. The accepted image and its input/output updates preserve disjoint
bounded mappings; arbitrary malformed `State` values are not the theorem's
initial states.

This is a deterministic single-hart memory model. It has no OS, runtime,
MMIO, interrupts, exception handlers, DMA, caches, scheduler, timing or devices.
It models neither a board's bootloader nor any environment that modifies memory
concurrently. The ISA source is the official
[RV32I specification, version 2.1](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).
The model is original code written from the public specification, not copied
from another emulator or verifier.

## Tests, proofs and trust boundaries

The checked V0 run on 2026-10-28 audited 122 theorem declarations, including
94 differential comparison lemmas, and rejected the deliberately false
mutated-image claim.

The QEMU runner executes supported instructions in an independent RISC-V
implementation. A Linux-user wrapper initializes registers/data, executes the
candidate word, and writes observations through syscalls. The wrapper and
syscalls are outside the bare-metal proof model. Lean checks each observation
against `step`. Cases cover wraparound, signed extremes, immediate extremes,
x0, all six branches taken/untaken and backward, loads/stores with signed
offsets, upper immediates and jumps. Jump checks compare QEMU link observations
and independently assembled symbol-table target addresses with the model. This is differential testing of selected legal instruction behavior,
not a proof of ISA conformance or QEMU correctness. Negative model checks cover
unsupported C/M/CSR/ECALL/reserved encodings, missing/truncated instruction
memory, permission/alignment/bounds faults, invalid bytes, exhausted fuel,
fetch past the map, and changing an instruction in the original ELF.
Rust tests cover strict loading/export, zero fill, provenance, determinism,
truncation and unsupported headers. Neither test suite replaces the Lean proofs.

The trusted boundaries are explicit:

1. The Lean kernel and installed pinned core/Std environment check the proof
   terms. The axiom audit allows only `propext` and `Quot.sound`; image fidelity
   uses no axioms, finite execution uses `propext`, and the readable proposition
   theorem additionally uses `Quot.sound`. No project axioms or proof escapes
   are allowed. The runner scans local Lean source for escape declarations and
   audits every theorem's transitive axioms, refusing unrecognized output.
2. The original-file read, literal injection, runner, filesystem, tools and hash
   recording bind formal literals to the external files. These are not formally
   verified. The Lean image-equality theorem removes reliance on a hash or on
   e5r's loader alone for the checked image, but both ELF-reader specifications
   and the checking orchestration still need review. The minimal Lean reader
   models PT_LOAD and selected header checks, not the complete ELF standard.
3. The ISA/memory model and the exact specification are part of the semantic
   TCB. QEMU tests provide evidence about the model; no theorem proves its
   refinement to hardware or the official ISA specification.
4. Assemblers, linkers and Rust are artifact producers, not trusted source-level
   correctness arguments. The result applies to the emitted bytes. Connecting
   source contracts to them requires ABI and representation abstraction and
   proofs that the chosen initial machine states represent those contracts.

## Reference study and staged follow-ups

The supplied [Anthropic article](https://www.anthropic.com/research/formal-verification)
reports 123 libraries, 239 entry points and about 180 million Rocq lines for the
larger effort. The inspected public
[proof repository README](https://github.com/theorem-labs/oss-verify-proofs)
reports 26 libraries and 61 entry points; these are publication-scope counts,
not results reproduced here. Its separation of theories, projects, proofs,
toolchain, tools/oft and index informed the artifact organization. Its
[checking documentation](https://github.com/theorem-labs/oss-verify-proofs/blob/main/docs/checking.md)
describes statement matching and an assumption audit; its
[semantics documentation](https://github.com/theorem-labs/oss-verify-proofs/blob/main/docs/semantics.md)
explicitly limits the Linux process model. The
[enrollment repository](https://github.com/theorem-labs/oss-verify)
serves build/enrollment rather than this proof implementation. These primary
sources were inspected on 2026-10-28. No implementation, proof or Linux semantics
was copied or vendored; repository license labels do not imply that all their
artifacts can be reused without checking their own licenses.

Next steps are symbolic Rust range proofs over larger input domains, more
optimization levels and compiler versions, explicit ABI/representation lemmas,
a larger independently validated ISA subset, and strict well-formed-state
invariants. Only then extend to one Embassy executor with timer/channel and
explicit interrupt, MMIO/device, DMA and scheduling semantics. RV32IMC,
privilege/CSR, Cortex-M and temporal/deadline properties are separate stages.
Firmware and microkernel execution models replace Linux process semantics;
they do not remove the need to model the environment. Rewriting Embassy or Rust
runtime abstractions at source level is outside this milestone.
