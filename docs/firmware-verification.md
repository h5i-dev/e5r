# Binary-level firmware verification (scope F)

e5r-verify proves safety properties of a firmware **binary** for one board.
The Lean kernel checks the proofs. The proof subject is the flash image built
from the ELF file's bytes. e5r's decompiler, CFG recovery and IR are not
inputs to any proof.

This document defines the supported scope. Milestone status is in
[ROADMAP.md, section F](ROADMAP.md#f-scoped-firmware-verification-2026-10-28-owner-authorization);
the V0 research proofs it grew from are in
[verification-rv32.md](verification-rv32.md).

## Status

| Result | State |
| --- | --- |
| Semantics for the scope (RV32IMAC, M-mode CSRs, interrupts, flash/RAM/devices) | Done; validated against QEMU (below) |
| `duty()` contract on the Embassy firmware binary (buffer loop, frame, source-level result) | Proved |
| Clamp binary for all 2^32 inputs, wraparound included | Proved |
| Verification jobs: CLI, structured results, stale-result detection, limits | Done |
| Soundness of the whole-firmware certificate checker (`E5R.AI.check_sound`) | Proved; kernel-replayed, standard axioms only |
| Hybrid composition: checker plus directly proved regions and masked summaries (`E5R.AI.check_sound_hybrid`) | Proved; standard axioms only |
| Machine-code summary of the firmware's channel ring-head update (`RingAI.spec_sound`, review worker) | Proved; used by the analyzer with `E5R_RING=1` |
| Two separate real binaries combining the checker with a direct summary (`demo_safe`, `loop_safe`) | Proved (labeled demos, not the Embassy firmware) |
| **Whole-firmware safety theorem for the Embassy example** (no escape from the model, every PWM duty ≤ 100) | **Not yet proved.** It needs a certificate for the firmware that the checker accepts; the analyzer does not yet produce one that is precise and small enough |

Nothing below claims more than this table. The function-level theorems are
about the emitted instructions of one function under its calling convention,
not about the firmware as a whole. That needs the whole-firmware theorem,
which would also cover interrupts arriving in the middle of the function.

## The supported configuration

| | |
| --- | --- |
| Board | SiFive HiFive1 Rev B: FE310-G002 SoC, one E31 hart |
| ISA | RV32IMAC + Zicsr + Zifencei, MRET, WFI |
| Privilege | Machine mode only |
| Boot | The board's bootloader jumps to `0x20010000` (ELF `e_entry`) in M-mode |
| Memory | 16 KiB DTIM RAM at `0x80000000`; the 4 MiB SPI flash after the 64 KiB bootloader, `0x20010000`-`0x203fffff` |
| Devices | CLINT (msip, mtimecmp, mtime), UART0, PWM0 registers as listed in the board file |
| Interrupts | Machine software, timer and external, CLINT mode |
| Toolchain | Rust 1.98.1, `riscv32imac-unknown-none-elf`, plain `cargo build --release` |
| Independent execution | QEMU 8.2.2 `-M sifive_e,revb=true` |

The single source for the memory map, registers, boot assumptions and
exclusions is the machine-readable
[`verification/rv32/boards/hifive1-revb.json`](../verification/rv32/boards/hifive1-revb.json).
The Lean board definition is generated from it by `tools/gen_board.py`. The
checker regenerates it and refuses to run if the committed copy differs.

Why this board: it is a real, widely available board; QEMU models it, so
there is an independent executable reference; the stable Rust target and
`riscv-rt` support it without patches; and its core has no caches, MMU, DMA
or second hart. The ESP32-C3 was considered and rejected. Its second-stage
bootloader, flash cache/MMU and the size of its HAL would put most of the
behavior that matters outside any model we could validate.

## What a guarantee says

A whole-firmware guarantee is a Lean theorem of this shape (`Theories/Platform.lean`). None is
proved yet; see the status table:

> For every machine state reachable from any boot state the board allows,
> through any sequence of instruction steps and interrupt entries and under
> any answers the environment gives:
>
> 1. the next transition cannot leave the modeled envelope: no architectural
>    exception (illegal instruction, misaligned access, ecall, ...) and no
>    behavior the model declines (an unmodeled address, CSR field or mode); and
> 2. every observable device write emitted so far satisfies the property
>    (for the Embassy example: every write to `pwm0.pwmcmp1` is at most 100).

"Any answers the environment gives" covers these choices:

- every device register read returns any 32-bit value;
- an enabled interrupt may be taken at any instruction boundary, whether or
  not the device has it pending;
- an SC with a reservation may succeed or fail.

These are deliberate over-approximations. Real hardware does fewer things,
so a property that holds for all of them holds on the board, as long as the
assumptions below hold.

Everything else fails closed. An access to an address the board file does
not list is `unsupported`, as is a CSR field outside the modeled subset or a
return to U-mode. The model never guesses a value. Unsupported behavior
reachable from boot means "no proof", not "safe".

## Boot assumptions

The theorem assumes these. Nothing checks them, so they belong to whoever
deploys the firmware:

1. The hart starts at the entry point in M-mode with `mstatus.MIE = 0`.
2. `mstatus` fields other than MIE, MPIE and MPP are zero (in particular MPRV).
3. No PMP entry is locked.
4. The flash holds exactly the ELF's `PT_LOAD` file bytes at their physical
   addresses, and nothing modifies flash while the firmware runs.
5. Only one hart runs. No debugger, DMA engine or other bus master touches
   memory or devices.

Everything else starts arbitrary: all registers, all of RAM, the remaining
CSRs within their implemented bits, the reservation and every device.

## Excluded

None of these is covered, and a result must not be read as covering them:

- **Not hardware safety in general.** The CPU and device behavior is a
  model. QEMU replay is evidence that the model is right, not a proof.
- **Not timing.** No cycle counts, interrupt latency, deadlines or liveness.
  A safety proof says nothing about whether a PWM write ever happens.
- Debug mode, NMIs, resets, watchdogs, bus errors on valid addresses, ECC and
  power events.
- U-mode, PMP restrictions, the PLIC's internal behavior, DMA and other harts.
- The bootloader, flash programming and the QSPI controller.
- Source-level claims. Neither Rust, its compiler, `riscv-rt` nor Embassy is
  verified. The theorem is about the emitted bytes, under the stated model.

## Trusted computing base

A guarantee rests on these. Each needs review, because none is proved:

1. The Lean 4.35.0 kernel and its core library, and the axiom audit, which
   allows only `propext`, `Quot.sound` and `Classical.choice`.
2. The semantics: `Theories/Hart.lean` (decoding and instruction meaning),
   `Theories/Platform.lean` (memory, devices, interrupts, reachability) and
   the generated board. They are written from the RISC-V specifications and
   the FE310-G002 manual. QEMU replay and differential tests are evidence for
   them, not proof.
3. The property statement for each target, and the boot assumptions above.
4. The binding from file to theorem. The exporter writes the ELF's bytes into
   Lean as a literal of the same buffer the runner hashed. An independent
   Lean ELF reader then derives the flash image from those bytes, and the
   image-fidelity theorem is proved by the kernel. Addresses a proof
   hard-codes are checked against the ELF's symbol table when the job pins
   them (`"symbols"`); that check is runner code, not a theorem. The
   runner, Python and the filesystem are not verified.
5. The runner's checks around the kernel. Every module is replayed through
   a fresh kernel (`leanchecker`) after it compiles, so a declaration added
   with kernel checking switched off is rejected however its source was
   written. The forbidden-word scan, the import check (every import must be
   a module the same job checked earlier) and the axiom audit are runner
   code.

The design of the ISA/memory split, the distinction between "the architecture
traps" and "the model declines", and frame summaries over regions follow
Theorem Labs'
[rocq-linux-process-semantics](https://github.com/theorem-labs/rocq-linux-process-semantics)
(MIT). That model is Rocq and describes a Linux process: no code or proof
from it is used here, and its process semantics supplies none of the
bare-metal interrupt, device or boot behavior modeled here.

## Running the checks

Installation on a fresh machine is in
[firmware-verification-install.md](firmware-verification-install.md). One
command rebuilds everything from source and rechecks it:

```sh
./scripts/check-firmware-verification.sh
```

It checks that the generated Lean boards match their JSON. It then runs
every job in `verification/rv32/jobs/` fresh and confirms each result is
current, and finally runs the negative controls and both QEMU differential
tests. Tool requirements are at the top of the script. CI runs the same
script in the `firmware-verification` job.

### Jobs

A job (`verification/rv32/jobs/*.json`, schema `e5r.verify.job.v1`) names:

- the ELF, how to build it, and its reviewed SHA-256;
- the board;
- the Lean modules, in dependency order;
- the theorems to audit (`Ns.*` means every theorem the modules declare in
  `Ns`);
- time and resident-memory limits.

```sh
target/release/e5r-verify check verification/rv32/jobs/hifive1-duty.json --out duty.json
target/release/e5r-verify verify-result duty.json
```

`check` does the following:
1. Builds the ELF and refuses it if its hash differs from the pin.
2. Refuses a stale generated board.
3. Exports the flash image and generates `image_fidelity`, a theorem that
   the independent Lean ELF reader reconstructs exactly that image from the
   original bytes.
4. Scans every module for proof escapes and metaprogramming: `sorry`,
   `admit`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`,
   `extern`, `unsafe`, `opaque`, `skipKernelTC`, `trustCompiler`, `run_cmd`,
   `run_elab`, `run_meta`, `#eval`, `elab`, `macro`, `syntax`,
   `initialize`, `addDecl`. Every import must be a module checked earlier
   in the same job.
5. Compiles each module from source with one Lean worker, under the limits,
   then replays every module's declarations through a fresh kernel with
   `leanchecker`.
6. Prints each named theorem's axioms and refuses anything beyond `propext`,
   `Classical.choice` and `Quot.sound`.

The result (`e5r.verify.result.v1`) has one status:

| Status | Meaning |
| --- | --- |
| `proved` | Every named theorem checked, with allowed axioms only |
| `failed` | A proof did not check. **Not a counterexample**: it says nothing about whether the property holds |
| `unsupported` | The exporter refused the binary or board as outside the scope; nothing was attempted |
| `resource_exhausted` | A time or memory limit stopped a step |
| `error` | The job could not run: a missing tool, a malformed job, a stale generated file, a changed ELF identity or an unknown theorem |

`counterexample` is reserved for a violation replayed in the model. No
current job kind produces one.

A result records SHA-256 identities of:
- the job, the board and the ELF;
- every model and proof source;
- the Lean and `e5r-verify` versions.

`verify-result` recomputes them and reports the result stale if any differ,
so a proof is never silently carried over to a changed binary,
specification, model or toolchain. `check --resume` skips recompiling a
module only if its source, every earlier module's source and the Lean
version are unchanged since it last compiled successfully. It is for
development; CI and the one-command check always run fresh.

### Rechecking without e5r

```sh
target/release/e5r-verify bundle verification/rv32/jobs/hifive1-clamp32.json --out clamp-bundle
cd clamp-bundle && ./recheck.sh
```

`bundle` runs the job fresh. If it is proved, `bundle` writes a
self-contained directory: the model and proof sources, the generated image
and fidelity modules, the ELF, the result, and SHA-256 sums of all of
them. Its `recheck.sh` needs only Lean, the version named in
`lean-toolchain`. It checks the sums, recompiles every module and requires
the axiom report to equal the recorded one. Python, Rust and e5r are not
involved, and no network access is needed. The clamp bundle is 11 MB and
rechecks in under a minute.

### Adding a target

1. Build the firmware so its ELF is byte-reproducible (no host paths in
   loaded bytes), and run `e5r-verify flash` on it. A refusal names the rule
   the image breaks.
2. Write the property in Lean against `Theories/Logic.lean` and the
   generated image module, as `Projects/hifive1/Duty.lean` does.
3. Add a job file listing the build, the ELF pin, the modules and the
   theorems, and run `e5r-verify check`.

No runner needs editing. Writing the proof is still manual for now; the
automatic whole-program checker is the open item above.

## Current results

As checked on 2026-10-29 on the development host (Lean 4.35.0, rustc 1.98.1):

| Job | Theorems | Time | Peak RSS |
| --- | --- | --- | --- |
| `hifive1-duty` (`duty_contract`, `nonvacuous`, 30 model controls, image fidelity) | 50 | 40 s | 957 MiB |
| `hifive1-clamp32` (`clamp_all`, `spec_toNat`, `wraps`, `nonvacuous`, image fidelity) | 15 | 20 s | 596 MiB |
| `hifive1-checker` (`check_sound`, `check_sound_hybrid`, image fidelity) | 3 | 90 s | 954 MiB |
| `hybrid-ringhead-firmware` (ring-head contract on the firmware bytes, `RingAI.spec_sound`) | 17 | 120 s | 955 MiB |
| `hybrid-ring-demo` / `hybrid-ring-loop-demo` (separate binaries) | 22 / 22 | 94 s / 100 s | 789 / 783 MiB |

`duty_contract` is proved about the instructions rustc emitted for `duty()`
in the checked image. From every state meeting the calling convention (`a0`
points at 8 bytes of RAM), the function returns to `ra` with
`a0 = min(sum/8 + 7, 100)`, the source-level expression. That is related to
the compiler's `min(sum/8, 93) + 7`. RAM is unchanged, only `a1`-`a3` are
clobbered, and every CSR is preserved. The loop is proved by an invariant.

Both are statements about uninterrupted instruction sequences: they take no
interrupt steps. For the clamp that is all the binary can do, because it
never enables interrupts and boot assumption 1 says they start disabled.
For `duty()` it is the function's own semantics; interrupts arriving in the
middle of it are for the whole-firmware theorem. The `duty` job pins the
proof's address `0x200102a0` to the ELF symbol containing `duty`.

`clamp_all` is proved for the 32-bit clamp binary (`opt-level` 1, 2 and `s`
emit the same bytes). From every boot state with the pc at the entry, the
binary reaches its idle loop having stored `input.wrapping_add(7).min(100)`
for every input word, and nothing else changed. `wraps` pins the overflow
case.

## Validation of the model

These are tests of the model, not proofs about it:

- **Whole firmware on QEMU `sifive_e`.** The QEMU trace of the Embassy
  firmware with UART input `A z B 0xff 0x00 Q` agrees with the model on
  every GPR and every modeled CSR after each of 62,773 transitions. That
  includes 170 timer interrupt entries and `mret`s and 1,032 device writes,
  and the duty values match the input.
- **Instruction level on QEMU user mode.** Seeded random programs cover all
  84 supported instruction kinds with edge-case operands. Four seeds, about
  30,000 instructions, all agree, and a trace with one flipped bit is
  rejected.
- **Negative controls.** `Projects/Controls.lean` is kernel-checked. It
  covers every fault class: misaligned, unmapped, flash writes, device
  width and direction, atomics outside RAM, illegal encodings,
  ecall/ebreak, unmodeled and read-only CSRs, entering U-mode, fetching
  outside the image, and SC with and without a reservation.
  `tools/test_job_controls.py` checks that the runner gives the right
  status to a changed ELF, a false theorem, a `sorry`, a memory limit, a
  non-ELF input and an unknown theorem.

The replay found one model bug: a CSR read through the environment lost its
pc advance. It was fixed before any proof depended on it.

## Independent review

A separate reviewer read the TCB (`Hart.lean`, `Platform.lean`,
`FlashElf.lean`, `flash.rs`, `job.rs`) against the RISC-V specifications
and these claims on 2026-10-29. The reviewer was a separate agent session,
not a human expert. Every finding was fixed or documented in the same
commit series:

- **SC without a reservation skipped the address checks**, so a misaligned
  or non-RAM SC did not trap. Fixed: SC probes its address first; two
  controls added.
- **A proof module could add a theorem without kernel checking** by
  metaprogramming (`run_cmd` plus an option name built from strings), and
  the scan and audit would accept it. Fixed: metaprogramming is banned, and
  every module is replayed by `leanchecker`. The exploit is now a permanent
  runner control.
- **Vectored `mtvec` with an unaligned base computes a different vector on
  SiFive cores.** Fixed: vectored mode needs a 128-byte-aligned base, else
  unsupported.
- **The flash window was the whole 512 MiB XIP alias.** Fixed: it is the
  physical flash after the bootloader.
- **Runner gaps.**
  - Unchecked imports: now refused.
  - The tool binary and `gen_board.py` were not in the result identity:
    now hashed.
  - Inputs changing mid-run: now detected.
  - `Ns.*` missed attributed theorems: fixed.
- **Two documentation overstatements** (literal checking, addresses bound
  to symbols): corrected, and the `duty` address is now pinned.

The reviewer found the decoders (every RV32C quadrant), immediates, M and A
arithmetic, CSR rules, interrupt entry/return and the two ELF readers'
rules correct. That was checked by reading and by evaluating about 20
encodings. It is not a proof.

## What remains for the whole-firmware theorem

`Theories/Absint.lean` is the checker the whole-firmware theorem will
rest on. It works by abstract interpretation:
- abstract values: value sets, ranges, and values symbolic in the
  interrupted machine;
- memory cells with guarded facts, enough to express `Option<Waker>`'s null
  niche;
- a global static-RAM invariant at interruptible points;
- an interrupt-handler summary relative to the interrupted registers, with
  a pinned region for `main`'s frame, where the Embassy executor lives.

`tools/Analyze.lean` searches for certificates with the same transfer
function. It is untrusted: whatever it emits either checks or is rejected.
Two things are open, and one is done:

1. **Precision: a candidate exists.** With one interrupt invariant per
   node partition (`Cert.Gs`/`Cert.part`, partitioned by the saved-pointer
   words 0x800000d4, 0x8000008c and 0x80000010), the proved ring-head
   summary, address and copy-before-branch splits, and value partitions in
   0x200103b8..0x200104e4, the analyzer reports no possible fault and emits
   a 65,845-node certificate. It is not accepted (item 2). With default
   options it still reports 68; an earlier option set reached 47.
   Almost all are a lost correlation between a task's state byte and the
   saved pointer it guards (the actuator's channel pointer at 0x800000d4,
   the sampler's channel tail), plus `wake()` with a merged task pointer.
   The checker now has the means to keep such facts across interrupts:
   - kept intervals (`Cert.hkeep`): static RAM the handler never writes,
     whose facts survive an interrupt window;
   - unconditional facts implied by guarded ones whose guard holds;
   - several facts about the same bytes are intersected.
   The untrusted analyzer's merge and reuse choices still lose the fact
   (`tools/Analyze.lean` options `E5R_ADDR_SPLIT`, `E5R_TAG_DEPTH`,
   `E5R_KEEP`, `E5R_KEEP_GUARDED`, `E5R_FREEZE_G`, `E5R_RING`, with their
   measurements in the commit messages).
2. **Size: the blocker.** The zero-report certificate's source (29 MB
   after sharing repeated lists) aborts elaboration within 24 GB after
   593 s, and the checker finds nodes by list index, so kernel evaluation
   would be quadratic in 65,845 nodes. Needed: an O(log n) node index in the
   checker, a compact encoding, and fewer nodes (a proved summary of the
   sampler's channel-tail update would replace the value partitions).
3. **`check_sound`: done.** `Theories/AbsintSound.lean` proves

   ```lean
   theorem check_sound (hc : check cfg boot cert = true)
       (hinit : ∀ m, Init m → StateHolds ρM boot m) :
       ∀ m evs, Reach cfg.board cfg.img Init m evs →
         ¬ Escapes cfg.board cfg.img m ∧ ∀ ev ∈ evs, EvOk cfg ev
   ```

   In words: if the checker accepts a certificate, then from any machine the
   boot description covers, no reachable machine can fault, either on its
   next instruction or on interrupt entry. Every device write along the way
   is also within the configured bounds (`cfg.allow`). That is the shape the
   firmware theorem needs: `pwmcmp1 ∈ 0..100` is one `allow` entry.
   `#print axioms` lists only `propext`, `Classical.choice` and
   `Quot.sound`, and `leanchecker` replays the module.

   Interrupts are handled compositionally:
   - The handler runs under the interrupted registers, pc, `mie`, `mtvec`
     and `mscratch`, held as symbols.
   - A frame lemma shows that handler stores touch only static RAM and the
     handler's stack budget below the interrupted sp.
   - `mret` provably resumes the interrupted node.

   Writing the proof found these checker bugs, all fixed before the
   checker was used for any result:
   - Byte stores recorded unmasked values.
   - Handler-frame loads were not range-checked.
   - Guards and pins were not restricted to RAM or static memory.
   - Interrupt points required MPP = M, but `mret` resumes with MPP = U.
   - A handler could change `mie`, `mtvec` or `mscratch`, which the return
     summary assumed unchanged.
   - A guarded stack fact at an interrupt point could be invalidated
     through a static guard word the handler writes.

4. **Hybrid composition: done.** Code the abstract domain handles badly can
   be proved directly and composed into the same theorem:
   `check_sound_hybrid` takes, next to an accepted `checkHybrid`
   certificate, proofs of directly proved `Region`s (delegated pcs; every
   step proved against `stepInstr` on the image bytes, interrupts allowed
   only where a certificate node describes the machine) and of masked
   summaries (`SumSpec`: a finite run with no interrupt enabled at any
   machine, ending where the summary's exit state describes it). Plain
   `check` accepts neither (`check_delegate`, `check_sums`), so
   `check_sound` is unchanged.

Until the first two are done, no whole-firmware guarantee is claimed.
