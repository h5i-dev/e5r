# Binary-level firmware verification (scope F)

e5r-verify proves safety properties of a firmware **binary** for one board.
The Lean kernel checks the proofs. The proof subject is the flash image built
from the ELF file's bytes. e5r's decompiler, CFG recovery and IR are not
inputs to any proof.

This document defines the supported scope. Milestone status is in
[ROADMAP.md, section F](ROADMAP.md#f-scoped-firmware-verification-2026-10-28-owner-authorization);
the V0 research proofs it grew from are in
[verification-rv32.md](verification-rv32.md).

## The supported configuration

| | |
| --- | --- |
| Board | SiFive HiFive1 Rev B: FE310-G002 SoC, one E31 hart |
| ISA | RV32IMAC + Zicsr + Zifencei, MRET, WFI |
| Privilege | Machine mode only |
| Boot | The board's bootloader jumps to `0x20010000` (ELF `e_entry`) in M-mode |
| Memory | 16 KiB DTIM RAM at `0x80000000`; XIP flash window `0x20000000`-`0x3fffffff` |
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

A firmware guarantee is a Lean theorem of this shape (`Theories/Platform.lean`):

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
   allows only `propext`, `Quot.sound` and `Classical.choice` and refuses any
   project axiom, `sorry`, `native_decide` or `ofReduceBool`.
2. The semantics: `Theories/Hart.lean` (decoding and instruction meaning),
   `Theories/Platform.lean` (memory, devices, interrupts, reachability) and
   the generated board. They are written from the RISC-V specifications and
   the FE310-G002 manual. QEMU replay and differential tests are evidence for
   them, not proof.
3. The property statement for each target, and the boot assumptions above.
4. The binding from file to theorem. The exporter writes the ELF's bytes into
   Lean. An independent Lean ELF reader then derives the flash image from
   those bytes, and the image-fidelity theorem is proved by the kernel. The
   runner checks the literal against every byte of the input file. The
   runner, Python and the filesystem are not verified.

The design of the ISA/memory split, the distinction between "the architecture
traps" and "the model declines", and frame summaries over regions follow
Theorem Labs'
[rocq-linux-process-semantics](https://github.com/theorem-labs/rocq-linux-process-semantics)
(MIT). That model is Rocq and describes a Linux process: no code or proof
from it is used here, and its process semantics supplies none of the
bare-metal interrupt, device or boot behavior modeled here.
