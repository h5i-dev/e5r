# Documentation

- [ROADMAP.md](ROADMAP.md): scope, milestones and what will not be built

## Verification (`e5r`)

- [ptx.md](verification/ptx.md): NVIDIA PTX kernels: model, kernel classes, spec format, command line, trusted base, open items
- [firmware.md](verification/firmware.md): RISC-V firmware for the HiFive1 Rev B: scope, guarantees, assumptions, trusted base
- [firmware-install.md](verification/firmware-install.md): installing the firmware toolchain
- [rmk-checkpoint.md](verification/rmk-checkpoint.md): RMK machine-code proofs, replay commands and open boundaries
- [rmk-checkpoint-validation.md](verification/rmk-checkpoint-validation.md): how the RMK checkpoint is validated
- [ram-image-export.md](verification/ram-image-export.md): exporting a RAM-resident ELF image to Lean
- [rv32-research.md](verification/rv32-research.md): the RV32I research proofs the firmware work grew from

## Toolkit (`e5rx`, development infrastructure)

- [MANUAL.md](toolkit/MANUAL.md): command reference
- [tutorial.md](toolkit/tutorial.md): a stripped binary to a committed annotation log
- [dashboard.md](toolkit/dashboard.md): the project workspace and dashboard
- [design/](toolkit/design/): one document per subsystem
- [scorecard.md](toolkit/scorecard.md), [benchmarks.md](toolkit/benchmarks.md), [boundaries.md](toolkit/boundaries.md), [decbench.md](toolkit/decbench.md): measured numbers
- [sla-format.md](toolkit/sla-format.md): Ghidra's compiled SLEIGH format
- [x86-64-notes.md](toolkit/x86-64-notes.md): x86-64 and ELF notes from the original C++ disassembler
