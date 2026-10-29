# RMK (QEMU virt, RV32) — direct machine-code proofs

Original e5r code, Apache-2.0. Target: upstream rmk @ 71556128, example `qemu-riscv-rynk`, release ELF
sha256 `f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30` (recipe: review worker's
BUILD-RECEIPT; deterministic only at fixed absolute paths). Board `QemuVirtRv32.board 0x80029bc8`,
image `(RamElf.imageOf 0x80000000 0x1000000 elf).ro` (main's independent reader, support-lean4 d96ca45).

| File | Content |
| --- | --- |
| `gen_elf.py` → `Elf.lean` (generated, untracked) | the pinned ELF as `RamElf.File` (64-byte LE words), sha256 checked |
| `Fetch.lean` | reader run once by the kernel (`roShape_ok`), `File.slice` lemmas, `fetchDecode_of`: a `.text` instruction fact in ~4 s / 0.8 GB |
| `Run.lean` | `Quiet` (no interrupt enabled) and `QRun` (quiet deterministic steps) |
| `Copy.lean` | `fwd`/`bwd`: what the byte loops do; `fwd_spec`/`bwd_spec`: the memmove result incl. overlap |
| `MemmoveFetch.lean` | 39 instruction facts of the emitted memmove (generated from the model's decoder) |
| `MemmoveLoops.lean` | forward loop 0x80020fc6 and backward loop 0x8002109c, all iterations |
| `MemmoveSmall.lean` | `Memmove.contract`: memmove from the trampoline 0x80020c1e for **n < 16** |

`Memmove.contract` (BOUNDED: n < 16; the word and misaligned paths for n ≥ 16 are not covered):
Pre: pc 0x80020c1e, quiet, n = a2 < 16, [a0, a0+n) and [a1, a1+n) in model RAM, sp 4-aligned with the
12 save-slot bytes below it in RAM, both ranges apart from the slots, ra even. Post: a quiet
deterministic run (no fault, no event, no interrupt enabled at any machine) returns to ra; every
register but t1, a1–a4, a6 as at entry (s0–s2 and sp restored, a0 = dst); CSRs unchanged; RAM outside
the slots = memmove of the entry RAM (dst ← src, either overlap direction, n = 0 leaves RAM alone).

Checks (from verification/rv32):

    python3 -I Projects/rmk/check_rmk.py ELF Projects/rmk/results/memmove-small.json  # proved, 93 theorems
    python3 -I Projects/rmk/test_controls.py                                           # 7/7 + baseline

`check_rmk.py` does what `e5r-verify check` does (pin check, forbidden words, fresh compile, leanchecker,
axiom audit) because the runner cannot export RAM-resident images yet.
