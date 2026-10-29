# COBS decoder proofs: `cobs::dec::decode_in_place_report` (pinned RMK image)

Owner: exporter/runner worker. Files: `Projects/rmk/Cobs/*.lean` only. No main
(Deframer) or peer (Memmove) file is edited. Image: the runner's packed ELF
(`Projects.rmk.Elf`, sha256 `f39d833f…`), board `QemuVirtRv32.board 0x80029bc8`
(`E5R.Rmk.B`), instruction fetch through `Projects/rmk/Fetch.lean`.

## The code (read from the bytes, 0x8001e02e..0x8001e148, 97 instructions)

* **ABI:** a0 = address of a 12-byte result, a1 = buffer, a2 = length. The buffer
  is decoded in place.
* **Frame:** `addi sp,sp,-16`; s0..s3 are saved at sp−4, −8, −12, −16 (caller sp).
* **Phases:**
  * **Scan** (0x8001e03c..0x8001e04e): n = the index of the first zero byte, or
    len if there is none.
  * **Decode loop** (0x8001e064..0x8001e0ea): code bytes, and copies of code−1
    bytes at 0x8001e09c..0x8001e0c2.
  * **Exit** (0x8001e102): stores a word at a0+a6 and the tag at a0, restores
    s0..s3, returns.
* **Results** (word offsets in the 12-byte slot):

  | Path | [a0] | [a0+4] | [a0+8] |
  | --- | --- | --- | --- |
  | len = 0 (0x8001e0f8) | 1 | 0 (empty) | — |
  | invalid frame (0x8001e116, code runs past n) | 1 | 1 | bytes written so far |
  | target too small (0x8001e0fe) | 1 | 2 | — |
  | success (0x8001e0ee) | 0 | source bytes used | bytes decoded |

* **Panic sites:** two calls to `core::panicking::panic_bounds_check`
  (0x8001f83a), from 0x8001e12a (copy read index = len) and 0x8001e140 (code
  index ≥ len). Both look unreachable, because every read index is below
  n ≤ len. That is still to be proved, as part of the decode-loop invariant.
* **Caller:** `next` calls the wrapper `cobs::dec::decode_in_place` (0x8001e006,
  32-byte frame, result at its sp+0xc). The wrapper returns
  `[out] = (tag − 1) | [res+4]` and `[out+4] = [res+8]`. Its length argument is
  the frame without its delimiter, at most 488.

## Proved (kernel-checked; axioms propext, Classical.choice, Quot.sound; no sorry)

**`E5R.Rmk.Cobs.decode` (Decode.lean): the whole function.** For every machine meeting
`CobsEnv` (len ≤ 488), a quiet deterministic run returns to ra, and:
* `Returns` holds: frame, registers, CSRs, and RAM unchanged outside slot/buffer/frame.
* `Res` holds:
  * **len = 0:** `[a0] = 1`, `[a0+4] = 0`.
  * **otherwise:**
    * `[a0] = 0`/`1` (ok/invalid);
    * `[a0+4] = n`/`1`, where n = the first zero index;
    * `[a0+8]` = the decoded length;
    * every buffer byte j < len equals the decoded output (j < its length) or the
      original byte.
  * All of it is a function of the ORIGINAL buffer bytes: `Spec.run`, a transliteration
    of the emitted loop.

Consequences:
* No panic site is reached. A returning QRun is the model's only behaviour, so
  neither `panic_bounds_check` call is taken; the guards are proved untaken.
* The "target too small" error (code 2) never occurs for in-place calls.
* Stores land only in the slot, the buffer or the frame.
* The outcome reads nothing outside the buffer, apart from the frame's own
  save/restore.

Building blocks:
* `Fetch.lean`: 97 instruction facts.
* `Basic.lean`: `CobsEnv`, `Returns`, `prologue`, `exit_run`, `finish`.
* `Empty.lean`: `empty`.
* `Scan.lean`: the first-zero loop.
* `Copy.lean`: the copy loop.
* `Spec.lean`: `block`/`run`.
* `Loop.lean`:
  * `LInv`, `ExitPrep`;
  * the head, both bodies, tail and exits;
  * `iter` and `loop`, the latter by fuel induction against `run`.

**Runner job** `jobs/rmk/rmk-cobs-decode.json`, with
wrapper `Projects/ramimage/Cobs.lean` (`E5R.RmkCobs.decode` on the runner's image and board via
checked `img_eq`/`board_eq`).
* Status: `proved` in 258 s (Lean compile, `leanchecker` replay of every module, axiom
  audit), peak 6.5 GB in the shared `Fetch.lean`.
* The symbols 0x8001e02e/0x8001e006 are pinned.
* Receipt: `verification/rv32/ram-image/rmk-qemu-riscv-rynk/rmk-cobs-decode.result.json`.

## Interface for main's `next` composition (proposal)

```lean
-- precondition (Cobs/Basic.lean)
structure CobsEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x8001e02e
  quiet : Quiet m.core
  out : B.inRam a0 12 ; outAl : a0 % 4 = 0
  buf : B.inRam a1 len ; len : len ≤ 488
  frame : B.inRam (sp − 16) 16 ; spAl : sp % 4 = 0
  outBuf, outFrame, bufFrame : pairwise disjoint
  ra : ra even
-- postcondition, every return (Cobs/Basic.lean)
structure Returns (m₀ m : Machine) : Prop where
  pc : m.pc = ra
  regs : every register but a0-a7, t0-t6 as at entry (so sp, ra, s0-s11, gp, tp)
  csr : CSRs unchanged
  ram : RAM unchanged outside [a0, a0+12) ∪ [a1, a1+len) ∪ [sp−16, sp)
```

Top-level theorem (proved):
`E5R.Rmk.Cobs.decode : ∀ m₀, CobsEnv m₀ → ∃ k m, QRun B img k m₀ m ∧ Returns m₀ m ∧ Res m₀ m`.

For `next`, the wrapper adds 32 bytes of frame on top of these 16, so 48 bytes
below sp at the wrapper's entry. The `decode_in_place` contract (0x8001e006,
straight-line around this call) is not proved yet. It should give
`[out] = 0xffffffff` on success, the error code otherwise, and
`[out+4] = [res+8]`.
