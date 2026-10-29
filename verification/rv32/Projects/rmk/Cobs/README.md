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

* `Cobs/Fetch.lean`: the 97 instruction facts.
* `Cobs/Basic.lean`:
  * `CobsEnv` (precondition), `Returns` (frame postcondition);
  * `prologue`, `exit_run`;
  * `finish`: every exit from 0x8001e102 meets `Returns`, with the exact result
    words.
* `Cobs/Empty.lean`: `empty`. With len = 0 the call returns with
  `[a0] = 1, [a0+4] = 0`, and `Returns` holds.
* `Cobs/Scan.lean`: `scan`. The first loop ends at 0x8001e050 with
  a4 = `firstZero (bufByte S buf) i len` (all bytes before it non-zero, a zero
  there unless it is len). RAM is unchanged; only a3 and a4 are written.

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

Planned top-level theorem (not yet proved; the name is reserved):

`E5R.Rmk.Cobs.decode : ∀ m₀, CobsEnv m₀ → ∃ k m, QRun B img k m₀ m ∧ Returns m₀ m ∧ Res m₀ m`

`Res` will state:
* the tag ∈ {0, 1}, with the result words as in the table;
* on success, [a0+4] ≤ len and [a0+8] ≤ [a0+4];
* the buffer after the call is a function of the buffer before it alone (the
  bound on reads), given by a transliteration of the emitted algorithm.

A returning `QRun` excludes the panics: each step is the model's only behaviour,
and the run ends at ra, not at 0x8001f83a.

For `next`, the wrapper adds 16 bytes of frame (32 in total) on top of this
16. A `decode_in_place` contract (0x8001e006, straight-line around this call)
will follow, giving `[out] = 0xffffffff` on success and the error code
otherwise.
