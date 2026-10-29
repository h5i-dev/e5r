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

## `decode_in_place` (0x8001e006), the function `next` calls: PROVED

`E5R.Rmk.Cobs.decode_in_place` (Wrapper.lean):

```lean
structure WEnv (m : Machine) : Prop where     -- a0 = out (8 bytes), a1 = buf, a2 = len
  pc : m.core.pc = 0x8001e006 ; quiet : Quiet m.core
  out : B.inRam a0 8 ; outAl : a0 % 4 = 0
  buf : B.inRam a1 len ; len : len ≤ 488
  frame : B.inRam (sp - 48) 48 ; spAl : sp % 4 = 0      -- 32 bytes here + 16 in the inner call
  outBuf, outFrame, bufFrame : pairwise disjoint (frame = [sp - 48, sp))
  ra : ra even
structure WReturns (m₀ m) : Prop   -- pc = ra; all but a0-a7, t0-t6 kept; CSRs kept;
                                   -- RAM unchanged outside [a0, a0+8) ∪ buf ∪ [sp-48, sp)
def WRes (m₀ m) : Prop :=          -- orig = original buffer bytes, n = firstZero orig 0 len,
                                   -- r = Spec.run orig n (n+1) 0 []
  (len = 0 → [a0] = 0) ∧
  (0 < len → [a0] = (if r.1 = ok then 0xffffffff else 1) ∧ [a0+4] = |r.2| ∧
     ∀ j < len, buf[j] = if j < |r.2| then r.2[j] else orig j)
theorem decode_in_place (m₀) (h : WEnv m₀) : ∃ k m, QRun B img k m₀ m ∧ WReturns m₀ m ∧ WRes m₀ m
```

In `next` (0x8001d4be):
* **Argument registers:**
  * a0 = next's sp + 4 (the 8-byte result);
  * a1 = buf + consumed;
  * a2 = the frame length up to the delimiter.
* **How `next` reads the result:** it compares `[sp+4]` against s9 = −1 (success), then
  reads `[sp+8]` as the decoded length.
* **For main's `next` composition:** `WEnv` needs 48 bytes below `next`'s sp at the
  call, disjoint from the buffer and from next's result slot.

Both contracts are in the runner job `jobs/rmk/rmk-cobs-decode.json`, restated on the
runner's image in `Projects/ramimage/Cobs.lean`. Status: `proved` in 294 s, 10 theorems
audited, standard axioms.

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

## Negative controls, bundle and recheck (both contracts, runner image)

Controls: `python3 -I scripts/test-rmk-cobs-job.py E5R_VERIFY`; transcript
`verification/rv32/ram-image/rmk-qemu-riscv-rynk/cobs-job-controls.txt`.
* **How proof mutations are run:** each edits copies of the Cobs modules (renamed into
  `build/testjobs/cobsmut/`) and runs the job on them.
* **What counts as a rejection:** `failed`, with the first Lean error located by
  re-running Lean on the failing module, inside a theorem of the mutated chain, and not an
  import or unknown-identifier error.

| Mutation | Result |
| --- | --- |
| unmodified copies (control) | `proved` |
| read guard: `Spec.block` invalid iff n ≤ src+code (was <) | rejected in Loop `block_small` |
| result tag swapped in `Res` | rejected in `decode` |
| decoded length + 1 in `Res` | rejected in `decode` |
| `CobsEnv.bufFrame := True` (buffer may overlap the frame) | rejected in Loop `exit_from` (first use of the hypothesis) |
| wrapper success word 0xfffffffe in `WRes` | rejected in `decode_in_place` |
| `WEnv.outFrame := True` (result may overlap the frame) | rejected in `decode_in_place` |
| opcode: 0x8001e0b2 `sb a5,0(s1)` → `sb a4,0(s1)` in the ELF (unpinned) | rejected at instruction fact `f8001e0b2` |
| a job module that does not exist | `error` (a tool problem, not a rejection) |

A rejected precondition mutation shows the proof needs that hypothesis. It does not show
the weakened statement is false.

Bundle: `e5r-verify bundle jobs/rmk/rmk-cobs-decode.json` (281 s), then `recheck.sh`
(158 s).
* The packing check passed: all 454,024 ELF bytes equal the Lean literal.
* Every theorem rechecks with exactly the recorded axioms, the 10 in `axioms.expected`.
* A separate `leanchecker` replay of the bundle's Cobs modules passes.
* Receipts are in `ram-image/rmk-qemu-riscv-rynk/cobs-bundle/`.

### Exact preconditions

**`decode` (`CobsEnv`):**
* pc = 0x8001e02e, and no interrupt enabled (`Quiet`);
* the result slot [a0, a0+12) in model RAM, with a0 ≡ 0 mod 4;
* the buffer [a1, a1+len) in model RAM, with len = a2 ≤ 488;
* the frame [sp−16, sp) in model RAM, with sp ≡ 0 mod 4;
* slot, buffer and frame pairwise disjoint;
* ra even.

**`decode_in_place` (`WEnv`):**
* pc = 0x8001e006;
* the result [a0, a0+8), the buffer, and the frame [sp−48, sp);
* otherwise the same conditions as `CobsEnv`.

"Model RAM" is [0x80029bc8, 0x81000000): `QemuVirtRv32.board rwBase`.

### Assumptions that remain (not established here)

* **ISA model:** the RV32 model (Theories/Hart, Platform) describes the hart. Main's QEMU
  replay is evidence for this, not part of these theorems.
* **Interrupts:** none is enabled during the call (`Quiet` is a premise).
* **Where the data lives:** buffer, slot and frame are in model RAM. Below rwBase the model
  treats the image as read-only, while on QEMU it is writable RAM. A caller with data there
  is not covered.
* **The binary:** the pinned ELF f39d833f, reproducible only at its original build path
  (`rmk-r0-audit/`).
* **The spec:** `Spec.run` transliterates the emitted loop. No claim is made that it equals
  COBS as standardized.
* **Scope:** these are function contracts. `next`'s composition (main) must establish
  `WEnv` at its call site.
