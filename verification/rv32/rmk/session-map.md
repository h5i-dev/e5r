# RMK Rynk session loop: map from the pinned bytes (f39d833f)

This map is read from the bytes with llvm-objdump and the model's own decoder. The session loop is
inlined into the embassy main task's poll function, `TaskStorage<…main_task…>::poll`. Its state
lives in the task future, a static whose bases are s6 = 0x8002a4bd and s7 = 0x8002a3cf.

## Addresses

| What | Where |
| --- | --- |
| Deframer (consumed, filled, discarding) | s6+0x2cf = 0x8002a78c..0x8002a798 |
| Buffer, 488 bytes | s7+0x1c1 = 0x8002a590..0x8002a778 |
| Parked count | s6+0x2db = 0x8002a798 |
| `RynkMessage` (ptr, len, header u16, byte, k) | s7+0x1b1 = 0x8002a580..0x8002a590 |

## The loop and what is proved

`CopyContract` (memmove) is a theorem: `Deframer.copy_contract`, from the peer's
`Memmove.contractAll`. `recv_step'` and `unpark_step'` are the unconditional forms.

| pc | Code | Status |
| --- | --- | --- |
| 0x80003e1a | Loop head: s1 = deframer, s0 = buffer, call `next` | `recv_step` |
| 0x80003e36 | a0&1 = 0 (None): go to 0x80003f58 | `recv_step` |
| 0x80003f58 | Load consumed, filled, discarding into s3/s5/s8/s9; call `tail` | `recv_step` |
| 0x80003f7c | `bnez s9` / `bgeu s5,s8` lead to 0x80003ff2; else the stores, then 0x8000434c (s4 ≠ 0) or 0x80004428 | **NOT proved** (UART read future) |
| 0x80003e3c | Some(k): s2 = k; call `park_pending` | `recv_step` |
| 0x80003e4e | a2 = 488 − parked; store parked at s6+0x2db; `bgeu a2,489` (slice panic at 0x80004234) never taken | `recv_step` |
| 0x80003e5e | Call `RynkMessage::from_decoded(msg, buf, 488 − parked, k)` (0x8001c3c6). Its length panic (len < 3) is never taken, since `next` gives k < consumed and so parked ≤ 484 | `recv_step` |
| 0x80003e70 | Return from `from_decoded` | `recv_step` (Some outcome) |
| 0x80003e70 → 0x80003fd8 | Header halfword at s6+0xcb (msg+8) negative as i16: straight to the unpark call site | `SomePath.some_neg` (then `unpark_round`) |
| 0x80003e70 → 0x800001f2 → 0x80003e9e | Header ≥ 0: future at s6+0x2f3 (state byte 0), poll of the dispatch closure | `SomeRound.some_pos`, against `DispatchContract` (NOT proved) |
| 0x80003e9e → 0x80004204 / 0x80003fa6 | Result 0xfe (Pending: poll exits to the executor) / 0xff | boundaries of `some_pos` (not proved beyond) |
| 0x80003e9e → 0x80008d5c → 0x80003f1e | Response byte, 7-byte frame buffer 0x8002a7b1, `encode_frame` | `some_pos`, against `EncodeContract` (NOT proved) |
| 0x80003f1e → 0x80003fd8 / 0x8000429e | Slice check (panic 0x80004210 not taken), send state; empty response → flag [s10] := 1, unpark site / send loop | `some_pos` (empty: back to the loop head; send: boundary) |
| 0x80003e70..0x80003fd4 (summary) | Read the header halfword at s6+0xcb; `RynkService::dispatch` (0x80003e9a); `encode_frame` (0x80003f1a); slice checks (panics at 0x80004210, 0x80004220…); the response send (`Uart16550::send_bytes` at 0x800042f8 via 0x8000429e); `yield_now` (0x80004320); 0x80003fa6 (header 0xff) → 0x80003fc6 … | **NOT proved** (dispatch and response) |
| 0x80003fd8 | Load parked from s6+0x2db; call `unpark_pending(deframer, buffer, 488, parked)` | `unpark_step` |
| 0x80003ff0 | `j 0x80003e1a` | `unpark_step` (ends at the loop head with `SessPre`) |
| 0x80003ff2.. | None with discarding or nothing pending: UART read future setup, `poll` of the read (0x80004018); `assert_offset` MMIO loops (0x8000437c…); executor | **NOT proved** |

## Theorems (Projects/rmk/Deframer/)

* `Session.recv_step`: `SessPre` at 0x80003e1a reaches one of two points by a quiet run:
  * Some, at 0x80003e70, with the message filled;
  * None, at 0x80003f7c, with the invariant.

  Writes are confined.
* `Session.unpark_step`: `UnparkAt` at 0x80003fd8 (parked ≤ 488, discarding ≤ 1) reaches
  `SessPre` at 0x80003e1a, at the same sp, with filled = parked.

## Composition tools (proved)

* `Projects/rmk/Reach.lean`:
  * `reach_on_runs`: if every checkpoint starts a quiet deterministic run back to a checkpoint,
    every machine reachable from the checkpoints is on such a run and has emitted no event.
  * `reach_avoids`: the same, for an absorbing pc region with no checkpoint in it.
* `Projects/rmk/PanicRegion.lean`:
  * `panic_absorbing`: once in `slice_index_fail`, `panic_bounds_check`, `panic_fmt` or the `j .`
    loop of `rust_begin_unwind`, a deterministic run never leaves.
  * `reach_no_panic`: with checkpoints off the panic path, no reachable machine is at
    0x8001fafc, 0x8001f83a or 0x8001e148.

  This uses only the run endpoints, not their intermediate pcs.

* `Projects/rmk/Trees.lean`. `Lands P m` says that every `Step` behaviour from m, for every
  oracle (any device-read value) and with device writes as events, reaches a checkpoint. Each node
  must be quiet and must not fault under any oracle; those obligations are proved, not assumed.
  * `reach_lands`, `reach_no_escape`: from checkpoints rooted in such trees, no reachable machine
    escapes.
  * `PanicRegion.reach_no_panic_io`: none reaches a panic pc.
* `Projects/rmk/DevRead.lean` `lands_lbu_dev`: a device `lbu` is a tree node, with one successor
  per value the device may return.
* `Projects/rmk/Deframer/Rx.lean` `rx_loop`: the UART receive poll 0x80004374..0x800043a8, for
  every LSR/RBR value sequence.
  * Every behaviour reaches 0x800043a8 with i ≤ cap.
  * Registers outside ra/s0/s1/a0-a2 are kept.
  * RAM changes only in buf[dst..dst+cap) and the one stack byte of `assert_offset`.
  * NO CopyContract dependency.
  * Explicit preconditions (`RxEnv`): s3/s5 = the UART RBR/LSR addresses (read from the
    `Uart16550` struct in RAM; its contents are assumed, not proved), cap ≥ 1, the ranges in RAM,
    and the core quiet at entry.

* `Projects/rmk/Deframer/NonePath.lean` `none_step`: from `recv_step`'s None point 0x80003f7c,
  every behaviour, for every UART value, either
  * returns to the loop head 0x80003e1a with `SessPre` (bytes read: filled += n ≤ 488), or
  * stops at an EXPLICIT boundary: 0x80003ff2 (discarding / nothing pending) or 0x80004428 (buffer
    full / no byte ready), where the read future and the executor take over. Those are not proved.

  Explicit assumptions (`NoneAt`):
  * the Uart16550 struct (base 0x10000000 at +0x1c, stride 1 at +0x20) lies outside the future's
    state words;
  * the task flag pointer at sp+0x24 points into RAM outside the deframer;
  * there are 0x28 stack bytes above sp.

## What closing the loop still needs (not assumed anywhere)

* `reach_on_runs` covers only deterministic, event-free segments. Both gaps below do device I/O:
  * UART writes emit events, so they are not `DetStep`;
  * UART reads take their value from the environment.

  The next composition step is a variant that allows deterministic steps emitting events
  (writes), plus a branching argument over the read values (reads). Neither exists yet.

* **Some gap.** From 0x80003e70 to 0x80003fd8 the code must:
  * keep s6, s7, sp and the stack bound;
  * keep the parked count ≤ 488 at s6+0x2db, and discarding ≤ 1;
  * not reach a panic.

  It runs dispatch, the response encoding and the UART writes. It yields to the executor at
  `yield_now`, where other tasks run between polls, so a single quiet run of one task cannot
  express it. It needs a `Reach`-style statement over the executor.
* **None gap.** From 0x80003f7c through the UART read future back to 0x80003e1a. The read bytes
  come from the device oracle: MMIO reads are not `DetStep`.
* **Interrupts.** In the 300,000-state replay mstatus.MIE = mie = 0 and there were no interrupts.
  `SessPre` assumes `Quiet`; that is an assumption about the run, not a theorem.
