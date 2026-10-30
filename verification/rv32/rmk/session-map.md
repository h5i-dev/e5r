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

All of this is CONDITIONAL on `CopyContract` (memmove, still open).

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
| 0x80003e70..0x80003fd4 | Read the header halfword at s6+0xcb; `RynkService::dispatch` (0x80003e9a); `encode_frame` (0x80003f1a); slice checks (panics at 0x80004210, 0x80004220…); the response send (`Uart16550::send_bytes` at 0x800042f8 via 0x8000429e); `yield_now` (0x80004320); 0x80003fa6 (header 0xff) → 0x80003fc6 … | **NOT proved** (dispatch and response) |
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
