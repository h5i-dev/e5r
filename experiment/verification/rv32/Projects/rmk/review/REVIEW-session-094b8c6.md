# Review: session invariant, rounds and the negative-header Some path (support-lean4 094b8c6)

This is the independent review worker's audit of:
- `Deframer/SessionInv.lean`: `SessInv`/`Extras`, `none_of_recv`, `extras_keep`, `session_round`, `unpark_round`;
- `Deframer/SomePath.lean`: `some_neg`.

**Pinned to commit 094b8c6.** Main's later, uncommitted widened `Extras` is not covered and needs its own pass. No main module was changed.

## How it was checked

- **Fresh build.** A clean `/dev/shm` worktree of 094b8c6 was built from source, with `Elf.lean` regenerated from the pinned ELF (f39d833f…).
  - The build ran module by module through `build_main.sh`, in the order of `sess-order.txt`.
  - All 78 modules compile, and the log ends BUILD-DONE.
- **Axioms.** `session_round`, `unpark_round` and `some_neg` use propext, Classical.choice and Quot.sound. There is no sorry, native_decide, bv_decide or `axiom` in SessionInv, SomePath, SomeSegs or NonePath.
- **`SessAudit.lean`** contains the proofs below, written against main's definitions.
- **`test_sess_controls.py`** holds 8 adversarial controls. All 8 are rejected in the expected declaration (`sess-controls-094b8c6.txt`).
- **Harness fix.** The first run exposed a bug in my harness (also present in the f8f1c44 Rx harness). When a control made several edits to one file, the restore kept the earlier edits. Both scripts are fixed. The Rx controls were rerun on a fresh f8f1c44 build; see `rx-controls-f8f1c44.txt`.

## Real initial state (QEMU observation, untrusted, used by no proof)

These values come from an existing QEMU trace of the same ELF, at the first arrival at the loop head 0x80003e1a, cross-checked with the disassembly:

| fact | real value | where the code sets it |
|---|---|---|
| sp | 0x80fffe10 | poll prologue `addi sp,sp,-0x1c0` (0x80003476) |
| s7, s6 | 0x8002a3cf, 0x8002a4bd | s7 = a0+0x7ff (0x800034ae), s6 = s7+0xee (0x800034bc); a0 = &POOL = 0x80029bd0 at poll entry |
| [0x8002a784] (uPtr) | 0x8002a1c0 | `sw a2,0x2c7(s6)` at 0x80003daa, a2 = `lw 0x1c(sp)` (the async fn's UART argument) |
| [0x8002a1dc] base, [0x8002a1e0] stride | 0x10000000, 1 | UART driver init (seen loaded at 0x8000c8fc / 0x8000c8e4 on the TX path) |
| [sp+0x24] flag pointer | 0x8002a7c9 = s6+0x30c | `sw a1,0x24(sp)` at 0x800034da, on every poll entry |
| deframer | consumed = filled = discarding = 0 | 0x80003e0a..0x80003e16 |
| mstatus / mie | 0 / 0 | never set, see I6 |

`sess_witness` proves that `SessInv` holds for a concrete machine with exactly this layout. **So the strengthened invariant is satisfiable at the real initialization.** It is not proved that the firmware establishes it.

## Findings

**S1. Non-vacuity holds.**
- `session_round_hits`: from the real-layout witness, some actual behaviour reaches `LoopQ`.
- `some_witness` and `some_neg_hits`: `SomeAt` with a negative header is satisfiable, and `some_neg` then reaches the loop head with `SessInv`. This also exercises the unpark tail.
- Controls:
  - a Some witness with header byte 0x7f is rejected;
  - a non-quiet witness core is rejected.

**S2. Universal oracle coverage.**
- `session_round` is a `Lands1`. Its None branch goes through `none_step` and the UART poll, with every LSR/RBR value quantified (as reviewed at f8f1c44).
- `some_neg` and `unpark_round` are deterministic `QRun`s with no device reads, so no oracle arises.

**S3. Frame and separation.**
- `SW` and `extras_keep` are sound.
- Shrinking the stack part of `SW` from 0x70 to 0x40 bytes is rejected: the receive step writes down to sp-0x70.
- Dropping `flagSep` is rejected in `none_of_recv`.
- Placing the UART struct in the receive buffer makes `uSep` fail in the witness (`extras_of`). So `uSep` is a real constraint, and the real layout (0x8002a1c0) satisfies it.
- Note: the real flag byte 0x8002a7c9 lies inside `SW`'s future-state range 0x8002a7b0..0x8002a7ca. `Extras` allows this, because `extras_keep` excludes the flag byte explicitly. A widened `Extras` must keep that exception.

**S4. Boundary escape.**
- `LoopQ` has three exits that are not proved: 0x80003ff2 and 0x80004428 (the read future) and `SomeAt` (dispatch).
- Removing either the read-future exit or the `SomeAt` exit is rejected. These are genuine escape points.
- No reachability-wide invariant follows yet. Applying `reach_lands` with `P = LoopQ` needs `Lands1` at every boundary point, which is not proved.

**S5. Missing initial facts.** These must be proved from the code before 0x80003e1a, not assumed. All were observed true.

- I1. **Struct pointer.** [0x8002a784] holds the `Uart16550` pointer, stored at 0x80003daa from the async fn argument at sp+0x1c.
- I2. **Struct contents.** [ptr+0x1c] = 0x10000000 and [ptr+0x20] = 1.
  - These are set by UART init before the task runs.
  - Proving them also needs "nothing writes them afterwards" across all executor and other-task code, not only the session's `SW`.
- I3. **Flag pointer.** [sp+0x24] = s6+0x30c. It is rewritten at every poll entry (0x800034da), so it can be established per poll rather than carried.
- I4. **Stack.** sp = 0x80fffe10, which satisfies `SessPre.sp` and `spTop`. Proving it requires the executor's stack depth at poll time.
- I5. **Deframer zeroed.** The path from poll entry through 0x80003d8e to 0x80003e1a contains the calls `TopicSubscribers::new` and `memset`. Their frames must stay out of `Extras`' facts.
- I6. **Quiet across executor polls.**
  - The only write to the `mie` CSR in the whole image is `csrwi mie, 0` at 0x80000008.
  - `csrs mstatus` (0x80016840) only restores a previous MIE in `critical_section::release`, and the single `mret` (0x80000188) is in the trap handler.
  - With mie = 0, `irqEnabled` is false for every code. So `Quiet` is provable as a whole-image invariant: no reachable instruction writes `mie` nonzero.
  - Recommendation: prove it once rather than assume it per round.
- I7. **Session base registers.** s6/s7 = `s6v`/`s7v` need a0 = &POOL (0x80029bd0) at poll entry, which is the executor's contract.

**S6. Version.** These findings are for 094b8c6. A re-review of the widened `Extras` is pending until main commits it.
