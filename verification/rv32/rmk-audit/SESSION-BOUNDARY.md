# RMK session: the UART/executor boundary and the Reach interface it needs

Exporter/runner worker, 2026-10-29, on main 51d2b14 (`recv_step`, `unpark_step`) and the pinned
image (ELF sha256 f39d833f…). This is an audit note: it closes no gap and assumes none closed.
Main's proof files are not edited. Nothing below is a safety claim about RMK.

Sources: `Theories/Platform.lean` (`interp`, `Step`, `Reach`, `Escapes`), `Theories/AbsintSound.lean`
(`Region`, `check_sound_hybrid`, `SumSound`, `EvOk`), `Projects/rmk/Run.lean` (`Quiet`, `QRun`),
`Projects/rmk/Deframer/{Spec,Session,SessionLoop}.lean`, `rmk/session-map.md`, and the bytes,
read with the model's own decoder (`rmk-audit/Dis.lean`; listings quoted below).

## 1. What is proved, in `Reach` terms

| Theorem | Kind | Hypotheses |
| --- | --- | --- |
| `Session.recv_step` | ∃ `QRun` from `SessPre` (0x80003e1a) to 0x80003e70 (Some) or 0x80003f7c (None) | `CopyContract` |
| `Session.unpark_step` | ∃ `QRun` from `UnparkAt` (0x80003fd8) to `SessPre` | `CopyContract` |
| `RmkSession.unpark_then_recv` (mine) | their composition, one `QRun` | `CopyContract` |
| `Closure.qrun_only`, `reach_closed`, `closed_of_anchored`, `reach_anchored` (mine, `Projects/rmk/Closure.lean`) | generic: a `QRun` is the only behaviour of `Step`; a closed set covers `Reach` | none |

A `QRun` is a sequence of `DetStep`s from `Quiet` machines. `Closure.qrun_only` proves that such
a step is the *only* `Step` from its machine (no other successor, no event, no interrupt), so a
proved `QRun` already describes everything `Reach` can do along it. What it cannot describe is
anything that is not a `DetStep`: a device read (`devVal w (o i)` depends on the oracle), a
device write (`Step` emits an `Event`, `DetStep` requires `[]`), an enabled interrupt.

## 2. What the open segments do, from the bytes

All addresses on the pinned image; model decoder output (`lean --run rmk-audit/Dis.lean`).

* **The loop is not one run.** The session loop is inside the main task's
  `TaskStorage::poll` (0x80003476). Its prologue allocates a 0x1c0 frame and recomputes the
  session bases from the task pointer on every poll:
  `0x800034ae addi s7,a0,0x7ff`, `0x800034bc addi s6,s7,0xee`.
  So `SessPre`'s s6 = 0x8002a4bd / s7 = 0x8002a3cf hold after a poll entry only when the
  executor passes a0 = 0x80029bd0 (the task storage).
* **Yield = return to the executor.** At 0x800043b6..0x800043f8 the poll stores a state byte
  (`sb 6, 0x2ee(s6)`; `sb 4, 0(s6)`), restores s0..s11/ra, `addi sp,sp,0x1c0`, `ret`. The
  stack frame is gone between polls; only the task future (static RAM around s6/s7) persists.
  The next poll re-enters through the state dispatch, not at 0x80003e1a directly.
* **Some gap (0x80003e70 → 0x80003fd8).** Reads the header halfword `lh a0,0xcb(s6)`, calls
  `RynkService::dispatch` (0x80003e9a), `encode_frame`, then the response send loop
  0x8000429e..0x80004310 (call at 0x800042f8 into the UART writer; progress counter at
  s6+0x327 compared with s6+0x317), and `yield_now` (0x80004320). The call at 0x800042f8 goes
  to `uart_16550::Uart16550<MmioBackend>::send_bytes` (0x800098a6), which reads the LSR
  (offset 5, `andi a0,a0,0x20`: THR empty, 0x800098f0) and the MSR (offset 6, `andi …,0x10`:
  CTS, 0x8000991a/0x80009944) before writing: device reads and device writes, so neither
  `DetStep` nor event-free.
* **Register addresses come from RAM.** Both UART paths compute the register address as
  `base + (offset << shift)` from the driver struct (`lbu …,0x20(…)` the shift,
  `lw …,0x1c(…)` the base; 0x800098d4/0x800098e6, 0x8000434c/0x80004362), after
  `0x8001692e` checks offset < 8. An access lands on a modeled UART0 register only if that
  struct still holds base 0x10000000 and the stride the board models; otherwise `interp`
  faults ("load from an unmodeled address"). That struct is one more RAM invariant the
  executor and every task must preserve.
* **None gap (0x80003f7c → loop head).** Sets up the read future (0x80003ff2..), polls
  `embassy_futures::select::Select<Uart read, …>` (call at 0x80004018 to 0x8000c89a). The
  byte loop at 0x8000434c..0x800043a2 is the receive path: `lbu a0,0(s5)` (LSR, `andi a0,a0,1`
  = data ready) and `lbu a0,0(s3)` (RBR) stored with `sb a0,0(s0)` into the buffer, with
  `0x8001692e` asserting the register offset < 8 before each access (panics otherwise).
  Every byte read is an oracle value: the buffer contents are arbitrary, which `recv_step`
  already allows ("whatever bytes the buffer holds").
* **Interrupts.** Every proved step assumes `Quiet` (no `irqEnabled` code). Nothing proves that
  the executor or other tasks keep `mstatus.MIE`/`mie` such that no interrupt is enabled.

## 3. `SessionSafe` as stated, against this boundary

`SessionSafe sp` quantifies over `Reach B img Init` with `Init m₀ := pc = loopPc ∧ Inv m₀.ram …`.
Two observations for main (no proof file edited, none assumed wrong):

1. **`Init` is weaker than `SessPre`.** It does not fix s6/s7, sp, `Quiet`, or `discarding ≤ 1`.
   A machine at 0x80003e1a with arbitrary s6 calls `next` on an arbitrary "deframer" and may
   reach a panic; with an interrupt enabled it may jump to the trap handler. So `SessionSafe`
   as stated is probably not provable from the session code; the natural statement uses
   `SessPre` (or a boot-time `Init` plus an executor invariant that establishes it).
2. **Faults are silent.** `Reach` only follows `.ok` steps; a machine that can fault simply has
   no successor, and `SessionSafe` says nothing about it. A safety statement should also give
   `¬ Escapes` for every reachable machine, as `check_sound` does.

## 4. The minimal interface (proved generic part: `Projects/rmk/Closure.lean`)

```lean
structure Closed (B img) (Init : Machine → Prop) (ev : Event → Prop) (R : Machine → Prop) : Prop where
  init  : ∀ m, Init m → R m
  step  : ∀ m, R m → ∀ o : Oracle, ∃ c ram evs, stepInstr B img m o = .ok c ram evs ∧
            (∀ e ∈ evs, ev e) ∧ R ⟨c, ram⟩
  quiet : ∀ m, R m → Quiet m.core

theorem reach_closed (hR : Closed B img Init ev R) :
  ∀ m evs, Reach B img Init m evs → R m ∧ ¬ Escapes B img m ∧ ∀ e ∈ evs, ev e
theorem closed_of_anchored (hA : Anchored B img A) : Closed B img A ev (OnSeg B img A)
```

* `step` is **for every oracle**: that is exactly how device reads enter (the LSR/RBR values
  are `o i`). A segment that reads the UART needs an `R` that holds for all read values, not a
  run.
* `ev` is where UART writes enter: `interp` already faults on any device address not in the
  board, so every event is at one of the eight UART0 registers; `ev` can restrict further
  (e.g. only THR/IER/FCR/LCR/MCR writes, with values), like `EvOk` with `Config.allow`.
* `quiet` makes interrupts an obligation of the region instead of an assumption of each run.
* `closed_of_anchored`: proved `QRun` segments between anchors (`recv_step`, `unpark_step`)
  are a `Closed` set without anything more. Mixing is by union: `R := OnSeg ∨ R_gap`, where a
  `QRun`'s end must lie in `R_gap`'s entry and `R_gap`'s exits in an anchor.

This is the same shape as the absint checker's `Region` (AbsintSound.lean:4001: `step` over all
oracles with `EvOk`, `irq`), whose `check_sound_hybrid` composes delegated regions with the
certified rest. The intended route for the session is therefore:

1. **Anchors** at the poll entry and the resume points, with invariants on the **task future in
   RAM** (state byte at s6+0x2ee, deframer, parked count at s6+0x2db, message), not on
   registers, since the frame does not survive a yield. `SessPre` is then derived after the
   prologue from a0 = 0x80029bd0.
2. **Deterministic stretches** (deframer calls, `from_decoded`, unpark): `QRun` segments, as
   proved, entered through `closed_of_anchored`.
3. **Device stretches** (UART send loop, read future, `select`): a `Region`/`Closed` set,
   proved by hand or by the absint checker, holding for every oracle value, events restricted
   to UART0, no interrupt enabled.
4. **Executor and other tasks**: they run between polls, so they are inside `Reach`. Either the
   absint checker certifies them (with the session delegated as a region), or a frame
   contract shows they do not write the task future, the deframer or the buffer and re-poll
   with a0 = 0x80029bd0. Neither exists yet.
5. Only then is a `SessionSafe`-style statement (with a strengthened `Init`, plus `¬ Escapes`)
   in reach. Every piece remains conditional on `CopyContract` until memmove's full contract
   is proved.

## 5. Status

| Piece | Status |
| --- | --- |
| Generic interface (`Closed`, `reach_closed`, `closed_of_anchored`, `reach_anchored`, `qrun_only`) | proved, std axioms (`Projects/rmk/Closure.lean`, in `jobs/rmk/rmk-session-conditional.json`) |
| `recv_step`, `unpark_step`, composition `unpark_then_recv` | proved, **conditional on `CopyContract`** |
| Some gap, None gap, poll entry/exit, executor, other tasks, interrupts | **not proved, not assumed** |
| `SessionSafe` | **not proved**; `Init` likely too weak (§3) |
