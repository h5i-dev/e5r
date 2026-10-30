/-
  RMK session-loop fragments (main's SessionInv/NonePath/SomePath/Rx/Trees, support-lean4
  094b8c6), on the image the job runner generates (`jobs/rmk/rmk-session-fragments.json`).
  Original e5r code, Apache-2.0.

  Every theorem below restates one of main's with its type written out, so an interface change
  makes this job fail instead of silently auditing something else. memmove and COBS are
  discharged (`copy_contract`, `cobs_report`). One composition is new: `unpark_lands`.

  EXPLICIT HYPOTHESES that stay hypotheses: `SessInv` = `SessPre` (pc, `Quiet`, s6/s7 bases,
  stack bounds, deframer invariant, discarding ≤ 1) plus `Extras` (the Uart16550 struct reached
  through the word at 0x8002a784 holds base 0x10000000 and stride 1, outside every written
  range; the task flag pointer at sp+0x24 points into RAM away from the deframer; 0x28 bytes of
  stack above sp). Nothing proves the executor or initialization establishes them.

  NOT `SessionSafe`: `LoopQ` includes boundaries where no proof continues (read future
  0x80003ff2 / 0x80004428, and `SomeAt` 0x80003e70 except for a negative header). Dispatch,
  encode, UART send, the executor, other tasks and interrupt preservation are not proved.
-/
import Projects.ramimage.Deframer
import Projects.rmk.Deframer.SomePath

namespace E5R.RmkFragments
open E5R E5R.Rmk E5R.Rmk.Deframer E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI

/-- One round from the loop head: every behaviour (every UART value) lands at the loop head
    with `SessInv` again or at an explicit boundary. -/
theorem round : ∀ m₀, SessInv m₀ → Lands1 B img LoopQ m₀ := session_round

/-- The unpark site back to the loop head, given the explicit `Extras`. -/
theorem unpark : ∀ m₀, UnparkAt m₀ → Extras m₀ →
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = 0x80003e1a ∧ SessInv m := unpark_round

/-- A negative message header goes straight to the unpark site and back to the loop head. -/
theorem some_negative : ∀ m, SomeAt m → 0x80 ≤ (m.ram 0x8002a589).toNat →
    ∃ k m', QRun B img k m m' ∧ m'.core.pc = 0x80003e1a ∧ SessInv m' := SomeP.some_neg

/-- The None path: every behaviour lands at the loop head (frame kept) or a read-future
    boundary. -/
theorem none_path : ∀ m, NoneP.NoneAt m → Lands B img (NoneP.NoneQ m.core m.ram) m :=
  NoneP.none_step

/-- Checkpoint soundness (main's Trees.lean): a set every member of which lands back in it
    covers `Reach`, with no fault, no escape and no interrupt enabled. -/
theorem reach_sound (P : Machine → Prop) (hck : ∀ m, P m → Lands1 B img P m) :
    ∀ m evs, Reach B img P m evs →
      Quiet m.core ∧ (∀ o f, stepInstr B img m o ≠ .fault f) ∧ ¬ Escapes B img m :=
  reach_no_escape P hck

/-- NEW: from the unpark call site (with `Extras`), every behaviour lands in `LoopQ`: through
    `unpark_pending` to the loop head, then one round. -/
theorem unpark_lands (m₀ : Machine) (h : UnparkAt m₀) (E : Extras m₀) : Lands B img LoopQ m₀ := by
  obtain ⟨k, m, hr, hpc, hs⟩ := unpark_round m₀ h E
  cases k with
  | zero =>
    cases hr
    exact absurd (h.pc.symm.trans hpc) (by decide)
  | succ k => exact (lands1_of_qrun_lands hr (session_round m hs).lands).lands

end E5R.RmkFragments
