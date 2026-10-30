/-
  RMK session-loop fragments (main's SessionInv/NonePath/SomePath/SomeRound/Rx/Trees,
  support-lean4 07a17e5), on the image the job runner generates (`jobs/rmk/rmk-session-fragments.json`).
  Original e5r code, Apache-2.0.

  Every theorem below restates one of main's with its type written out, so an interface change
  makes this job fail instead of silently auditing something else. memmove and COBS are
  discharged (`copy_contract`, `cobs_report`). Two compositions are new: `unpark_lands` and
  `round_some`.

  CONDITIONAL, NOT DISCHARGED: `some_round` and `round_some` take main's `DispatchContract`
  (RynkService::dispatch's future, polled at 0x80003e9a) and `EncodeContract` (encode_frame
  0x80008d5c) as HYPOTHESES `hD`, `hE`. Neither is proved anywhere. `some_round` also takes
  `h26 : x26 = 0x8002a7f0`, which `SomeAt`/`SessInv` do not carry; `round_some` does not assume
  it but leaves a Some point where it fails as an explicit residual boundary. The definitions of
  both contracts, `SomeQ`, `SW` and `Extras.spTop` (now sp+0x148) are pinned below by `rfl`.

  EXPLICIT HYPOTHESES that stay hypotheses: `SessInv` = `SessPre` (pc, `Quiet`, s6/s7 bases,
  stack bounds, deframer invariant, discarding ≤ 1) plus `Extras` (the Uart16550 struct reached
  through the word at 0x8002a784 holds base 0x10000000 and stride 1, outside every written
  range; the task flag pointer at sp+0x24 points into RAM away from the deframer; 0x148 bytes of
  stack above sp). Nothing proves the executor or initialization establishes them.

  NOT `SessionSafe`: `LoopQ`/`RoundQ` include boundaries where no proof continues (read future
  0x80003ff2 / 0x80004428; Pending to the executor 0x80004204; dispatch's 0xff path 0x80003fa6;
  the UART send loop 0x8000429e). Dispatch and encode are hypotheses; UART send, the executor,
  other tasks, initialization and interrupt preservation are not proved.
-/
import Projects.ramimage.Deframer
import Projects.rmk.Deframer.SomeRound

namespace E5R.RmkFragments
open E5R E5R.Rmk.Deframer E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI
open E5R.Rmk (Lands Lands1 QRun Quiet reach_no_escape lands_seq lands1_seq lands_of_qrun)
open E5R.Rmk.Deframer.SomeP (DispatchContract EncodeContract DispEnv EncEnv CallPost EncRes SomeQ)

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

/-! ## Pinned interfaces of 07a17e5 (a change to any of these makes the job fail) -/

theorem dispatch_def : DispatchContract =
    ∀ m₀, DispEnv m₀ → Lands B img (CallPost 0x80003e9e m₀) m₀ := rfl

theorem encode_def : EncodeContract =
    ∀ m₀, EncEnv m₀ → Lands B img (fun m => CallPost 0x80003f1e m₀ m ∧ EncRes m₀ m) m₀ := rfl

theorem someQ_def (m : Machine) : SomeQ m =
    ((m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80004204 ∨ m.core.pc = 0x80003fa6 ∨
      m.core.pc = 0x8000429e) := rfl

theorem sw_def (sp x : Word) : SW sp x =
    ((0x8002a78c ≤ x.toNat ∧ x.toNat < 0x8002a798) ∨ (0x8002a590 ≤ x.toNat ∧ x.toNat < 0x8002a778) ∨
      (sp.toNat - 0x70 ≤ x.toNat ∧ x.toNat < sp.toNat) ∨ (0x8002a798 ≤ x.toNat ∧ x.toNat < 0x8002a7b0) ∨
      (0x8002a580 ≤ x.toNat ∧ x.toNat < 0x8002a590) ∨ (0x8002a7b0 ≤ x.toNat ∧ x.toNat < 0x8002a7f4) ∨
      (sp.toNat + 0x140 ≤ x.toNat ∧ x.toNat < sp.toNat + 0x148)) := rfl

theorem extras_spTop (m : Machine) (E : Extras m) : (m.core.get 2).toNat + 0x148 ≤ 0x81000000 :=
  E.spTop

/-- CONDITIONAL on the two NAMED, UNPROVED callee contracts and on `h26`: from the Some point,
    every behaviour lands at the loop head with `SessInv` or at an explicit boundary. -/
theorem some_round (hD : DispatchContract) (hE : EncodeContract) (m₀ : Machine) (h : SomeAt m₀)
    (h26 : m₀.core.get 26 = 0x8002a7f0) : Lands B img SomeQ m₀ :=
  SomeP.some_round hD hE m₀ h h26

/-- Where one round followed by the Some path stops. The Some point stays a boundary only where
    `x26 ≠ 0x8002a7f0`, i.e. where `h26` is not available. -/
def RoundQ (m : Machine) : Prop :=
  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428 ∨
    (SomeAt m ∧ m.core.get 26 ≠ 0x8002a7f0) ∨
    m.core.pc = 0x80004204 ∨ m.core.pc = 0x80003fa6 ∨ m.core.pc = 0x8000429e

/-- NEW, CONDITIONAL on `hD`, `hE`: one round from the loop head, continued through the Some path
    wherever `h26` holds there. No `h26` is assumed. -/
theorem round_some (hD : DispatchContract) (hE : EncodeContract) (m₀ : Machine) (h : SessInv m₀) :
    Lands1 B img RoundQ m₀ := by
  refine lands1_seq (fun m hm => ?_) (session_round m₀ h)
  rcases hm with hl | hr | hr | hs
  · exact .done (.inl hl)
  · exact .done (.inr (.inl hr))
  · exact .done (.inr (.inr (.inl hr)))
  · by_cases h26 : m.core.get 26 = 0x8002a7f0
    · refine lands_seq (fun x hx => ?_) (SomeP.some_round hD hE m hs h26)
      rcases hx with a | b | c | d
      · exact .done (.inl a)
      · exact .done (.inr (.inr (.inr (.inr (.inl b)))))
      · exact .done (.inr (.inr (.inr (.inr (.inr (.inl c))))))
      · exact .done (.inr (.inr (.inr (.inr (.inr (.inr d))))))
    · exact .done (.inr (.inr (.inr (.inl ⟨hs, h26⟩))))

end E5R.RmkFragments
