/-
  RMK session fragments on the runner-generated pinned image. Original e5r code, Apache-2.0.

  `round`, `unpark`, `some_negative`, `none_path` and `unpark_lands` have discharged
  memmove/COBS dependencies. Entry invariants, Quiet, and explicit boundary exits remain.
  They do not establish SessionSafe, boot reachability, or interrupt preservation.

  WARNING: `some_round` and `round_some` below are historical CONDITIONAL interfaces.
  EncodeContract is refuted (Projects/rmk/review/SomeAudit.lean); these implications are vacuous
  and MUST NOT be counted as session safety evidence. The independently proved encode_spec
  requires EncPre and write-set separation; connecting it to this caller remains open.
  DispatchContract now also requires an explicit world invariant W.
-/
import Projects.ramimage.Deframer
import Projects.rmk.Deframer.SomeRound

namespace E5R.RmkFragments
open E5R E5R.Rmk.Deframer E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI
open E5R.Rmk (Lands Lands1 QRun Quiet reach_no_escape lands_seq lands1_seq lands_of_qrun)
open E5R.Rmk.Deframer.SomeP (DispatchContract EncodeContract DispEnv EncEnv CallPost EncRes SomeQ WAt)

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

/-! ## Current conditional interfaces (a change to any of these makes the job fail) -/

theorem dispatch_def (W : (Word → BitVec 8) → Prop) : DispatchContract W =
    ∀ m₀, DispEnv m₀ → W m₀.ram → Lands B img (CallPost 0x80003e9e m₀) m₀ := rfl

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

/-- Historical implication with a refuted EncodeContract premise; not safety evidence. -/
theorem some_round (W : (Word → BitVec 8) → Prop) (hD : DispatchContract W)
    (hE : EncodeContract) (m₀ : Machine) (h : SomeAt m₀) (hW : WAt W m₀) :
    Lands B img SomeQ m₀ :=
  SomeP.some_round W hD hE m₀ h hW

/-- Boundaries after one round and the conditional Some continuation. -/
def RoundQ (m : Machine) : Prop :=
  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428 ∨
    m.core.pc = 0x80004204 ∨ m.core.pc = 0x80003fa6 ∨ m.core.pc = 0x8000429e

/-- Historical conditional composition. EncodeContract is refuted; no safety claim. -/
theorem round_some (W : (Word → BitVec 8) → Prop) (hD : DispatchContract W)
    (hE : EncodeContract) (hW : ∀ m, SomeAt m → WAt W m)
    (m₀ : Machine) (h : SessInv m₀) : Lands1 B img RoundQ m₀ := by
  refine lands1_seq (fun m hm => ?_) (session_round m₀ h)
  rcases hm with hl | hr | hr | hs
  · exact .done (.inl hl)
  · exact .done (.inr (.inl hr))
  · exact .done (.inr (.inr (.inl hr)))
  · refine lands_seq (fun x hx => ?_) (SomeP.some_round W hD hE m hs (hW m hs))
    rcases hx with a | b | c | d
    · exact .done (.inl a)
    · exact .done (.inr (.inr (.inr (.inl b))))
    · exact .done (.inr (.inr (.inr (.inr (.inl c)))))
    · exact .done (.inr (.inr (.inr (.inr (.inr d)))))

end E5R.RmkFragments
