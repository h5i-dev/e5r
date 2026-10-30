/-
  Independent audit of main's session invariant and rounds (Deframer/SessionInv.lean,
  Deframer/SomePath.lean) at support-lean4 094b8c6. Review evidence only: nothing here is used by
  main's proofs, and no main module is changed.

  Original e5r code, Apache-2.0.

  The witness RAM below uses the values observed (QEMU, untrusted, not used by any proof) at the
  real first arrival at the loop head 0x80003e1a of the pinned image:
    sp = 0x80fffe10; [0x8002a784] = 0x8002a1c0 (the Uart16550 struct, stored at 0x80003daa);
    [0x8002a1dc] = 0x10000000 and [0x8002a1e0] = 1 (base and stride, read on the UART write path);
    [sp+0x24] = s6+0x30c = 0x8002a7c9 (stored at 0x800034da); the deframer zeroed (0x80003e0a..16).

  PROVED here:
  * `sess_witness`: `SessInv` holds for that concrete machine, so the strengthened invariant is
    satisfiable with the real layout (it is NOT proved that the firmware establishes it);
  * `session_round_hits`: from it, some actual behaviour reaches `LoopQ` (the round is not vacuous);
  * `some_witness` / `some_neg_hits`: `SomeAt` with a negative header is satisfiable and `some_neg`
    then reaches the loop head with `SessInv`;
  * `lands_hits` (re-proved, as in RxAudit): `Lands` trees are entered by real runs.
-/
import Projects.rmk.Deframer.SomePath

namespace E5R.Rmk.Review2
open E5R E5R.Rmk E5R.Rmk.Deframer E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI E5R.Rmk.Deframer.SomeP

theorem reach_cons {B : Board} {img : List Segment} {m m' : Machine} {e : List Event}
    (hs : Step B img m m' e) : ∀ {x evs}, Reach B img (· = m') x evs → Reach B img (· = m) x (e ++ evs) := by
  intro x evs h
  induction h with
  | init h0 => subst h0; simpa using (Reach.step (Reach.init rfl) hs : Reach B img (· = m) _ ([] ++ e))
  | step _ hs' ih => rw [← List.append_assoc]; exact .step ih hs'

theorem lands_hits {B : Board} {img : List Segment} {P : Machine → Prop} :
    ∀ {m}, Lands B img P m → ∃ x evs, Reach B img (· = m) x evs ∧ P x := by
  intro m h
  induction h with
  | done hp => exact ⟨_, [], .init rfl, hp⟩
  | @step m hq hf _ ih =>
    cases hr : stepInstr B img m (fun _ => 0) with
    | fault f => exact absurd hr (hf _ f)
    | ok c ram evs =>
      obtain ⟨x, evs', hx, hp⟩ := ih ⟨c, ram⟩ evs (.instr _ hr)
      exact ⟨x, _, reach_cons (.instr _ hr) hx, hp⟩

/-- A RAM given by a byte table (every other byte 0). -/
def mem (t : List (Nat × Nat)) (a : Word) : BitVec 8 :=
  match t.find? (fun p => p.1 == a.toNat) with
  | some p => BitVec.ofNat 8 p.2
  | none => 0

/-- The observed layout at the first loop head. -/
def loopTbl : List (Nat × Nat) :=
  [(0x8002a784, 0xc0), (0x8002a785, 0xa1), (0x8002a786, 0x02), (0x8002a787, 0x80),
   (0x8002a1df, 0x10), (0x8002a1e0, 1),
   (0x80fffe34, 0xc9), (0x80fffe35, 0xa7), (0x80fffe36, 0x02), (0x80fffe37, 0x80)]

def core (pc : Word) : Core where
  pc := pc
  x := fun r => if r.val = 22 then s6v else if r.val = 23 then s7v else if r.val = 2 then 0x80fffe10 else 0
  mie_ := false
  mpie := false
  mpp := 3
  mieReg := 0
  mtvec := 0x800000f8
  mepc := 0
  mcause := 0
  mscratch := 0
  resv := false

theorem core_quiet (pc : Word) : Quiet (core pc) := fun code => by simp [irqEnabled, core]

/-- The extras of the invariant, for any RAM table extending the loop layout. -/
theorem extras_of (t : List (Nat × Nat)) (pc : Word) (ht : t.take 10 = loopTbl)
    (hu : ramRead (mem t) uPtr .w = 0x8002a1c0) (hb : ramRead (mem t) 0x8002a1dc .w = 0x10000000)
    (hs : mem t 0x8002a1e0 = 1) (hf : ramRead (mem t) 0x80fffe34 .w = 0x8002a7c9) :
    Extras ⟨core pc, mem t⟩ := by
  have g2 : (core pc).get 2 = 0x80fffe10 := rfl
  have e1 : ramRead (mem t) uPtr .w + 0x0000001c#32 = 0x8002a1dc := by rw [hu]; decide
  have e2 : ramRead (mem t) uPtr .w + 0x00000020#32 = 0x8002a1e0 := by rw [hu]; decide
  have e3 : ramRead (mem t) ((core pc).get 2 + 0x00000024#32) .w = 0x8002a7c9 := by rw [g2]; exact hf
  refine ⟨by rw [g2]; decide, by rw [e1]; exact hb, by rw [e1]; decide, by show (mem t (ramRead (mem t) uPtr .w + 0x00000020#32)).toNat = 1; rw [e2, hs]; decide,
    by rw [e2]; decide, ?_, by rw [e3]; decide, by rw [e3]; decide, ?_⟩
  · intro k hk
    rw [e1, e3, g2]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
      (refine ⟨?_, by decide⟩; unfold SW; decide)
  · intro k hk
    rw [e3, g2]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- **The strengthened invariant is satisfiable with the real layout.** -/
theorem sess_witness : SessInv ⟨core 0x80003e1a, mem loopTbl⟩ := by
  refine ⟨⟨rfl, core_quiet _, rfl, rfl, by decide, by decide, ?_, by decide⟩,
    extras_of loopTbl _ rfl (by decide) (by decide) (by decide) (by decide)⟩
  unfold Deframer.Inv consumed filled word; decide

/-- One round from the witness is not vacuous: some behaviour reaches `LoopQ`. -/
theorem session_round_hits :
    ∃ x evs, Reach B img (· = ⟨core 0x80003e1a, mem loopTbl⟩) x evs ∧ LoopQ x :=
  lands_hits (session_round _ sess_witness).lands

/-- The Some point: the loop layout plus a message (`RynkMessage` at 0x8002a580: data = bufA,
    len 3, cap 3) whose header high byte 0x8002a589 is 0x80 (negative). -/
def someTbl : List (Nat × Nat) :=
  loopTbl ++ [(0x8002a580, 0x90), (0x8002a581, 0xa5), (0x8002a582, 0x02), (0x8002a583, 0x80),
    (0x8002a584, 3), (0x8002a58c, 3), (0x8002a589, 0x80)]

theorem some_witness : SomeAt ⟨core 0x80003e70, mem someTbl⟩ := by
  refine ⟨rfl, core_quiet _, rfl, rfl, by decide, by decide, ⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by unfold consumed word; decide, by unfold filled word; decide⟩, by decide, by decide,
    extras_of someTbl _ rfl (by decide) (by decide) (by decide) (by decide)⟩

/-- `some_neg` is not vacuous: from the witness it reaches the loop head with `SessInv`. -/
theorem some_neg_hits : ∃ k m', QRun B img k ⟨core 0x80003e70, mem someTbl⟩ m' ∧
    m'.core.pc = 0x80003e1a ∧ SessInv m' :=
  some_neg _ some_witness (by decide)

end E5R.Rmk.Review2
