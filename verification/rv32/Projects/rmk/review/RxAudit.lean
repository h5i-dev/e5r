/-
  Independent audit of main's checkpoint trees (Trees.lean, DevRead.lean) and the UART receive
  poll (Deframer/Rx.lean) at support-lean4 f8f1c44. Review evidence only: nothing here is used by
  main's proofs, and no main module is changed.

  Original e5r code, Apache-2.0.

  PROVED here:
  * `lands_hits`: a `Lands` tree is not vacuous: from its root some actual sequence of `Step`s
    reaches a checkpoint. So `Lands B img (fun _ => False) m` never holds (`lands_false`).
  * `weak_vacuous`: the no-fault field of `Lands.step` is essential: without it, a machine whose
    next instruction faults under every oracle (odd pc) "lands" in the empty checkpoint set.
  * `rx_witness`: `RxEnv` and `RxAt` are satisfiable together (a concrete quiet core at
    0x80004374), so `rx_loop` is not vacuous; `rx_exit_reached`: from it the exit 0x800043a8 is
    actually reached by some behaviour.
-/
import Projects.rmk.Deframer.Rx

namespace E5R.Rmk.Review
open E5R E5R.Rmk E5R.Rmk.Deframer.Rx

/-- Prepending a step to a run from a single start. -/
theorem reach_cons {B : Board} {img : List Segment} {m m' : Machine} {e : List Event}
    (hs : Step B img m m' e) : ∀ {x evs}, Reach B img (· = m') x evs → Reach B img (· = m) x (e ++ evs) := by
  intro x evs h
  induction h with
  | init h0 => subst h0; simpa using (Reach.step (Reach.init rfl) hs : Reach B img (· = m) _ ([] ++ e))
  | step _ hs' ih => rw [← List.append_assoc]; exact .step ih hs'

/-- Every `Lands` tree is entered by real behaviour: some run from the root reaches `P`. -/
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

theorem lands_false {B : Board} {img : List Segment} (m : Machine) : ¬ Lands B img (fun _ => False) m := by
  intro h; obtain ⟨_, _, _, hp⟩ := lands_hits h; exact hp

/-- `Lands` without the no-fault field (the hypothesis this control drops). -/
inductive LandsW (B : Board) (img : List Segment) (P : Machine → Prop) : Machine → Prop
  | done {m} : P m → LandsW B img P m
  | step {m} : Quiet m.core → (∀ x evs, Step B img m x evs → LandsW B img P x) → LandsW B img P m

/-- Counterexample: with the field dropped, a quiet machine at an odd pc (every oracle faults)
    lands in the EMPTY checkpoint set. -/
theorem weak_vacuous {B : Board} {img : List Segment} (m : Machine) (hq : Quiet m.core)
    (hodd : m.core.pc.getLsbD 0 = true) : LandsW B img (fun _ => False) m := by
  refine .step hq fun x evs hs => ?_
  cases hs with
  | instr o h => simp [stepInstr, hodd] at h
  | irq code he _ => rw [hq code] at he; exact absurd he (by decide)

/-- A concrete entry core for the receive poll. -/
def c0 : Core where
  pc := 0x80004374
  x := fun r => if r.val = 19 then 0x10000000 else if r.val = 21 then 0x10000005 else
    if r.val = 20 then 16 else if r.val = 18 then 0x80030000 else if r.val = 2 then 0x80040000 else 0
  mie_ := false
  mpie := false
  mpp := 3
  mieReg := 0
  mtvec := 0
  mepc := 0
  mcause := 0
  mscratch := 0
  resv := false

theorem c0_quiet : Quiet c0 := fun code => by simp [irqEnabled, c0]

theorem rx_witness (M0 : Word → BitVec 8) : RxEnv c0 ∧ RxAt c0 M0 c0 M0 0 := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨rfl, c0_quiet, fun _ _ => rfl, by decide, by decide, fun _ _ _ => rfl⟩⟩

/-- The receive poll's exit is reached by real behaviour from the witness entry. -/
theorem rx_exit_reached (M0 : Word → BitVec 8) :
    ∃ x evs, Reach B img (· = ⟨c0, M0⟩) x evs ∧ RxOut c0 M0 x := by
  obtain ⟨hE, hA⟩ := rx_witness M0
  exact lands_hits (rx_loop c0 M0 hE _ 0 c0 M0 rfl hA)

/-- The same core with the timer interrupt enabled (mstatus.MIE, mie.MTIE) and mtvec = 0x80000000. -/
def c1 : Core := { c0 with mie_ := true, mieReg := 0x80, mtvec := 0x80000000 }

/-- The core after taking the timer interrupt from `c1`. -/
def c1irq : Core :=
  { c1 with pc := 0x80000000, mepc := 0x80004374, mcause := BitVec.ofNat 32 (2 ^ 31 + 7), mpie := true, mie_ := false, mpp := 3 }

/-- Counterexample for dropping `Quiet`: at the loop head a non-quiet core has a `Step` (the timer
    interrupt, to mtvec) that is no instruction step under any oracle, so `step_oracle`, and with
    it every `Lands` argument above, needs the quiet hypothesis. -/
theorem irq_counter (M0 : Word → BitVec 8) :
    ∃ x, Step B img ⟨c1, M0⟩ x [] ∧ x.core.pc = 0x80000000 ∧
      ¬ ∃ o evs, stepInstr B img ⟨c1, M0⟩ o = .ok x.core x.ram evs := by
  refine ⟨⟨c1irq, M0⟩, .irq 7 (show irqEnabled c1 7 = true by decide) (show takeIrq c1 7 = .done c1irq by rfl), rfl, ?_⟩
  rintro ⟨o, evs, h⟩
  have hpc : (⟨c1, M0⟩ : Machine).core.pc = 0x80004374 := rfl
  rw [stepInstr_of (by rw [hpc]; decide) (by rw [hpc]; exact E5R.Rmk.RxFetch.f80004374), exec_opimm] at h
  simp only [interp, Result.ok.injEq] at h
  have := congrArg Core.pc h.1
  simp [Core.wr, c1, c0, c1irq] at this

end E5R.Rmk.Review
