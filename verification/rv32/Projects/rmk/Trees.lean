/-
  Checkpoint composition with device I/O: every behaviour of the model, not only deterministic runs.

  Original e5r code, Apache-2.0.

  `Lands P m`: from m every behaviour of `Step` reaches a checkpoint (P) after finitely many steps
  (the tree is inductive, so every path through it is finite; no uniform bound is claimed, since
  each device-read value has its own subtree). At each step on the way the machine is quiet (no
  interrupt can be taken) and its instruction faults under NO oracle. The successors are quantified
  over every oracle, so a device read's value is arbitrary, and steps may emit device-write events.
  Both per-step obligations are discharged, not assumed.

  PROVED here, for any board and image:
  * `lands_of_qrun`: a quiet deterministic run to a checkpoint is such a tree;
  * `lands_seq`: trees compose (to Q, then from every Q machine to P);
  * `step_oracle`: a quiet machine's `Step` is an instruction step under some oracle;
  * `reach_lands`: if every checkpoint is the root of a tree of at least one step (`Lands1`),
    every machine reachable from the checkpoints is in one, whatever events were emitted;
  * `reach_no_escape`: no reachable machine can leave the verified envelope (`Escapes`).
-/
import Projects.rmk.Reach

namespace E5R.Rmk
open E5R

inductive Lands (B : Board) (img : List Segment) (P : Machine → Prop) : Machine → Prop
  | done {m} : P m → Lands B img P m
  | step {m} : Quiet m.core → (∀ o f, stepInstr B img m o ≠ .fault f) →
      (∀ x evs, Step B img m x evs → Lands B img P x) → Lands B img P m

/-- A tree of at least one step: the root itself steps. -/
def Lands1 (B : Board) (img : List Segment) (P : Machine → Prop) (m : Machine) : Prop :=
  Quiet m.core ∧ (∀ o f, stepInstr B img m o ≠ .fault f) ∧ ∀ x evs, Step B img m x evs → Lands B img P x

theorem Lands1.lands {B : Board} {img : List Segment} {P : Machine → Prop} {m : Machine}
    (h : Lands1 B img P m) : Lands B img P m := .step h.1 h.2.1 h.2.2

theorem lands_of_qrun {B : Board} {img : List Segment} {P : Machine → Prop} :
    ∀ {k m m'}, QRun B img k m m' → P m' → Lands B img P m := by
  intro k m m' h hp
  induction h with
  | refl => exact .done hp
  | step hq hs _ ih =>
    refine .step hq (fun o f e => by rw [hs o] at e; cases e) fun x evs hx => ?_
    obtain ⟨rfl, -⟩ := quiet_step hq hs hx
    exact ih hp

theorem lands1_of_qrun {B : Board} {img : List Segment} {P : Machine → Prop} {k : Nat} {m m' : Machine}
    (h : QRun B img (k + 1) m m') (hp : P m') : Lands1 B img P m := by
  obtain ⟨m₁, hq, hd, hr⟩ := qrun_first h
  refine ⟨hq, (fun o f e => by rw [hd o] at e; cases e), fun x evs hx => ?_⟩
  obtain ⟨rfl, -⟩ := quiet_step hq hd hx
  exact lands_of_qrun hr hp

theorem lands_seq {B : Board} {img : List Segment} {P Q : Machine → Prop}
    (hQ : ∀ m, Q m → Lands B img P m) : ∀ {m}, Lands B img Q m → Lands B img P m := by
  intro m h
  induction h with
  | done hq => exact hQ _ hq
  | step hq hf _ ih => exact .step hq hf ih

theorem lands1_seq {B : Board} {img : List Segment} {P Q : Machine → Prop}
    (hQ : ∀ m, Q m → Lands B img P m) {m : Machine} (h : Lands1 B img Q m) : Lands1 B img P m :=
  ⟨h.1, h.2.1, fun x evs hx => lands_seq hQ (h.2.2 x evs hx)⟩

/-- A quiet machine takes no interrupt: its steps are instruction steps under some oracle. -/
theorem step_oracle {B : Board} {img : List Segment} {m x : Machine} {evs : List Event}
    (hq : Quiet m.core) (hs : Step B img m x evs) : ∃ o, stepInstr B img m o = .ok x.core x.ram evs := by
  cases hs with
  | instr o h => exact ⟨o, h⟩
  | irq code he _ => rw [hq code] at he; exact absurd he (by decide)

theorem reach_lands {B : Board} {img : List Segment} (P : Machine → Prop)
    (hck : ∀ m, P m → Lands1 B img P m) : ∀ m evs, Reach B img P m evs → Lands B img P m := by
  intro m evs hr
  induction hr with
  | init hp => exact .done hp
  | step _ hs ih =>
    cases ih with
    | done hp => exact (hck _ hp).2.2 _ _ hs
    | step _ _ hx => exact hx _ _ hs

theorem reach_no_escape {B : Board} {img : List Segment} (P : Machine → Prop)
    (hck : ∀ m, P m → Lands1 B img P m) :
    ∀ m evs, Reach B img P m evs → Quiet m.core ∧ (∀ o f, stepInstr B img m o ≠ .fault f) ∧ ¬ Escapes B img m := by
  intro m evs hr
  have key : Quiet m.core ∧ ∀ o f, stepInstr B img m o ≠ .fault f := by
    cases reach_lands P hck m evs hr with
    | done hp => exact ⟨(hck _ hp).1, (hck _ hp).2.1⟩
    | step hq hf _ => exact ⟨hq, hf⟩
  refine ⟨key.1, key.2, ?_⟩
  rintro (⟨o, f, h⟩ | ⟨code, e, he, -⟩)
  · exact key.2 o f h
  · rw [key.1 code] at he; exact absurd he (by decide)

end E5R.Rmk
