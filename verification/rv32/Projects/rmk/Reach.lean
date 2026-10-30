/-
  From quiet deterministic runs between checkpoints to every reachable machine (`Reach`).

  Original e5r code, Apache-2.0.

  PROVED here, for any board, image and checkpoint set P:
  * `quiet_step`: from a quiet machine with a deterministic step, `Step` (under ANY oracle, or an
    interrupt) has exactly that successor and emits nothing;
  * `reach_on_runs`: if every checkpoint starts a quiet deterministic run of at least one step that
    ends at a checkpoint, then every machine reachable from the checkpoints has emitted no event
    and has a quiet deterministic run to a checkpoint;
  * `reach_avoids`: then, for a pc region that absorbs runs (a run from inside it stays inside)
    and contains no checkpoint, no reachable machine is in the region.

  This is how segment theorems such as `Deframer.Session.recv_step` become statements about every
  behaviour of the model. It does NOT cover a segment containing a device read (MMIO loads draw
  from the environment, so they are not `DetStep`) or an enabled interrupt: such a segment needs
  its own step-closure argument.
-/
import Projects.rmk.Run

namespace E5R.Rmk
open E5R

theorem qrun_first {B : Board} {img : List Segment} {k : Nat} {m m' : Machine} (h : QRun B img (k + 1) m m') :
    ∃ m₁, Quiet m.core ∧ DetStep B img m m₁ ∧ QRun B img k m₁ m' := by
  cases h with
  | step hq hs hr => exact ⟨_, hq, hs, hr⟩

theorem quiet_step {B : Board} {img : List Segment} {m m₁ x : Machine} {evs : List Event}
    (hq : Quiet m.core) (hd : DetStep B img m m₁) (hs : Step B img m x evs) : x = m₁ ∧ evs = [] := by
  cases hs with
  | instr o h =>
    have := hd o
    rw [h] at this
    injection this with h1 h2 h3
    subst h1 h2 h3
    exact ⟨rfl, rfl⟩
  | irq code he _ => rw [hq code] at he; exact absurd he (by decide)

theorem reach_on_runs {B : Board} {img : List Segment} (P : Machine → Prop)
    (hrun : ∀ m₀, P m₀ → ∃ k m, QRun B img (k + 1) m₀ m ∧ P m) :
    ∀ m evs, Reach B img P m evs → evs = [] ∧ ∃ k m', QRun B img k m m' ∧ P m' := by
  intro m evs hr
  induction hr with
  | init hp => exact ⟨rfl, 0, _, .refl _, hp⟩
  | step _ hs ih =>
    obtain ⟨he, k, m', hrun', hp⟩ := ih
    cases k with
    | zero =>
      cases hrun'
      obtain ⟨k₁, mE, hr₁, hpE⟩ := hrun _ hp
      obtain ⟨m₁, hq, hd, hrest⟩ := qrun_first hr₁
      obtain ⟨rfl, rfl⟩ := quiet_step hq hd hs
      exact ⟨by simp [he], k₁, mE, hrest, hpE⟩
    | succ j =>
      obtain ⟨m₁, hq, hd, hrest⟩ := qrun_first hrun'
      obtain ⟨rfl, rfl⟩ := quiet_step hq hd hs
      exact ⟨by simp [he], j, m', hrest, hp⟩

/-- A pc region that every quiet deterministic run started inside it stays in. -/
def Absorbing (B : Board) (img : List Segment) (R : Word → Prop) : Prop :=
  ∀ k m m', R m.core.pc → QRun B img k m m' → R m'.core.pc

theorem reach_avoids {B : Board} {img : List Segment} (P : Machine → Prop)
    (hrun : ∀ m₀, P m₀ → ∃ k m, QRun B img (k + 1) m₀ m ∧ P m)
    (R : Word → Prop) (hR : Absorbing B img R) (hP : ∀ m, P m → ¬ R m.core.pc) :
    ∀ m evs, Reach B img P m evs → ¬ R m.core.pc := by
  intro m evs hr hm
  obtain ⟨-, k, m', hrun', hp⟩ := reach_on_runs P hrun m evs hr
  exact hP m' hp (hR k m m' hm hrun')

end E5R.Rmk
