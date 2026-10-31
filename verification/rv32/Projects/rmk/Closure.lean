/-
  From proved runs to `Reach`: the interface a session-loop safety proof has to meet.

  Original e5r code, Apache-2.0.

  `SessionSafe` (Projects/rmk/Deframer/Spec.lean) quantifies over `Reach`: every machine any
  sequence of `Step`s (any oracle, any enabled interrupt) can produce. The session theorems so
  far (`recv_step`, `unpark_step`) say a `QRun` EXISTS. This file proves, generically:

  * `qrun_only`: a quiet deterministic step is the ONLY `Step` from its machine (no other
    successor, no event). So a `QRun` is all `Reach` can do from its first machine.
  * `Closed` / `reach_closed`: the minimal Reach-level interface. A predicate `R` that contains
    the initial machines, is closed under `stepInstr` for EVERY oracle (device reads), whose
    every emitted event satisfies `EvOk`, and at which no interrupt is enabled, covers `Reach`;
    hence no reachable machine `Escapes` and every event satisfies `EvOk`.
  * `Anchored` / `closed_of_anchored`: how proved `QRun` segments meet that interface. If every
    anchor machine has a non-empty `QRun` to another anchor, the machines strictly inside those
    runs (plus the anchors) form a `Closed` set with no events.

  Nothing here is about RMK's bytes and nothing here closes a gap: code that reads a device or
  writes one (the UART) is not a `QRun`, so it can only enter through `Closed` directly, with an
  `R` that holds for every oracle value (see verification/rv32/rmk-audit/SESSION-BOUNDARY.md).
-/
import Projects.rmk.Run

namespace E5R.Rmk.Closure
open E5R E5R.Rmk

/-- A quiet deterministic step is the only transition. -/
theorem qrun_only {B : Board} {img : List Segment} {m m₁ m' : Machine} {evs : List Event}
    (hq : Quiet m.core) (hd : DetStep B img m m₁) (hs : Step B img m m' evs) :
    m' = m₁ ∧ evs = [] := by
  cases hs with
  | instr o h =>
    rw [hd o] at h
    cases h
    exact ⟨rfl, rfl⟩
  | irq code he _ => rw [hq code] at he; cases he

/-- A quiet deterministic step does not escape. -/
theorem det_not_escapes {B : Board} {img : List Segment} {m m₁ : Machine}
    (hq : Quiet m.core) (hd : DetStep B img m m₁) : ¬ Escapes B img m := by
  rintro (⟨o, f, h⟩ | ⟨code, e, he, -⟩)
  · rw [hd o] at h; cases h
  · rw [hq code] at he; cases he

/-- The Reach-level interface: `R` is closed under every instruction step for every oracle,
    emits only events satisfying `ev`, and enables no interrupt. -/
structure Closed (B : Board) (img : List Segment) (Init : Machine → Prop) (ev : Event → Prop)
    (R : Machine → Prop) : Prop where
  init : ∀ m, Init m → R m
  step : ∀ m, R m → ∀ o : Oracle, ∃ c ram evs, stepInstr B img m o = .ok c ram evs ∧
    (∀ e ∈ evs, ev e) ∧ R ⟨c, ram⟩
  quiet : ∀ m, R m → Quiet m.core

theorem reach_closed {B : Board} {img : List Segment} {Init : Machine → Prop} {ev : Event → Prop}
    {R : Machine → Prop} (hR : Closed B img Init ev R) :
    ∀ m evs, Reach B img Init m evs → R m ∧ ¬ Escapes B img m ∧ ∀ e ∈ evs, ev e := by
  have inv : ∀ m evs, Reach B img Init m evs → R m ∧ ∀ e ∈ evs, ev e := by
    intro m evs h
    induction h with
    | init hi => exact ⟨hR.init _ hi, by simp⟩
    | step _ hs ih =>
      obtain ⟨hr, he⟩ := ih
      cases hs with
      | instr o h =>
        obtain ⟨c, ram, evs, h', hev, hr'⟩ := hR.step _ hr o
        rw [h'] at h
        cases h
        refine ⟨hr', fun e he' => ?_⟩
        rcases List.mem_append.mp he' with h1 | h1
        · exact he e h1
        · exact hev e h1
      | irq code hen _ => rw [hR.quiet _ hr code] at hen; cases hen
  intro m evs h
  obtain ⟨hr, he⟩ := inv m evs h
  refine ⟨hr, ?_, he⟩
  rintro (⟨o, f, hf⟩ | ⟨code, e, hen, -⟩)
  · obtain ⟨c, ram, evs, h', -⟩ := hR.step _ hr o
    rw [h'] at hf; cases hf
  · rw [hR.quiet _ hr code] at hen; cases hen

/-- Proved segments: every anchor has a non-empty quiet run to an anchor. -/
def Anchored (B : Board) (img : List Segment) (A : Machine → Prop) : Prop :=
  ∀ m, A m → ∃ k m₁, 0 < k ∧ QRun B img k m m₁ ∧ A m₁

/-- The machines on the way from a machine to an anchor (the anchors included). -/
def OnSeg (B : Board) (img : List Segment) (A : Machine → Prop) (m : Machine) : Prop :=
  ∃ k m₁, 0 < k ∧ QRun B img k m m₁ ∧ A m₁

theorem closed_of_anchored {B : Board} {img : List Segment} {A : Machine → Prop} {ev : Event → Prop}
    (hA : Anchored B img A) : Closed B img A ev (OnSeg B img A) where
  init := hA
  step := by
    rintro m ⟨k, m₁, hk, hr, ha⟩ o
    cases hr with
    | refl => omega
    | @step n _ m' _ hq hd hr' =>
      refine ⟨m'.core, m'.ram, [], hd o, by simp, ?_⟩
      show OnSeg B img A m'
      cases n with
      | zero => cases hr'; exact hA _ ha
      | succ n => exact ⟨n + 1, m₁, by omega, hr', ha⟩
  quiet := by
    rintro m ⟨k, m₁, hk, hr, -⟩
    cases hr with
    | refl => omega
    | step hq _ _ => exact hq

/-- Proved segments alone: no reachable machine escapes, none emits an event, and every
    reachable machine is on a proved run to an anchor. -/
theorem reach_anchored {B : Board} {img : List Segment} {A : Machine → Prop}
    (hA : Anchored B img A) :
    ∀ m evs, Reach B img A m evs → OnSeg B img A m ∧ ¬ Escapes B img m ∧ evs = [] := by
  intro m evs h
  obtain ⟨h1, h2, h3⟩ := reach_closed (closed_of_anchored (ev := fun _ => False) hA) m evs h
  refine ⟨h1, h2, ?_⟩
  cases evs with
  | nil => rfl
  | cons e _ => exact (h3 e (by simp)).elim

end E5R.Rmk.Closure
