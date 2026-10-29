/-
  Hybrid safety proofs: composing a closed invariant (for example the one the
  abstract-interpretation checker establishes) with directly proved
  machine-code summaries of hard regions.

  Original e5r code, Apache-2.0.

  Everything here is stated over the concrete semantics of
  `Theories/Platform.lean` (`Step`, `Reach`, `Escapes`, `Event`) and the
  safety property the checker proves: no reachable machine can escape, and
  every event on the way satisfies `Ok`. Nothing is assumed about a summary
  that is not proved against the fetched image.

  A *masked run* is a sequence of deterministic instruction steps through
  machines with `mstatus.MIE = 0`. On such a machine no interrupt is enabled
  (`irqEnabled` requires MIE), and a deterministic step is the machine's only
  transition: every intermediate state of the run has exactly one successor,
  emits no event and cannot fault. A summary that ends its runs in the
  outer invariant may therefore be treated as one edge, and `hybrid_sound`
  proves that this is sound for global `Reach`, interrupts included. Runs
  are finite by construction (`MRun n`), so no termination argument is
  needed; a summary that never reaches its exit is simply not provable.
-/
import Theories.Logic

namespace E5R.Hybrid
open E5R

variable {B : Board} {img : List Segment}

/-! ## Masked runs -/

def Masked (m : Machine) : Prop := m.core.mie_ = false

theorem irqEnabled_masked {m : Machine} (h : Masked m) (code : Nat) :
    irqEnabled m.core code = false := by
  unfold Masked at h; simp [irqEnabled, h]

/-- `n` deterministic instruction steps, each from a machine with interrupts
    disabled. -/
inductive MRun (B : Board) (img : List Segment) : Nat → Machine → Machine → Prop
  | refl (m) : MRun B img 0 m m
  | step {n m m₁ m₂} : Masked m → DetStep B img m m₁ → MRun B img n m₁ m₂ → MRun B img (n+1) m m₂

theorem MRun.trans {a b m₁ m₂ m₃} (h₁ : MRun B img a m₁ m₂) (h₂ : MRun B img b m₂ m₃) :
    MRun B img (a + b) m₁ m₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | step hm hs _ ih => rw [Nat.add_right_comm]; exact .step hm hs (ih h₂)

theorem MRun.single {m m'} (hm : Masked m) (h : DetStep B img m m') : MRun B img 1 m m' :=
  .step hm h (.refl _)

theorem MRun.toDetSteps {n m m'} (h : MRun B img n m m') : DetSteps B img n m m' := by
  induction h with
  | refl => exact .refl _
  | step _ hs _ ih => exact .step hs ih

/-- From a masked machine with a deterministic step, that step is the only
    transition, and it emits nothing. -/
theorem step_of_masked {m m₁ m' evs} (hm : Masked m) (hd : DetStep B img m m₁)
    (hs : Step B img m m' evs) : m' = m₁ ∧ evs = [] := by
  cases hs with
  | instr o h =>
    rw [hd o] at h
    simp only [Result.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | irq code hen _ => rw [irqEnabled_masked hm] at hen; cases hen

theorem noEscape_of_masked {m m₁} (hm : Masked m) (hd : DetStep B img m m₁) : ¬ Escapes B img m := by
  rintro (⟨o, f, hf⟩ | ⟨code, e, hen, _⟩)
  · exact hd.noFault o f hf
  · rw [irqEnabled_masked hm] at hen; cases hen

/-! ## Safety from a closed invariant -/

/-- The safety property of `check_sound`: no reachable machine escapes and
    every event emitted on the way satisfies `Ok`. -/
def Safe (B : Board) (img : List Segment) (Init : Machine → Prop) (Ok : Event → Prop) : Prop :=
  ∀ m evs, Reach B img Init m evs → ¬ Escapes B img m ∧ ∀ ev ∈ evs, Ok ev

/-- `I` cannot escape, and every transition from it emits allowed events and
    lands in `J`. -/
def StepsInto (B : Board) (img : List Segment) (Ok : Event → Prop) (I J : Machine → Prop) : Prop :=
  ∀ m, I m → ¬ Escapes B img m ∧ ∀ m' evs, Step B img m m' evs → J m' ∧ ∀ ev ∈ evs, Ok ev

theorem safe_of_closed {Init I : Machine → Prop} {Ok : Event → Prop}
    (hinit : ∀ m, Init m → I m) (hc : StepsInto B img Ok I I) : Safe B img Init Ok := by
  have inv : ∀ m evs, Reach B img Init m evs → I m ∧ ∀ ev ∈ evs, Ok ev := by
    intro m evs hr
    induction hr with
    | init h => exact ⟨hinit _ h, by simp⟩
    | step _ hs ih =>
      obtain ⟨hI, hev⟩ := ih
      obtain ⟨hI', hev'⟩ := (hc _ hI).2 _ _ hs
      exact ⟨hI', fun ev hm => (List.mem_append.mp hm).elim (hev ev) (hev' ev)⟩
  intro m evs hr
  exact ⟨(hc _ (inv m evs hr).1).1, (inv m evs hr).2⟩

/-! ## Summaries -/

/-- A directly proved summary of a hard region: from every machine in `Pre`,
    a masked run of at least one instruction ends in `Post`. -/
structure Summary (B : Board) (img : List Segment) where
  Pre : Machine → Prop
  Post : Machine → Prop
  run : ∀ m, Pre m → ∃ n m', MRun B img (n+1) m m' ∧ Post m'

/-- Machines strictly inside a masked run that ends in `I`. -/
def Inside (B : Board) (img : List Segment) (I : Machine → Prop) (m : Machine) : Prop :=
  ∃ j m₁, MRun B img (j+1) m m₁ ∧ I m₁

theorem inside_steps {I : Machine → Prop} {Ok : Event → Prop} :
    StepsInto B img Ok (Inside B img I) (fun m => Inside B img I m ∨ I m) := by
  rintro m ⟨j, m₁, hr, hI⟩
  cases hr with
  | step hm hd hrest =>
    refine ⟨noEscape_of_masked hm hd, fun m' evs hs => ?_⟩
    obtain ⟨rfl, rfl⟩ := step_of_masked hm hd hs
    refine ⟨?_, by simp⟩
    cases j with
    | zero => cases hrest; exact .inr hI
    | succ j => exact .inl ⟨j, m₁, hrest, hI⟩

/-- **Hybrid composition.** An outer invariant `I` (from abstract
    interpretation or any other proof) whose transitions stay in `I` or
    enter a summary's precondition, and a summary whose runs end in `I`,
    give the global safety property from every initial machine in `I` or in
    the summary's precondition. Interrupts are covered: outside the region by
    `I`'s own obligations, inside it because the run is masked. -/
theorem hybrid_sound {Init I : Machine → Prop} {Ok : Event → Prop} (S : Summary B img)
    (hinit : ∀ m, Init m → I m ∨ S.Pre m)
    (hI : StepsInto B img Ok I (fun m => I m ∨ S.Pre m))
    (hpost : ∀ m, S.Post m → I m) :
    Safe B img Init Ok := by
  have pre_inside : ∀ m, S.Pre m → Inside B img I m := fun m h => by
    obtain ⟨n, m', hr, hp⟩ := S.run m h
    exact ⟨n, m', hr, hpost _ hp⟩
  refine safe_of_closed (I := fun m => I m ∨ Inside B img I m) (fun m h => ?_) ?_
  · rcases hinit m h with h | h
    · exact .inl h
    · exact .inr (pre_inside m h)
  · rintro m (h | h)
    · obtain ⟨hne, hs⟩ := hI m h
      refine ⟨hne, fun m' evs hst => ?_⟩
      obtain ⟨h', hev⟩ := hs m' evs hst
      exact ⟨h'.imp id (pre_inside m'), hev⟩
    · obtain ⟨hne, hs⟩ := (inside_steps (Ok := Ok)) m h
      refine ⟨hne, fun m' evs hst => ?_⟩
      obtain ⟨h', hev⟩ := hs m' evs hst
      exact ⟨h'.symm, hev⟩

/-- Several summaries at once: their preconditions and postconditions joined. -/
def Summary.join (S T : Summary B img) : Summary B img where
  Pre m := S.Pre m ∨ T.Pre m
  Post m := S.Post m ∨ T.Post m
  run m h := h.elim
    (fun h => let ⟨n, m', hr, hp⟩ := S.run m h; ⟨n, m', hr, .inl hp⟩)
    (fun h => let ⟨n, m', hr, hp⟩ := T.run m h; ⟨n, m', hr, .inr hp⟩)

/-! ## Outer invariants from an existing safety theorem -/

/-- Machines reachable from `E`. If a safety theorem covers every run from
    `E` (as `check_sound` does for its boot set), this set is a closed
    invariant: a summary may hand over to it at its exit. -/
def ReachFrom (B : Board) (img : List Segment) (E : Machine → Prop) (m : Machine) : Prop :=
  ∃ evs, Reach B img E m evs

theorem reachFrom_steps {E : Machine → Prop} {Ok : Event → Prop} (h : Safe B img E Ok) :
    StepsInto B img Ok (ReachFrom B img E) (ReachFrom B img E) := by
  rintro m ⟨evs, hr⟩
  refine ⟨(h m evs hr).1, fun m' evs' hs => ⟨⟨_, .step hr hs⟩, fun ev hm => ?_⟩⟩
  exact (h m' _ (.step hr hs)).2 ev (List.mem_append_right _ hm)

/-- Sequential composition: a summary from every initial machine, then any
    proof that covers every run from the summary's exit states. -/
theorem seq_sound {Init : Machine → Prop} {Ok : Event → Prop} (S : Summary B img)
    (hinit : ∀ m, Init m → S.Pre m) (hrest : Safe B img S.Post Ok) : Safe B img Init Ok :=
  hybrid_sound (I := ReachFrom B img S.Post) S (fun m h => .inr (hinit m h))
    (fun m h => let ⟨hne, hs⟩ := reachFrom_steps hrest m h
      ⟨hne, fun m' evs hst => let ⟨h', hev⟩ := hs m' evs hst; ⟨.inl h', hev⟩⟩)
    (fun _ h => ⟨[], .init h⟩)

end E5R.Hybrid
