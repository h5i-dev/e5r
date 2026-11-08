import Theories.Logic
namespace E5R.Thermostat.Trace
open E5R

/-- A finite deterministic run whose every instruction boundary masks IRQs.
    Terminal boundaries are included so that they can be used as loop cutpoints. -/
inductive Closed (B : Board) (img : List Segment) : Nat → Machine → Machine → Prop
  | done {m} : m.core.mie_ = false → Closed B img 0 m m
  | next {n m m₁ m₂} : m.core.mie_ = false → DetStep B img m m₁ →
      Closed B img n m₁ m₂ → Closed B img (n+1) m m₂

theorem disabled {B img n m d} (h : Closed B img n m d) : m.core.mie_ = false := by
  cases h with
  | done hm => exact hm
  | next hm _ _ => exact hm

theorem deterministic {B img n m d} (h : Closed B img n m d) : DetSteps B img n m d := by
  induction h with
  | done _ => exact .refl _
  | next _ hs _ ih => exact .step hs ih

theorem trans {B img n k m d e} (h : Closed B img n m d) (h' : Closed B img k d e) :
    Closed B img (n+k) m e := by
  induction h with
  | done _ => simpa using h'
  | next hm hs _ ih => rw [Nat.add_right_comm]; exact .next hm hs (ih h')

/-- Any platform Step at a deterministic, IRQ-masked boundary agrees with it.
    This explicitly excludes interrupt interleavings via the actual Step rule. -/
theorem unique_step {B img m d e evs} (hs : DetStep B img m d) (hm : m.core.mie_ = false)
    (h : Step B img m e evs) : e = d ∧ evs = [] := by
  cases h with
  | instr o he =>
    rw [hs o] at he
    cases he
    exact ⟨rfl,rfl⟩
  | irq code hen _ => simp [irqEnabled,hm] at hen

theorem no_escape {B img m d} (hs : DetStep B img m d) (hm : m.core.mie_ = false) :
    ¬Escapes B img m := by
  rintro (⟨o,f,hf⟩ | ⟨code,e,hen,_⟩)
  · rw [hs o] at hf
    cases hf
  · simp [irqEnabled,hm] at hen

/-- Every strict prefix is safe, and every platform execution prefix follows
    the same finite instruction run. The endpoint is deliberately not claimed
    safe unless the next segment also has a certificate. -/
theorem safe_prefix {B img n m d} (h : Closed B img n m d) :
    (n = 0 ∧ m = d) ∨
      (¬Escapes B img m ∧ ∃ m₁ k, n = k+1 ∧ Closed B img k m₁ d ∧
        ∀ e evs, Step B img m e evs → e = m₁ ∧ evs = []) := by
  cases h with
  | done _ => exact .inl ⟨rfl,rfl⟩
  | next hm hs tail =>
    exact .inr ⟨no_escape hs hm,_,_,rfl,tail,fun _ _ => unique_step hs hm⟩

/-- Intermediate states retain a certified remaining suffix to an invariant
    cutpoint. This does not assert the committed invariant during field stores. -/
def Envelope (B : Board) (img : List Segment) (I : Machine → Prop) (m : Machine) : Prop :=
  ∃ n d, Closed B img n m d ∧ I d

/-- A productive collection of certified segments composes under the actual
    Reach relation. No environment or UART progress is hidden in this rule. -/
theorem loop_safety {B img} (I : Machine → Prop)
    (segments : ∀ m, I m → ∃ n d, 0 < n ∧ Closed B img n m d ∧ I d) :
    ∀ m evs, Reach B img I m evs → Envelope B img I m ∧ evs = [] ∧ ¬Escapes B img m := by
  have advance : ∀ m, Envelope B img I m →
      ¬Escapes B img m ∧ ∀ e evs, Step B img m e evs → Envelope B img I e ∧ evs = [] := by
    intro m ⟨n,d,h,hi⟩
    have process : ∀ n d, 0 < n → Closed B img n m d → I d →
        ¬Escapes B img m ∧ ∀ e evs, Step B img m e evs → Envelope B img I e ∧ evs = [] := by
      intro n d hn hc hi
      cases hc with
      | done _ => omega
      | next hm hs tail =>
        refine ⟨no_escape hs hm,?_⟩
        intro e evs he
        obtain ⟨rfl,rfl⟩ := unique_step hs hm he
        exact ⟨⟨_,_,tail,hi⟩,rfl⟩
    cases n with
    | zero =>
      cases h
      obtain ⟨n,d,hn,h,hi⟩ := segments m hi
      exact process n d hn h hi
    | succ n => exact process (n+1) d (by omega) h hi
  intro m evs hr
  induction hr with
  | init hi =>
    obtain ⟨n,d,hn,h,hd⟩ := segments _ hi
    have he : Envelope B img I _ := ⟨n,d,h,hd⟩
    exact ⟨he,rfl,(advance _ he).1⟩
  | step _ hs ih =>
    obtain ⟨he,hev⟩ := (advance _ ih.1).2 _ _ hs
    exact ⟨he,by simp [ih.2.1,hev],(advance _ he).1⟩
end E5R.Thermostat.Trace
