/-
Refutations: what a counterexample has to show, in the grid semantics.

A buggy kernel is refuted by a concrete launch and initial state plus a
reachable configuration that faults, races or finishes with a wrong result.
`reach_thread` makes such configurations easy to exhibit: running one thread
alone for `j` legal steps, leaving every other thread where it is, is one of
the interleavings. The configurations are then evaluated by `simp`, so a
refutation is a kernel-checked theorem like the proofs, not a test.
-/
import Ptx.Logic.RaceFreedom

namespace Ptx

/-- Thread `t` run alone for `j` global-only steps from configuration `c`. -/
def Cfg.advance (K : Kernel) (L : Launch) (c : Cfg) (t : Tid) (j : Nat) : Cfg :=
  let r := trace K L.alloc (L.ctx t) j (c.ts t) c.mem
  { c with ts := updT c.ts t r.1, mem := r.2 }

theorem updT_same (f : Tid → TState) (t : Tid) (s : TState) : updT f t s t = s := by simp [updT]

theorem updT_updT (f : Tid → TState) (t : Tid) (s s' : TState) :
    updT (updT f t s) t s' = updT f t s' := by
  funext u; by_cases h : u = t <;> simp [updT, h]

theorem updT_self (f : Tid → TState) (t : Tid) : updT f t (f t) = f := by
  funext u; by_cases h : u = t <;> simp [updT, h]

theorem reach_thread {K : Kernel} {L : Launch} {c : Cfg} {t : Tid} (ht : t ∈ L.threads) :
    ∀ j, (∀ i < j, ∃ s' m', stepMem K L.alloc (L.ctx t) (trace K L.alloc (L.ctx t) i (c.ts t) c.mem).1
      (trace K L.alloc (L.ctx t) i (c.ts t) c.mem).2 = .ok s' m') →
    Reach K L c (c.advance K L t j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have : c.advance K L t 0 = c := by
      simp only [Cfg.advance, trace, updT_self]
    rw [this]; exact .refl _
  | succ j ih =>
    intro h
    have hr := ih fun i hi => h i (by omega)
    obtain ⟨s', m', hs⟩ := h j (by omega)
    refine .tail hr (.inl ⟨t, ht, s', ⟨m', c.sh t.ctaid⟩, ?_, ?_⟩)
    · exact res_of_stepMem (c := c.advance K L t j) (by simp only [Cfg.advance, updT_same]; exact hs)
    · simp only [Cfg.advance, Cfg.write, trace_succ_back hs, updT_updT]
      congr; funext d; by_cases h : d = t.ctaid <;> simp [updC, h]

theorem Reach.trans {K L} {c₁ c₂ c₃ : Cfg} (h₁ : Reach K L c₁ c₂) (h₂ : Reach K L c₂ c₃) :
    Reach K L c₁ c₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

/-- `j` legal steps of one thread, front to back, so `simp` can evaluate it. -/
def okSteps (K : Kernel) (al : List Region) (c : Ctx) : Nat → TState → Mem → Prop
  | 0, _, _ => True
  | j + 1, s, m =>
    match stepMem K al c s m with
    | .ok s' m' => okSteps K al c j s' m'
    | _ => False

theorem okSteps_trace {K al c} : ∀ {j s m}, okSteps K al c j s m →
    ∀ i < j, ∃ s' m', stepMem K al c (trace K al c i s m).1 (trace K al c i s m).2 = .ok s' m' := by
  intro j
  induction j with
  | zero => intro _ _ _ i hi; omega
  | succ j ih =>
    intro s m h i hi
    unfold okSteps at h
    split at h
    · next s' m' hs =>
      cases i with
      | zero => exact ⟨s', m', by simpa [trace] using hs⟩
      | succ i => rw [trace_succ hs]; exact ih h i (by omega)
    · exact h.elim

theorem reach_thread' {K : Kernel} {L : Launch} {c : Cfg} {t : Tid} (ht : t ∈ L.threads) {j : Nat}
    (h : okSteps K L.alloc (L.ctx t) j (c.ts t) c.mem) : Reach K L c (c.advance K L t j) :=
  reach_thread ht j (okSteps_trace h)

end Ptx
