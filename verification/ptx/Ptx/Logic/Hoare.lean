/-
One thread on its own: traces, footprints and a total-correctness logic.

`Safe … J s m` is an inductive (so finite) derivation that the thread, run
alone from `(s, m)`, reaches a state satisfying `J` with every step on the way
legal and every access inside its footprint (`R` may be read, `W` may be read
and written). It is the per-kernel proof obligation; `Solo` is what the grid
theorem (RaceFreedom.lean) consumes, and `Safe.solo` turns one into the other.

`wp` computes a sufficient condition for `Safe` by running the instruction
table up to the next cut point (a set of pcs, e.g. a loop head) or `done`. On a
concrete kernel `simp` evaluates it, leaving only the arithmetic and branch
conditions; `wp_sound` is what makes that evaluation a proof. `Safe.loop` is
the loop rule: an invariant indexed by a decreasing measure.
-/
import Ptx.Semantics.SIMT

namespace Ptx

/-- An access stays in the footprint: stores only in `W`, loads in `R ∪ W`. -/
def InFoot (R W : Addr → Prop) (acc : Addr × Size × Bool) : Prop :=
  ∀ x, covers acc.1 acc.2.1.bytes x → W x ∨ (acc.2.2 = false ∧ R x)

section
variable (K : Kernel) (al : List Region) (c : Ctx)

/-- The thread alone, `k` steps from `(s, m)` (it stays put once it cannot
step). -/
def trace : Nat → TState → Mem → TState × Mem
  | 0, s, m => (s, m)
  | k + 1, s, m =>
    match stepMem K al c s m with
    | .ok s' m' => trace k s' m'
    | _ => (s, m)

/-- The thread alone takes `n` legal steps inside its footprint and then
halts. -/
structure Solo (R W : Addr → Prop) (s₀ : TState) (m₀ : Mem) (n : Nat) : Prop where
  ok : ∀ k < n, ∃ s' m', stepMem K al c (trace K al c k s₀ m₀).1 (trace K al c k s₀ m₀).2 = .ok s' m'
  foot : ∀ k < n, ∀ acc, (action K c (trace K al c k s₀ m₀).1).acc = some acc → InFoot R W acc
  halt : stepMem K al c (trace K al c n s₀ m₀).1 (trace K al c n s₀ m₀).2 = .halted

variable (R W : Addr → Prop)

inductive Safe (J : TState → Mem → Prop) : TState → Mem → Prop
  | stop {s m} : J s m → Safe J s m
  | next {s s' m} : action K c s = .next s' → Safe J s' m → Safe J s m
  | load {s m a sz k} : action K c s = .load a sz k → accessOk al a sz = true →
      InFoot R W (a, sz, false) → Safe J (k (rd m a sz)) m → Safe J s m
  | store {s m a sz v s'} : action K c s = .store a sz v s' → accessOk al a sz = true →
      InFoot R W (a, sz, true) → Safe J s' (wr m a sz v) → Safe J s m

/-- The weakest precondition, up to the next cut point or `done`, by running
the instruction table with `fuel` steps. -/
def wp (cut : Nat → Bool) (Q : TState → Mem → Prop) : Nat → TState → Mem → Prop
  | 0, _, _ => False
  | f + 1, s, m =>
    match action K c s with
    | .next s' => if cut s'.pc then Q s' m else wp cut Q f s' m
    | .load a sz k =>
      accessOk al a sz = true ∧ InFoot R W (a, sz, false) ∧
        (if cut (k (rd m a sz)).pc then Q (k (rd m a sz)) m else wp cut Q f (k (rd m a sz)) m)
    | .store a sz v s' =>
      accessOk al a sz = true ∧ InFoot R W (a, sz, true) ∧
        (if cut s'.pc then Q s' (wr m a sz v) else wp cut Q f s' (wr m a sz v))
    | .done => Q s m
    | .fault => False

end

variable {K : Kernel} {al : List Region} {c : Ctx} {R W : Addr → Prop}

/-- What `wp` stops at: a cut point after at least one step, or `done`. -/
def Stop (K : Kernel) (c : Ctx) (cut : Nat → Bool) (Q : TState → Mem → Prop) (s : TState) (m : Mem) :
    Prop := Q s m ∧ (cut s.pc = true ∨ action K c s = .done)

theorem wp_sound {cut : Nat → Bool} {Q : TState → Mem → Prop} :
    ∀ {f s m}, wp K al c R W cut Q f s m → Safe K al c R W (Stop K c cut Q) s m := by
  intro f
  induction f with
  | zero => intro s m h; exact h.elim
  | succ f ih =>
    intro s m h
    unfold wp at h
    have stopOrGo : ∀ {s' m'}, (if cut s'.pc then Q s' m' else wp K al c R W cut Q f s' m') →
        Safe K al c R W (Stop K c cut Q) s' m' := by
      intro s' m' h'
      by_cases hc : cut s'.pc = true
      · simp only [hc, ↓reduceIte] at h'; exact .stop ⟨h', .inl hc⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h'; exact ih h'
    split at h
    · next s' hs => exact .next hs (stopOrGo h)
    · next a sz k hs => exact .load hs h.1 h.2.1 (stopOrGo h.2.2)
    · next a sz v s' hs => exact .store hs h.1 h.2.1 (stopOrGo h.2.2)
    · next hs => exact .stop ⟨h, .inr hs⟩
    · exact h.elim

theorem Safe.mono {J J' : TState → Mem → Prop} {s m} (h : Safe K al c R W J s m)
    (hJ : ∀ s m, J s m → Safe K al c R W J' s m) : Safe K al c R W J' s m := by
  induction h with
  | stop hj => exact hJ _ _ hj
  | next ha _ ih => exact .next ha ih
  | load ha hok hf _ ih => exact .load ha hok hf ih
  | store ha hok hf _ ih => exact .store ha hok hf ih

theorem Safe.weaken {J J' : TState → Mem → Prop} {s m} (h : Safe K al c R W J s m)
    (hJ : ∀ s m, J s m → J' s m) : Safe K al c R W J' s m :=
  h.mono fun s m hj => .stop (hJ s m hj)

/-- Loop rule: from every invariant state, the thread reaches either a
smaller-measure invariant state or the exit condition. -/
theorem Safe.loop {I : Nat → TState → Mem → Prop} {J : TState → Mem → Prop}
    (step : ∀ v s m, I v s m → Safe K al c R W (fun s m => (∃ v' < v, I v' s m) ∨ J s m) s m) :
    ∀ v s m, I v s m → Safe K al c R W J s m := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro s m hI
    refine (step v s m hI).mono fun s' m' h => ?_
    rcases h with ⟨v', hv, hI'⟩ | hJ
    · exact ih v' hv s' m' hI'
    · exact .stop hJ

theorem trace_succ {k s m s' m'} (h : stepMem K al c s m = .ok s' m') :
    trace K al c (k + 1) s m = trace K al c k s' m' := by
  simp [trace, h]

theorem stepMem_next {s s' m} (h : action K c s = .next s') : stepMem K al c s m = .ok s' m := by
  simp [stepMem, h]

theorem stepMem_load {s m a sz k} (h : action K c s = .load a sz k) (hok : accessOk al a sz = true) :
    stepMem K al c s m = .ok (k (rd m a sz)) m := by
  simp [stepMem, h, hok]

theorem stepMem_store {s m a sz v s'} (h : action K c s = .store a sz v s')
    (hok : accessOk al a sz = true) : stepMem K al c s m = .ok s' (wr m a sz v) := by
  simp [stepMem, h, hok]

/-- A derivation that ends at `done` gives a `Solo` run, and the final state
satisfies the postcondition. -/
theorem Safe.solo {Q : TState → Mem → Prop} {s m}
    (h : Safe K al c R W (fun s m => action K c s = .done ∧ Q s m) s m) :
    ∃ n, Solo K al c R W s m n ∧ Q (trace K al c n s m).1 (trace K al c n s m).2 := by
  induction h with
  | @stop s m hj =>
    refine ⟨0, ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _), ?_⟩, hj.2⟩
    simp [trace, stepMem, hj.1]
  | @next s s' m ha _ ih =>
    obtain ⟨n, hs, hq⟩ := ih
    have hst := stepMem_next (al := al) (m := m) ha
    refine ⟨n + 1, ⟨?_, ?_, ?_⟩, by rw [trace_succ hst]; exact hq⟩
    · intro k hk
      cases k with
      | zero => exact ⟨s', m, by simpa [trace] using hst⟩
      | succ k => rw [trace_succ hst]; exact hs.ok k (by omega)
    · intro k hk acc hacc
      cases k with
      | zero => simp [trace, ha, Action.acc] at hacc
      | succ k => rw [trace_succ hst] at hacc; exact hs.foot k (by omega) acc hacc
    · rw [trace_succ hst]; exact hs.halt
  | @load s m a sz k ha hok hf _ ih =>
    obtain ⟨n, hs, hq⟩ := ih
    have hst := stepMem_load (m := m) ha hok
    refine ⟨n + 1, ⟨?_, ?_, ?_⟩, by rw [trace_succ hst]; exact hq⟩
    · intro j hj
      cases j with
      | zero => exact ⟨_, m, by simpa [trace] using hst⟩
      | succ j => rw [trace_succ hst]; exact hs.ok j (by omega)
    · intro j hj acc hacc
      cases j with
      | zero => simp [trace, ha, Action.acc] at hacc; subst hacc; exact hf
      | succ j => rw [trace_succ hst] at hacc; exact hs.foot j (by omega) acc hacc
    · rw [trace_succ hst]; exact hs.halt
  | @store s m a sz v s' ha hok hf _ ih =>
    obtain ⟨n, hs, hq⟩ := ih
    have hst := stepMem_store (m := m) ha hok
    refine ⟨n + 1, ⟨?_, ?_, ?_⟩, by rw [trace_succ hst]; exact hq⟩
    · intro j hj
      cases j with
      | zero => exact ⟨_, _, by simpa [trace] using hst⟩
      | succ j => rw [trace_succ hst]; exact hs.ok j (by omega)
    · intro j hj acc hacc
      cases j with
      | zero => simp [trace, ha, Action.acc] at hacc; subst hacc; exact hf
      | succ j => rw [trace_succ hst] at hacc; exact hs.foot j (by omega) acc hacc
    · rw [trace_succ hst]; exact hs.halt

end Ptx
