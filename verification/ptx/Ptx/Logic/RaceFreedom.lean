/-
From per-thread proofs to the whole grid.

`grid_sound` is proved once, for every kernel of the subset. Its hypotheses
are per thread: thread `t`, run alone from the initial memory, halts after
legal steps whose loads stay in `R t ∪ W t` and whose stores stay in `W t`
(`Solo`), ending in a memory with property `P t`; and no thread writes a byte
another thread reads or writes (`hdisj`). Reads may overlap.

Its conclusion is about every interleaving of the grid (`Reach`/`Steps`):

* no reachable configuration faults (bounds, alignment, unsupported forms);
* every reachable configuration has finished or can step, and no execution is
  longer than the sum of the per-thread step counts, so every execution
  terminates and ends with every thread finished;
* no two threads ever make conflicting accesses (`RaceFree`);
* when all threads have finished, each byte a thread owns holds what that
  thread's solo run left there, and every byte no thread owns is unchanged.

The proof keeps, for each reachable configuration, how far each thread has
come along its solo trace, and shows the shared memory agrees with that
thread's solo memory on everything it can touch.
-/
import Ptx.Logic.Hoare

namespace Ptx

section
variable {K : Kernel} {al : List Region} {c : Ctx}

theorem trace_succ_back : ∀ {k s m s' m'},
    stepMem K al c (trace K al c k s m).1 (trace K al c k s m).2 = .ok s' m' →
    trace K al c (k + 1) s m = (s', m') := by
  intro k
  induction k with
  | zero => intro s m s' m' h; simp only [trace] at h ⊢; rw [h]
  | succ k ih =>
    intro s m s' m' h
    unfold trace at h ⊢
    split
    · next s₁ m₁ h₁ => rw [h₁] at h; exact ih h
    · next hne => exact absurd (by simp at h; exact h) (by
        intro h'; cases hs : stepMem K al c s m <;> simp_all)

theorem stepMem_halted {s m} : stepMem K al c s m = .halted → action K c s = .done := by
  unfold stepMem; split <;> (try split) <;> simp_all

theorem stepMem_halted_of_done {s m} (h : action K c s = .done) : stepMem K al c s m = .halted := by
  simp [stepMem, h]

/-- The solo run only changes bytes in `W`. -/
theorem Solo.frame {R W : Addr → Prop} {s₀ m₀ n} (hs : Solo K al c R W s₀ m₀ n) :
    ∀ k ≤ n, ∀ x, ¬ W x → (trace K al c k s₀ m₀).2 x = m₀ x := by
  intro k
  induction k with
  | zero => intro _ x _; rfl
  | succ k ih =>
    intro hk x hx
    obtain ⟨s', m', hst⟩ := hs.ok k (by omega)
    rw [trace_succ_back hst]
    have hprev := ih (by omega) x hx
    revert hst
    unfold stepMem
    split
    · next hA => intro h; cases h; exact hprev
    · next a sz kk hA =>
      split
      · intro h; cases h; exact hprev
      · intro h; cases h
    · next a sz v s'' hA =>
      split
      · intro h; cases h
        have hf := hs.foot k (by omega) (a, sz, true) (by simp [hA, Action.acc])
        have : ¬ covers a sz.bytes x := fun hc => by
          rcases hf x hc with h | ⟨h, _⟩
          · exact hx h
          · simp at h
        show wr _ a sz v x = m₀ x
        rw [wr_outside this]; exact hprev
      · intro h; cases h
    · intro h; cases h
    · intro h; cases h

end

theorem sum_le_of_le {l : List Tid} {f g : Tid → Nat} (h : ∀ t ∈ l, f t ≤ g t) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp); have := ih (fun t ht => h t (by simp [ht])); omega

/-- Lowering one member's value by one lowers the sum by at least one. -/
theorem sum_lt_of_dec {l : List Tid} {f g : Tid → Nat} {t : Tid} (ht : t ∈ l)
    (hlt : g t < f t) (hle : ∀ u ∈ l, g u ≤ f u) : (l.map g).sum + 1 ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hl : ∀ u ∈ l, g u ≤ f u := fun u hu => hle u (by simp [hu])
    have ha := hle a (by simp)
    by_cases hta : t = a
    · subst hta; have := sum_le_of_le hl; omega
    · have : t ∈ l := by simp [hta] at ht; exact ht
      have := ih this hl; omega

section
variable (K : Kernel) (L : Launch) (r0 : Tid → String → Val) (p0 : Tid → String → Bool) (m0 : Mem)
variable (R W : Tid → Addr → Prop) (n : Tid → Nat)

abbrev s0 (t : Tid) : TState := (Cfg.init r0 p0 m0).ts t

abbrev soloAt (t : Tid) (k : Nat) : TState × Mem := trace K L.alloc (L.ctx t) k (s0 r0 p0 m0 t) m0

/-- The configuration is the composition of the solo runs, each `k t` steps in. -/
structure Inv (k : Tid → Nat) (c : Cfg) : Prop where
  le : ∀ t ∈ L.threads, k t ≤ n t
  ts : ∀ t ∈ L.threads, c.ts t = (soloAt K L r0 p0 m0 t (k t)).1
  own : ∀ t ∈ L.threads, ∀ x, W t x → c.mem x = (soloAt K L r0 p0 m0 t (k t)).2 x
  rest : ∀ x, (∀ t ∈ L.threads, ¬ W t x) → c.mem x = m0 x

end

section
variable {K : Kernel} {L : Launch} {r0 : Tid → String → Val} {p0 : Tid → String → Bool} {m0 : Mem}
variable {R W : Tid → Addr → Prop} {n : Tid → Nat}

theorem inv_halted {k c t} (hI : Inv K L r0 p0 m0 W n k c) (ht : t ∈ L.threads)
    (hsolo : Solo K L.alloc (L.ctx t) (R t) (W t) (s0 r0 p0 m0 t) m0 (n t)) (heq : k t = n t) :
    c.res K L t = .halted := by
  have := hsolo.halt
  rw [← heq] at this
  unfold Cfg.res; rw [hI.ts t ht]
  exact stepMem_halted_of_done (stepMem_halted this)

theorem inv_step {k c t}
    (hI : Inv K L r0 p0 m0 W n k c) (ht : t ∈ L.threads)
    (hsolo : ∀ t ∈ L.threads, Solo K L.alloc (L.ctx t) (R t) (W t) (s0 r0 p0 m0 t) m0 (n t))
    (hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x, W t x → ¬ R u x ∧ ¬ W u x)
    (hlt : k t < n t) :
    ∃ s' m', c.res K L t = .ok s' m' ∧
      Inv K L r0 p0 m0 W n (fun u => if u = t then k t + 1 else k u)
        { ts := updT c.ts t s', mem := m' } := by
  have hs := hsolo t ht
  obtain ⟨S', M', hst⟩ := hs.ok (k t) hlt
  have htr := trace_succ_back hst
  have hfoot := hs.foot (k t) hlt
  rcases hS : trace K L.alloc (L.ctx t) (k t) (s0 r0 p0 m0 t) m0 with ⟨S, M⟩
  rw [hS] at hst hfoot
  dsimp only at hst hfoot
  have hts : c.ts t = S := by rw [hI.ts t ht]; simp only [soloAt, hS]
  have hown : ∀ x, W t x → c.mem x = M x := fun x hx => by
    rw [hI.own t ht x hx]; simp only [soloAt, hS]
  have hM : ∀ x, ¬ W t x → M x = m0 x := fun x hx => by
    have := hs.frame (k t) (Nat.le_of_lt hlt) x hx
    rw [hS] at this; exact this
  -- the shared memory agrees with the solo memory on the thread's footprint
  have hagree : ∀ x, (W t x ∨ R t x) → c.mem x = M x := by
    intro x hx
    by_cases hw : W t x
    · exact hown x hw
    · have hr : R t x := hx.resolve_left hw
      rw [hI.rest x, hM x hw]
      intro u hu hwu
      by_cases hut : u = t
      · subst hut; exact hw hwu
      · exact (hdisj u hu t ht hut x hwu).1 hr
  -- the new invariant, given the step's effect on memory
  have finish : ∀ m', (∀ x, (∀ u ∈ L.threads, u ≠ t → W u x → m' x = c.mem x)) →
      (∀ x, (∀ u ∈ L.threads, ¬ W u x) → m' x = c.mem x) →
      (∀ x, W t x → m' x = M' x) →
      Inv K L r0 p0 m0 W n (fun u => if u = t then k t + 1 else k u)
        { ts := updT c.ts t S', mem := m' } := by
    intro m' hoth hrest hmine
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu; by_cases h : u = t
      · subst h; simp; omega
      · simp [h]; exact hI.le u hu
    · intro u hu; by_cases h : u = t
      · subst h; simp [updT, htr]
      · simp [updT, h]; exact hI.ts u hu
    · intro u hu x hx; by_cases h : u = t
      · subst h; simp [htr]; exact hmine x hx
      · simp [h]; rw [hoth x u hu h hx]; exact hI.own u hu x hx
    · intro x hx; show m' x = m0 x; rw [hrest x hx]; exact hI.rest x hx
  unfold Cfg.res; rw [hts]
  revert hfoot hst
  unfold stepMem
  split
  · next s'' hA =>
    intro _ hst; injection hst with h1 h2; subst h1 h2
    exact ⟨_, _, rfl, finish c.mem (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) hown⟩
  · next a sz kk hA =>
    split
    · next hok =>
      intro hfoot hst; injection hst with h1 h2; subst h1 h2
      have hf := hfoot (a, sz, false) (by simp [hA, Action.acc])
      have hrd : rd c.mem a sz = rd M a sz := rd_congr fun x hx => by
        apply hagree; rcases hf x hx with h | ⟨_, h⟩
        · exact .inl h
        · exact .inr h
      refine ⟨_, _, rfl, ?_⟩
      rw [hrd]; exact finish c.mem (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) hown
    · intro _ h; cases h
  · next a sz v s'' hA =>
    split
    · next hok =>
      intro hfoot hst; injection hst with h1 h2; subst h1 h2
      have hf := hfoot (a, sz, true) (by simp [hA, Action.acc])
      have hcov : ∀ x, covers a sz.bytes x → W t x := fun x hx => by
        rcases hf x hx with h | ⟨h, _⟩
        · exact h
        · simp at h
      refine ⟨_, _, rfl, finish _ ?_ ?_ ?_⟩
      · intro x u hu hut hwu
        apply wr_outside; intro hx
        exact (hdisj t ht u hu (Ne.symm hut) x (hcov x hx)).2 hwu
      · intro x hx; apply wr_outside; intro hc; exact hx t ht (hcov x hc)
      · intro x hx
        by_cases hc : covers a sz.bytes x
        · rw [wr_inside hc, wr_inside hc]
        · rw [wr_outside hc, wr_outside hc]; exact hown x hx
    · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

/-- What `grid_sound` proves about every execution of the launch. -/
structure GridOk (K : Kernel) (L : Launch) (c₀ : Cfg) (W : Tid → Addr → Prop)
    (P : Tid → Mem → Prop) (bound : Nat) : Prop where
  noFault : ∀ c, Reach K L c₀ c → ¬ Faults K L c
  progress : ∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c'
  bounded : ∀ j c, Steps K L j c₀ c → j ≤ bound
  raceFree : RaceFree K L c₀
  final : ∀ c, Reach K L c₀ c → Done K L c →
    (∀ t ∈ L.threads, ∃ M, P t M ∧ ∀ x, W t x → c.mem x = M x) ∧
    (∀ x, (∀ t ∈ L.threads, ¬ W t x) → c.mem x = c₀.mem x)

theorem inv_reach
    (hsolo : ∀ t ∈ L.threads, Solo K L.alloc (L.ctx t) (R t) (W t) (s0 r0 p0 m0 t) m0 (n t))
    (hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x, W t x → ¬ R u x ∧ ¬ W u x) :
    ∀ j c, Steps K L j (Cfg.init r0 p0 m0) c → ∃ k, Inv K L r0 p0 m0 W n k c ∧
      j + (L.threads.map fun t => n t - k t).sum ≤ (L.threads.map n).sum := by
  intro j c h
  generalize hc0 : Cfg.init r0 p0 m0 = c0 at h
  induction h with
  | refl =>
    subst hc0
    refine ⟨fun _ => 0, ⟨fun _ _ => Nat.zero_le _, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => rfl⟩, ?_⟩
    simp
  | @tail j c₁ c₂ c₃ _ hstep ih =>
    obtain ⟨k, hI, hsum⟩ := ih hc0
    obtain ⟨t, ht, s', m', hres, rfl⟩ := hstep
    have hlt : k t < n t := by
      rcases Nat.lt_or_ge (k t) (n t) with h | h
      · exact h
      · have := inv_halted hI ht (hsolo t ht) (Nat.le_antisymm (hI.le t ht) h)
        rw [hres] at this; cases this
    obtain ⟨s'', m'', hres', hI'⟩ := inv_step hI ht hsolo hdisj hlt
    rw [hres] at hres'; cases hres'
    refine ⟨_, hI', ?_⟩
    have := sum_lt_of_dec (l := L.threads) (f := fun u => n u - k u)
      (g := fun u => n u - (if u = t then k t + 1 else k u)) ht (by simp; omega)
      (by intro u _; by_cases h : u = t <;> simp [h]; omega)
    omega

theorem grid_sound {P : Tid → Mem → Prop}
    (hsolo : ∀ t ∈ L.threads, ∃ n, Solo K L.alloc (L.ctx t) (R t) (W t) (s0 r0 p0 m0 t) m0 n ∧
      P t (trace K L.alloc (L.ctx t) n (s0 r0 p0 m0 t) m0).2)
    (hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x, W t x → ¬ R u x ∧ ¬ W u x) :
    ∃ bound, GridOk K L (Cfg.init r0 p0 m0) W P bound := by
  classical
  let n : Tid → Nat := fun t => if h : t ∈ L.threads then Classical.choose (hsolo t h) else 0
  have hn : ∀ t (h : t ∈ L.threads), n t = Classical.choose (hsolo t h) := fun t h => by simp [n, h]
  have hS : ∀ t ∈ L.threads, Solo K L.alloc (L.ctx t) (R t) (W t) (s0 r0 p0 m0 t) m0 (n t) :=
    fun t h => by rw [hn t h]; exact (Classical.choose_spec (hsolo t h)).1
  have hP : ∀ t ∈ L.threads, P t (soloAt K L r0 p0 m0 t (n t)).2 :=
    fun t h => by rw [hn t h]; exact (Classical.choose_spec (hsolo t h)).2
  have reachInv : ∀ c, Reach K L (Cfg.init r0 p0 m0) c → ∃ k, Inv K L r0 p0 m0 W n k c := by
    intro c hc
    obtain ⟨j, hj⟩ := hc.steps
    obtain ⟨k, hk, _⟩ := inv_reach hS hdisj j c hj
    exact ⟨k, hk⟩
  -- every thread is either finished (at the end of its trace) or can step
  have status : ∀ k c, Inv K L r0 p0 m0 W n k c → ∀ t ∈ L.threads,
      (k t = n t ∧ c.res K L t = .halted) ∨ (k t < n t ∧ ∃ s' m', c.res K L t = .ok s' m') := by
    intro k c hI t ht
    rcases Nat.lt_or_ge (k t) (n t) with h | h
    · obtain ⟨s', m', hr, _⟩ := inv_step hI ht hS hdisj h
      exact .inr ⟨h, s', m', hr⟩
    · have heq := Nat.le_antisymm (hI.le t ht) h
      exact .inl ⟨heq, inv_halted hI ht (hS t ht) heq⟩
  refine ⟨(L.threads.map n).sum, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c hc ⟨t, ht, hf⟩
    obtain ⟨k, hI⟩ := reachInv c hc
    rcases status k c hI t ht with ⟨_, h⟩ | ⟨_, s', m', h⟩ <;> rw [h] at hf <;> cases hf
  · intro c hc
    obtain ⟨k, hI⟩ := reachInv c hc
    by_cases hd : Done K L c
    · exact .inl hd
    · right
      have : ∃ t ∈ L.threads, c.res K L t ≠ .halted :=
        Classical.byContradiction fun h' => hd fun t ht =>
          Classical.byContradiction fun h'' => h' ⟨t, ht, h''⟩
      obtain ⟨t, ht, hnh⟩ := this
      rcases status k c hI t ht with ⟨_, h⟩ | ⟨_, s', m', h⟩
      · exact absurd h hnh
      · exact ⟨_, t, ht, s', m', h, rfl⟩
  · intro j c hj
    obtain ⟨k, _, hsum⟩ := inv_reach hS hdisj j c hj
    omega
  · intro c₁ c₂ h₁ h₂ t ht u hu htu x y hx hy ⟨hw, b, hbx, hby⟩
    obtain ⟨k₁, hI₁⟩ := reachInv c₁ h₁
    obtain ⟨k₂, hI₂⟩ := reachInv c₂ h₂
    have footOf : ∀ k c, Inv K L r0 p0 m0 W n k c → ∀ v ∈ L.threads, ∀ z,
        c.pending K L v = some z → InFoot (R v) (W v) z := by
      intro k c hI v hv z hz
      unfold Cfg.pending at hz
      rw [hI.ts v hv] at hz
      rcases Nat.lt_or_ge (k v) (n v) with h | h
      · exact (hS v hv).foot (k v) h z hz
      · have heq := Nat.le_antisymm (hI.le v hv) h
        have := stepMem_halted (hS v hv).halt
        rw [← heq] at this
        simp only [soloAt] at hz; rw [this] at hz; simp [Action.acc] at hz
    have fx := footOf k₁ c₁ hI₁ t ht x hx b hbx
    have fy := footOf k₂ c₂ hI₂ u hu y hy b hby
    rcases hw with hw | hw
    · have hWt : W t b := by rcases fx with h | ⟨h, _⟩; exact h; rw [hw] at h; cases h
      have := hdisj t ht u hu htu b hWt
      rcases fy with h | ⟨_, h⟩
      · exact this.2 h
      · exact this.1 h
    · have hWu : W u b := by rcases fy with h | ⟨h, _⟩; exact h; rw [hw] at h; cases h
      have := hdisj u hu t ht (Ne.symm htu) b hWu
      rcases fx with h | ⟨_, h⟩
      · exact this.2 h
      · exact this.1 h
  · intro c hc hd
    obtain ⟨k, hI⟩ := reachInv c hc
    have hk : ∀ t ∈ L.threads, k t = n t := fun t ht => by
      rcases status k c hI t ht with ⟨h, _⟩ | ⟨_, s', m', h⟩
      · exact h
      · have := hd t ht; rw [h] at this; cases this
    refine ⟨fun t ht => ⟨_, hP t ht, fun x hx => by rw [hI.own t ht x hx, hk t ht]⟩, ?_⟩
    intro x hx; exact hI.rest x hx

end

end Ptx
