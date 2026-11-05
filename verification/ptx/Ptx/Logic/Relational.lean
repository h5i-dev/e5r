/- Direct equivalence of concrete PTX executions. The premises relate two
finite solo traces; no mathematical output function or operator spec occurs.
The grid theorem lifts this relation to every pair of interleavings. -/
import Ptx.Logic.Launch1D

namespace Ptx.Relational

/-- Safety, progress, bounded execution, race freedom and an actual final run. -/
def Total (K : Kernel) (L : Launch) (c₀ : Cfg) : Prop :=
  (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
  (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
  (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
  RaceFree K L c₀ ∧ (∃ c, Reach K L c₀ c ∧ Done K L c)

/-- Global bytes outside all launched thread write footprints are preserved. -/
def Frame (K : Kernel) (L : Launch) (c₀ : Cfg) (W : Tid → Addr → Prop) : Prop :=
  ∀ c, Reach K L c₀ c → Done K L c → ∀ x,
    (∀ t ∈ L.threads, ¬ W t x) → c.mem x = c₀.mem x

/-- Observable global memory equality, including bytes outside the outputs.
Both sides terminate safely; the final configurations are independently
quantified, so this is not equality under an arbitrary paired schedule. -/
def Equivalent (K₀ K₁ : Kernel) (L : Launch) (c₀ : Cfg) (W : Tid → Addr → Prop) : Prop :=
  K₀.shared = [] ∧ K₁.shared = [] ∧ Total K₀ L c₀ ∧ Total K₁ L c₀ ∧
  (∀ c d, Reach K₀ L c₀ c → Done K₀ L c →
    Reach K₁ L c₀ d → Done K₁ L d → c.mem = d.mem) ∧
  Frame K₀ L c₀ W ∧ Frame K₁ L c₀ W

/-- Direct relation on concrete traces, allowing different step counts,
registers, branch structure and intermediate memories. -/
def Paired (K₀ K₁ : Kernel) (L : Launch) (R W : Tid → Addr → Prop)
    (r : Tid → String → Val) (p : Tid → String → Bool) (m : Mem) : Prop :=
  ∀ t ∈ L.threads, ∃ n₀ n₁,
    Solo K₀ L.alloc (L.ctx t) (R t) (W t) (s0 r p m t) m n₀ ∧
    Solo K₁ L.alloc (L.ctx t) (R t) (W t) (s0 r p m t) m n₁ ∧
    ∀ x, W t x →
      (trace K₀ L.alloc (L.ctx t) n₀ (s0 r p m t) m).2 x =
      (trace K₁ L.alloc (L.ctx t) n₁ (s0 r p m t) m).2 x

/-- Lift related solo executions using disjoint ownership. Final memory is
related directly to the other concrete program, never through a shared spec. -/
theorem equivalent_of_paired {K₀ K₁ L R W r p m}
    (h₀ : K₀.shared = []) (h₁ : K₁.shared = [])
    (pair : Paired K₀ K₁ L R W r p m)
    (disj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x,
      W t x → ¬ R u x ∧ ¬ W u x) (sh : Dim3 → Mem) :
    Equivalent K₀ K₁ L (Cfg.init r p m sh) W := by
  classical
  let n₀ : Tid → Nat := fun t => if h : t ∈ L.threads then (pair t h).choose else 0
  let n₁ : Tid → Nat := fun t => if h : t ∈ L.threads then (pair t h).choose_spec.choose else 0
  have hp : ∀ t ∈ L.threads,
      Solo K₀ L.alloc (L.ctx t) (R t) (W t) (s0 r p m t) m (n₀ t) ∧
      Solo K₁ L.alloc (L.ctx t) (R t) (W t) (s0 r p m t) m (n₁ t) ∧
      ∀ x, W t x →
        (trace K₀ L.alloc (L.ctx t) (n₀ t) (s0 r p m t) m).2 x =
        (trace K₁ L.alloc (L.ctx t) (n₁ t) (s0 r p m t) m).2 x := by
    intro t ht
    simpa only [n₀, n₁, dite_eq_left ht] using (pair t ht).choose_spec.choose_spec
  let M₀ := fun t => (trace K₀ L.alloc (L.ctx t) (n₀ t) (s0 r p m t) m).2
  let M₁ := fun t => (trace K₁ L.alloc (L.ctx t) (n₁ t) (s0 r p m t) m).2
  obtain ⟨b₀,g₀⟩ := grid_sound (P := fun t M => ∀ x, W t x → M x = M₀ t x)
    (fun t ht => ⟨n₀ t,(hp t ht).1,fun _ _ => rfl⟩) disj sh
  obtain ⟨b₁,g₁⟩ := grid_sound (P := fun t M => ∀ x, W t x → M x = M₁ t x)
    (fun t ht => ⟨n₁ t,(hp t ht).2.1,fun _ _ => rfl⟩) disj sh
  refine ⟨h₀,h₁,⟨g₀.noFault,g₀.progress,⟨b₀,g₀.bounded⟩,g₀.raceFree,g₀.exists_done⟩,
    ⟨g₁.noFault,g₁.progress,⟨b₁,g₁.bounded⟩,g₁.raceFree,g₁.exists_done⟩,?_,?_,?_⟩
  · intro c d hc hcd hd hdd
    obtain ⟨fc,framec⟩ := g₀.final c hc hcd
    obtain ⟨fd,framed⟩ := g₁.final d hd hdd
    funext x
    by_cases hw : ∃ t ∈ L.threads, W t x
    · obtain ⟨t,ht,hx⟩ := hw
      obtain ⟨C,hC,hcx⟩ := fc t ht
      obtain ⟨D,hD,hdx⟩ := fd t ht
      exact (hcx x hx).trans ((hC x hx).trans
        (((hp t ht).2.2 x hx).trans ((hD x hx).symm.trans (hdx x hx).symm)))
    · have hx : ∀ t ∈ L.threads, ¬ W t x := fun t ht h => hw ⟨t,ht,h⟩
      exact (framec x hx).trans (framed x hx).symm
  · intro c hc hd
    exact (g₀.final c hc hd).2
  · intro c hc hd
    exact (g₁.final c hc hd).2

/-- A convenient way to establish the relational premise by nested symbolic
execution: run the original, then run the candidate with a postcondition that
compares directly with the original's final memory. -/
theorem paired_of_safe {K₀ K₁ L R W r p m}
    (h : ∀ t ∈ L.threads,
      Safe K₀ L.alloc (L.ctx t) (R t) (W t) (fun s M₀ =>
        action K₀ (L.ctx t) s = .done ∧
        Safe K₁ L.alloc (L.ctx t) (R t) (W t) (fun s M₁ =>
          action K₁ (L.ctx t) s = .done ∧ ∀ x, W t x → M₀ x = M₁ x)
          (s0 r p m t) m) (s0 r p m t) m) : Paired K₀ K₁ L R W r p m := by
  intro t ht
  obtain ⟨n₀,h₀,h₁⟩ := (h t ht).solo
  obtain ⟨n₁,h₁,heq⟩ := h₁.solo
  exact ⟨n₀,n₁,h₀,h₁,heq⟩

end Ptx.Relational
