/- Direct execution equivalence across different launches and thread ownership.
The relation compares concrete solo traces, never a shared operator spec. -/
import Ptx.Logic.Relational

namespace Ptx.Relational

/-- Total correctness and equal observable memory for independently completed
executions, with each side's own launch and write ownership. -/
def EquivalentLaunches (K₀ K₁ : Kernel) (L₀ L₁ : Launch) (c₀ c₁ : Cfg)
    (W₀ W₁ : Tid → Addr → Prop) : Prop :=
  K₀.shared = [] ∧ K₁.shared = [] ∧ Total K₀ L₀ c₀ ∧ Total K₁ L₁ c₁ ∧
  (∀ c d, Reach K₀ L₀ c₀ c → Done K₀ L₀ c →
    Reach K₁ L₁ c₁ d → Done K₁ L₁ d → c.mem = d.mem) ∧
  Frame K₀ L₀ c₀ W₀ ∧ Frame K₁ L₁ c₁ W₁

/-- Source threads may correspond to portions of a wider candidate store.
Solo execution safety, disjoint ownership, equal total write coverage and a
relation between actual final trace bytes suffice for different launch shapes. -/
theorem equivalent_launches_of_traces {K₀ K₁ : Kernel} {L₀ L₁ : Launch}
    {R₀ W₀ R₁ W₁ : Tid → Addr → Prop}
    {r₀ r₁ : Tid → String → Val} {p₀ p₁ : Tid → String → Bool} {m : Mem}
    (h₀ : K₀.shared = []) (h₁ : K₁.shared = [])
    (n₀ n₁ : Tid → Nat)
    (solo₀ : ∀ t ∈ L₀.threads,
      Solo K₀ L₀.alloc (L₀.ctx t) (R₀ t) (W₀ t) (s0 r₀ p₀ m t) m (n₀ t))
    (solo₁ : ∀ t ∈ L₁.threads,
      Solo K₁ L₁.alloc (L₁.ctx t) (R₁ t) (W₁ t) (s0 r₁ p₁ m t) m (n₁ t))
    (disj₀ : ∀ t ∈ L₀.threads, ∀ u ∈ L₀.threads, t ≠ u → ∀ x,
      W₀ t x → ¬ R₀ u x ∧ ¬ W₀ u x)
    (disj₁ : ∀ t ∈ L₁.threads, ∀ u ∈ L₁.threads, t ≠ u → ∀ x,
      W₁ t x → ¬ R₁ u x ∧ ¬ W₁ u x)
    (coverage : ∀ x, (∃ t ∈ L₀.threads, W₀ t x) ↔ ∃ u ∈ L₁.threads, W₁ u x)
    (compare : ∀ t ∈ L₀.threads, ∀ x, W₀ t x → ∃ u ∈ L₁.threads, W₁ u x ∧
      (trace K₀ L₀.alloc (L₀.ctx t) (n₀ t) (s0 r₀ p₀ m t) m).2 x =
      (trace K₁ L₁.alloc (L₁.ctx u) (n₁ u) (s0 r₁ p₁ m u) m).2 x)
    (sh₀ sh₁ : Dim3 → Mem) :
    EquivalentLaunches K₀ K₁ L₀ L₁ (Cfg.init r₀ p₀ m sh₀) (Cfg.init r₁ p₁ m sh₁) W₀ W₁ := by
  let M₀ := fun t => (trace K₀ L₀.alloc (L₀.ctx t) (n₀ t) (s0 r₀ p₀ m t) m).2
  let M₁ := fun t => (trace K₁ L₁.alloc (L₁.ctx t) (n₁ t) (s0 r₁ p₁ m t) m).2
  obtain ⟨b₀,g₀⟩ := grid_sound (P := fun t M => ∀ x, W₀ t x → M x = M₀ t x)
    (fun t ht => ⟨n₀ t,solo₀ t ht,fun _ _ => rfl⟩) disj₀ sh₀
  obtain ⟨b₁,g₁⟩ := grid_sound (P := fun t M => ∀ x, W₁ t x → M x = M₁ t x)
    (fun t ht => ⟨n₁ t,solo₁ t ht,fun _ _ => rfl⟩) disj₁ sh₁
  refine ⟨h₀,h₁,⟨g₀.noFault,g₀.progress,⟨b₀,g₀.bounded⟩,g₀.raceFree,g₀.exists_done⟩,
    ⟨g₁.noFault,g₁.progress,⟨b₁,g₁.bounded⟩,g₁.raceFree,g₁.exists_done⟩,?_,?_,?_⟩
  · intro c d hc hcd hd hdd
    obtain ⟨fc,framec⟩ := g₀.final c hc hcd
    obtain ⟨fd,framed⟩ := g₁.final d hd hdd
    funext x
    by_cases hw : ∃ t ∈ L₀.threads, W₀ t x
    · obtain ⟨t,ht,hx⟩ := hw
      obtain ⟨u,hu,hy,heq⟩ := compare t ht x hx
      obtain ⟨C,hC,hcx⟩ := fc t ht
      obtain ⟨D,hD,hdx⟩ := fd u hu
      exact (hcx x hx).trans ((hC x hx).trans
        (heq.trans ((hD x hy).symm.trans (hdx x hy).symm)))
    · have hx₀ : ∀ t ∈ L₀.threads, ¬ W₀ t x := fun t ht h => hw ⟨t,ht,h⟩
      have hx₁ : ∀ u ∈ L₁.threads, ¬ W₁ u x :=
        fun u hu h => hw ((coverage x).mpr ⟨u,hu,h⟩)
      exact (framec x hx₀).trans (framed x hx₁).symm
  · intro c hc hd
    exact (g₀.final c hc hd).2
  · intro c hc hd
    exact (g₁.final c hc hd).2

#print axioms equivalent_launches_of_traces
end Ptx.Relational
