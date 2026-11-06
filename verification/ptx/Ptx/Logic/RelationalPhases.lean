/- Direct observable execution equivalence for kernels with shared memory.
This composes actual phased executions using the existing phase_sound theorem;
no mathematical decoder specification is introduced. Warp synchronization still
requires its own faithful model and cannot be discharged by this CTA theorem. -/
import Ptx.Logic.PhaseSound
import Ptx.Logic.Relational

namespace Ptx.Relational

/-- Same total-correctness and observable-memory requirements as Equivalent,
without its empty-shared fragment restriction. It is a new contract; the
existing checker statement and its restrictions remain unchanged. -/
def SharedEquivalent (K₀ K₁ : Kernel) (L : Launch) (c₀ : Cfg)
    (W₀ W₁ : Tid → Addr → Prop) : Prop :=
  Total K₀ L c₀ ∧ Total K₁ L c₀ ∧
  (∀ c d, Reach K₀ L c₀ c → Done K₀ L c →
    Reach K₁ L c₀ d → Done K₁ L d → c.mem = d.mem) ∧
  Frame K₀ L c₀ W₀ ∧ Frame K₁ L c₀ W₁

/-- The union of one thread's global writes in its real phases. -/
def phaseWrites (S : Phased) (t : Tid) (a : Addr) : Prop :=
  ∃ k < S.P t.ctaid, (S.F t k).w (.global, a)

theorem total_of_phased {K L S c₀ m} (result : Phased.Result K L S c₀ m) :
    Total K L c₀ := by
  exact ⟨result.noFault, result.progress, result.bounded, result.raceFree,
    Phased.exists_done_of result.progress result.bounded⟩

theorem frame_of_phased {K L S c₀ m} (result : Phased.Result K L S c₀ m)
    (initial : c₀.mem = m) (noCells : ∀ a, ¬ S.Cell a) :
    Frame K L c₀ (phaseWrites S) := by
  intro c hc hd a outside
  rw [initial]
  apply (result.final c hc hd).2.1 a
  · intro t ht k hk hw
    exact outside t ht ⟨k,hk,hw⟩
  · intro b hb
    exact False.elim (noCells b hb)

/-- Both sides' per-thread phase derivations prove their actual final views.
The comparison relates those views directly, allowing different registers,
phase counts, trace lengths and shared-memory scratch contents. -/
theorem shared_equivalent_of_phases {K₀ K₁ L S₀ S₁ r p m sh}
    (ok₀ : Phased.Ok K₀ L S₀ r p m sh) (ok₁ : Phased.Ok K₁ L S₁ r p m sh)
    (noCells₀ : ∀ a, ¬ S₀.Cell a) (noCells₁ : ∀ a, ¬ S₁.Cell a)
    (coverage : ∀ a, (∃ t ∈ L.threads, phaseWrites S₀ t a) ↔
      ∃ t ∈ L.threads, phaseWrites S₁ t a)
    (compare : ∀ t ∈ L.threads, ∀ a, phaseWrites S₀ t a →
      ∃ u ∈ L.threads, phaseWrites S₁ u a ∧
      (S₀.M t.ctaid (S₀.P t.ctaid)).g a = (S₁.M u.ctaid (S₁.P u.ctaid)).g a) :
    SharedEquivalent K₀ K₁ L (Cfg.init r p m sh) (phaseWrites S₀) (phaseWrites S₁) := by
  have result₀ := Phased.phase_sound ok₀
  have result₁ := Phased.phase_sound ok₁
  have frame₀ := frame_of_phased result₀ rfl noCells₀
  have frame₁ := frame_of_phased result₁ rfl noCells₁
  refine ⟨total_of_phased result₀, total_of_phased result₁, ?_, frame₀, frame₁⟩
  intro c d hc hcd hd hdd
  funext a
  by_cases written : ∃ t ∈ L.threads, phaseWrites S₀ t a
  · obtain ⟨t,ht,hw⟩ := written
    obtain ⟨u,hu,hw',heq⟩ := compare t ht a hw
    obtain ⟨k,hk,hwrite⟩ := hw
    obtain ⟨j,hj,hwrite'⟩ := hw'
    exact ((result₀.final c hc hcd).1 t ht k hk a hwrite).trans
      (heq.trans ((result₁.final d hd hdd).1 u hu j hj a hwrite').symm)
  · have outside₀ : ∀ t ∈ L.threads, ¬ phaseWrites S₀ t a :=
      fun t ht hw => written ⟨t,ht,hw⟩
    have outside₁ : ∀ t ∈ L.threads, ¬ phaseWrites S₁ t a :=
      fun t ht hw => written ((coverage a).mpr ⟨t,ht,hw⟩)
    exact (frame₀ c hc hcd a outside₀).trans (frame₁ d hd hdd a outside₁).symm

#print axioms shared_equivalent_of_phases
end Ptx.Relational
