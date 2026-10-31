/-
  Masked-run summaries as regions of the abstract-interpretation checker's
  hybrid soundness theorem (`E5R.AI.check_sound_hybrid`, support-lean4
  d6ae986). Original e5r code, Apache-2.0.

  A delegated certificate node hands the machine to a region `R`; the
  checker's theorem requires every step from `R` to stay in `R` or reach a
  machine some main-thread certificate node describes (`MainInv`), with
  allowed events, and every enabled interrupt at an `R` machine to come with
  `MainInv`. `regionOf` takes `R` = machines strictly inside a masked run
  that ends in `MainInv`: each step is the run's deterministic step (no
  event, no fault), and no interrupt is enabled, so the interrupt obligation
  is vacuous rather than assumed.
-/
import Theories.Hybrid.Basic
import Theories.AbsintSound

namespace E5R.Hybrid
open E5R E5R.AI

def regionOf (cfg : Config) (cert : Cert) : Region cfg cert where
  R := Inside cfg.board cfg.img (MainInv cert)
  step m h o := by
    obtain ⟨j, m₁, hr, hI⟩ := h
    cases hr with
    | step hm hd hrest =>
      rename_i m₂
      refine ⟨m₂.core, m₂.ram, [], hd o, by simp, ?_⟩
      cases j with
      | zero => cases hrest; exact .inr hI
      | succ j => exact .inl ⟨j, m₁, hrest, hI⟩
  irq m h code hen := by
    obtain ⟨j, m₁, hr, _⟩ := h
    cases hr with
    | step hm _ _ => rw [irqEnabled_masked hm] at hen; cases hen

/-- A masked run from `m` to a machine a main-thread node describes puts `m`
    in the region. -/
theorem regionOf_entry {cfg : Config} {cert : Cert} {n : Nat} {m m' : Machine}
    (hr : MRun cfg.board cfg.img (n+1) m m') (hI : MainInv cert m') : (regionOf cfg cert).R m :=
  ⟨n, m', hr, hI⟩

/-- `MainInv` from a certificate node that covers an abstract state. -/
theorem mainInv_of_cover {cert : Cert} {s : AState} {m : Machine} {n : Node} (hn : n ∈ cert.nodes)
    (hnd : n.s.hnd = false) (hleq : s.leq n.s = true) (hs : StateHolds ρM s m) : MainInv cert m := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hn
  exact ⟨j, n, hj, hnd, leq_state_sound hleq hs⟩

/-! ## Masked runs as checker summaries (support-lean4 34fadf2) -/

/-- A masked run that ends in `Q` is a `SafeTo` run: every machine on it has
    no interrupt enabled, steps under every oracle, emits nothing. -/
theorem safeTo_of_mrun {cfg : Config} {Q : Machine → Prop} :
    ∀ {n m m'}, MRun cfg.board cfg.img n m m' → Q m' → SafeTo cfg Q m
  | _, _, _, .refl _, hq => .done hq
  | _, _, _, .step (m₁ := m₁) hm hd hr, hq =>
    .step (fun code => irqEnabled_masked hm code)
      (fun o => ⟨m₁.core, m₁.ram, [], hd o⟩)
      (fun o c ram evs h ev hev => by
        rw [hd o] at h; simp only [Result.ok.injEq] at h; obtain ⟨-, -, rfl⟩ := h; cases hev)
      (fun o c ram evs h => by
        rw [hd o] at h; simp only [Result.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h
        exact safeTo_of_mrun hr hq)

/-- A masked run of at least one instruction that ends in `Q` is a
    `SafeStep`, the obligation `SumSound` asks of a summary. -/
theorem safeStep_of_mrun {cfg : Config} {Q : Machine → Prop} {n m m'}
    (hr : MRun cfg.board cfg.img (n+1) m m') (hq : Q m') : SafeStep cfg Q m := by
  cases hr with
  | step hm hd hrest =>
    rename_i m₁
    exact ⟨fun code => irqEnabled_masked hm code,
      fun o => ⟨m₁.core, m₁.ram, [], hd o, by simp, safeTo_of_mrun hrest hq⟩⟩

end E5R.Hybrid
