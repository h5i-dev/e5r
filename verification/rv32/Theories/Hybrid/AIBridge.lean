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

end E5R.Hybrid
