/- Warp model regressions. Concrete schedules use every one of 64 actual
threads. These are not the FP4 entry and do not claim FP4 acceptance. -/
import Ptx.Logic.WarpSchedule

namespace Ptx.Examples.Warp
open Ptx.Warp

private def one : Dim3 := ⟨1, 1, 1⟩
private def zero : Dim3 := ⟨0, 0, 0⟩
private def L : Launch := { grid := one, block := ⟨64,1,1⟩, params := fun _ => 0, alloc := [] }
private def K : Kernel where
  name := "warp_then_cta"
  params := []
  regs := []
  body := [⟨none, .warpBar⟩, ⟨none, .bar⟩, ⟨none, .ret⟩]
  labels := []
private def initial : State := State.init (fun _ _ => 0) (fun _ _ => false) (fun _ => 0) (fun _ _ => 0)
private def w₀ : Id := ⟨zero, 0⟩
private def w₁ : Id := ⟨zero, 1⟩
private def mixed : State := releaseWarp L initial w₀

theorem first_warp_ready : warpReadyB K L initial w₀ = true := by decide +kernel
theorem second_warp_ready : warpReadyB K L initial w₁ = true := by decide +kernel

theorem mixed_cta_not_ready : ctaReadyB K L mixed zero = false := by decide +kernel
theorem mixed_second_warp_ready : warpReadyB K L mixed w₁ = true := by decide +kernel

theorem legal_mixed_waits_do_not_diverge : ¬ Ptx.Warp.Diverged K L mixed := by
  rintro ⟨t, ht, u, hu, hcta, hw, hbad⟩
  by_cases hti : id L t = w₀ <;> by_cases hui : id L u = w₀ <;>
    simp_all [mixed, releaseWarp, initial, State.init, Cfg.init, Ptx.Warp.res, Ptx.Warp.action, Ptx.action, exec, K, atWarp,
      guardHolds, TState.skip]

theorem partial_fullmask_not_ready :
    warpReadyB K { L with block := ⟨16,1,1⟩ } initial w₀ = false := by decide +kernel

/-- A successful full-mask/CTA schedule gives an actual completed grid run. -/
theorem sixty_four_thread_execution : ∃ c, Ptx.Warp.Reach K L initial c ∧ Ptx.Warp.Done K L c := by
  have h : (execute K L initial [.warp w₀, .warp w₁, .cta zero]).any (doneB K L) = true := by
    decide +kernel
  cases he : execute K L initial [.warp w₀, .warp w₁, .cta zero] with
  | none => simp [he] at h
  | some c =>
    refine ⟨c, execute_reach _ he, doneB_spec ?_⟩
    simpa only [he, Option.any_some] using h

#print axioms legal_mixed_waits_do_not_diverge
#print axioms sixty_four_thread_execution
end Ptx.Examples.Warp
