/-
Negative controls: each deliberate bug in benchmarks/buggy is refuted by a
kernel-checked counterexample in the same grid semantics the proofs use, on
a small launch that satisfies every hypothesis of `vadd_correct`. So the
statement of `vadd_correct` is false for each of these kernels; the proof
does not go through because the property does not hold, not because the
proof script is brittle.

* `vadd_nobound` (no `i < n` check): thread 1 of a 2-thread launch with
  `n = 1` faults loading `b[1]`, outside the allocation.
* `vadd_tid` (index from `%tid.x` only): with two CTAs of one thread, both
  threads reach a store to `c[0]` in the same configuration: a data race.
* `vadd_sub` (`b[i] - a[i]`): the only execution of a one-thread launch with
  `a[0] = 1`, `b[0] = 2` finishes with `c[0] = 1`, not `3`.
-/
import Ptx.Logic.Refute
import Ptx.Logic.Launch1D
import Ptx.Tactics.Eval
import Ptx.Kernels.VAddNoBound
import Ptx.Kernels.VAddTid
import Ptx.Kernels.VAddSub

-- The evaluation simp sets are shared across goals; not every lemma fires in each.
set_option linter.unusedSimpArgs false

namespace Ptx.Examples.Buggy
open Ptx

/-- Parameters `a = 0x1000`, `b = 0x2000`, `c = 0x3000`, `n = 1`. -/
def prm : String → Val := fun x =>
  if x = "vadd_param_0" then 0x1000 else if x = "vadd_param_1" then 0x2000
  else if x = "vadd_param_2" then 0x3000 else if x = "vadd_param_3" then 1 else 0

def launch (G B : BitVec 32) : Launch where
  grid := ⟨G, 1, 1⟩
  block := ⟨B, 1, 1⟩
  params := prm
  alloc := [⟨0x1000, 4⟩, ⟨0x2000, 4⟩, ⟨0x3000, 4⟩]

def tid (c t : BitVec 32) : Tid := ⟨⟨c, 0, 0⟩, ⟨t, 0, 0⟩⟩

/-- `a[0] = 1`, `b[0] = 2`, everything else 0. -/
def mem₀ : Mem := fun x => if x = 0x1000 then 1 else if x = 0x2000 then 2 else 0

def cfg₀ : Cfg := Cfg.init (fun _ _ => 0) (fun _ _ => false) mem₀ (fun _ _ => 0)

/-! ### No bounds check: an out-of-bounds load -/

theorem nobound_faults :
    ∃ c, Reach Ptx.Kernels.VAddNoBound.vadd (launch 1 2) cfg₀ c ∧
      Faults Ptx.Kernels.VAddNoBound.vadd (launch 1 2) c := by
  have ht : tid 0 1 ∈ (launch 1 2).threads := by rw [mem_threads]; simp only [Launch.Thread, launch, tid]; decide
  refine ⟨cfg₀.advance _ _ (tid 0 1) 13, reach_thread' ht ?_, .inl ⟨tid 0 1, ht, ?_⟩⟩
  · simp [okSteps, stepMem, ptx_eval, Ptx.Kernels.VAddNoBound.vadd, launch, prm, cfg₀, Cfg.init,
      tid, accessOk, Region.holds, lo32, ext32]
  · simp [Cfg.advance, Cfg.res, Cfg.heap, tstep, trace, stepMem, ptx_eval, Ptx.Kernels.VAddNoBound.vadd, launch, prm,
      cfg₀, Cfg.init, tid, updT, accessOk, Region.holds, lo32, ext32]

/-! ### Index from `%tid.x` only: a write-write race -/

theorem tid_races : ¬ RaceFree Ptx.Kernels.VAddTid.vadd (launch 2 1) cfg₀ := by
  intro hrf
  let K := Ptx.Kernels.VAddTid.vadd
  have h0 : tid 0 0 ∈ (launch 2 1).threads := by rw [mem_threads]; simp only [Launch.Thread, launch, tid]; decide
  have h1 : tid 1 0 ∈ (launch 2 1).threads := by rw [mem_threads]; simp only [Launch.Thread, launch, tid]; decide
  let c₁ := cfg₀.advance K (launch 2 1) (tid 0 0) 20
  let c₂ := c₁.advance K (launch 2 1) (tid 1 0) 20
  have r₁ : Reach K (launch 2 1) cfg₀ c₁ := reach_thread' h0 (by
    simp [K, okSteps, stepMem, ptx_eval, Ptx.Kernels.VAddTid.vadd, launch, prm, cfg₀, Cfg.init,
      tid, accessOk, Region.holds, lo32, ext32])
  have r₂ : Reach K (launch 2 1) c₁ c₂ := reach_thread' h1 (by
    simp [K, c₁, Cfg.advance, trace, okSteps, stepMem, ptx_eval, Ptx.Kernels.VAddTid.vadd, launch,
      prm, cfg₀, Cfg.init, tid, updT, accessOk, Region.holds, lo32, ext32])
  have p₀ : c₂.pending K (launch 2 1) (tid 0 0) = some ⟨.global, 0x3000, .b4, .write⟩ := by
    simp [K, c₁, c₂, Cfg.pending, Cfg.advance, trace, stepMem, ptx_eval, Ptx.Kernels.VAddTid.vadd,
      launch, prm, cfg₀, Cfg.init, tid, updT, accessOk, Region.holds, lo32, ext32, Action.acc]
  have p₁ : c₂.pending K (launch 2 1) (tid 1 0) = some ⟨.global, 0x3000, .b4, .write⟩ := by
    simp [K, c₁, c₂, Cfg.pending, Cfg.advance, trace, stepMem, ptx_eval, Ptx.Kernels.VAddTid.vadd,
      launch, prm, cfg₀, Cfg.init, tid, updT, accessOk, Region.holds, lo32, ext32, Action.acc]
  have hr := Reach.trans r₁ r₂
  have := hrf c₂ c₂ hr hr _ h0 _ h1 (by decide) _ _ p₀ p₁
    ⟨rfl, nofun, .inl nofun, 0x3000, by decide, by decide⟩
  rcases this with ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · simp [tid] at h

/-! ### `sub` for `add`: a wrong result -/

theorem sub_wrong :
    ∃ c, Reach Ptx.Kernels.VAddSub.vadd (launch 1 1) cfg₀ c ∧
      Done Ptx.Kernels.VAddSub.vadd (launch 1 1) c ∧
      rd32 c.mem 0x3000 ≠ rd32 mem₀ 0x1000 + rd32 mem₀ 0x2000 := by
  let K := Ptx.Kernels.VAddSub.vadd
  have h0 : tid 0 0 ∈ (launch 1 1).threads := by rw [mem_threads]; simp only [Launch.Thread, launch, tid]; decide
  have only : ∀ t ∈ (launch 1 1).threads, t = tid 0 0 := by
    intro t ht
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := (show (launch 1 1).OneD 1 1 from ⟨rfl, rfl⟩).thread ht
    have : t.ctaid.x = 0 := BitVec.eq_of_toNat_eq (by simp at a1 ⊢; omega)
    have : t.tid.x = 0 := BitVec.eq_of_toNat_eq (by simp at a2 ⊢; omega)
    rcases t with ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩
    simp_all [tid]
  let c := cfg₀.advance K (launch 1 1) (tid 0 0) 21
  refine ⟨c, reach_thread' h0 ?_, fun t ht => ?_, ?_⟩
  · simp [K, okSteps, stepMem, ptx_eval, Ptx.Kernels.VAddSub.vadd, launch, prm, cfg₀, Cfg.init,
      tid, accessOk, Region.holds, lo32, ext32]
  · rw [only t ht]
    simp [K, c, Cfg.res, Cfg.heap, tstep, Cfg.advance, trace, stepMem, ptx_eval, Ptx.Kernels.VAddSub.vadd, launch,
      prm, cfg₀, Cfg.init, tid, updT, accessOk, Region.holds, lo32, ext32]
  · simp [K, c, Cfg.advance, trace, stepMem, ptx_eval, Ptx.Kernels.VAddSub.vadd, launch, prm, cfg₀,
      Cfg.init, tid, updT, accessOk, Region.holds, lo32, ext32, rd, rd32, wr, mem₀]

end Ptx.Examples.Buggy
