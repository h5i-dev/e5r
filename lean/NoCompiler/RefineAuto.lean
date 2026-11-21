import NoCompiler.RefineLockstep
import NoCompiler.RefineStraightRegion

/-
Automation for refinement proofs (docs/isa/refine.md, "Automation").

A refinement task's proof is generated, not written: `nocompiler refine A.elf
B.elf FUNC` (the tree diff) writes a certificate (lockstep pairs for the
unchanged instructions, one `RRegion` per changed interval, live sets) and,
per region, the two instruction sequences. Then

    theorem region_0_ok : region_0.Ok cA cB := by nocompiler_region region_0 [as…] [bs…]
    theorem refines (hA : ARuns spec cA DA eA) : Refines spec cA DA eA cB DB eB := by
      nocompiler_refine cert [region_0_ok, …]

* `nocompiler_region r as bs`: the straight-line region `r` (register
  instructions only), by `RRegion.ok_of_seqEquiv` and `seq_equiv` (kernel
  tier). The side conditions (the code holds the sequences, the region's
  intervals and exits are the sequences') are decided. The region's live
  sets must be literal lists of registers.
* `nocompiler_region_bv r as bs`: the same with `seq_equiv_bv`: the theorem is
  in the bv_decide tier (docs/isa/trust.md), and the audit says so.
* `nocompiler_refine cert [h, …]`: `Refines.of_cert`, the certificate check by
  kernel evaluation, and the regions' proofs, in the certificate's order.

What none of these can do is left as a goal: a region that is not a
straight-line equivalence (a loop whose relational invariant is not "the live
registers are equal") needs its own proof (`RRegion.Ok.of_bigSim`).
-/
namespace NoCompiler

/-- A straight-line region from its two instruction sequences (kernel tier). -/
macro "nocompiler_region" r:ident as:term:max bs:term:max : tactic => `(tactic| (
  unfold $r:ident
  refine RRegion.ok_of_seqEquiv (as := $as) (bs := $bs) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_
  seq_equiv))

/-- The same, with `bv_decide` where the kernel tier fails (bv_decide tier). -/
macro "nocompiler_region_bv" r:ident as:term:max bs:term:max : tactic => `(tactic| (
  unfold $r:ident
  refine RRegion.ok_of_seqEquiv (as := $as) (bs := $bs) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_
  seq_equiv_bv))

/-- `Refines` from a certificate and its regions' proofs. A's run (`ARuns`,
    decision 2026-11-21 (3)) is taken from a hypothesis in the context. -/
macro "nocompiler_refine" k:ident " [" hs:term,* "]" : tactic => `(tactic| (
  refine Refines.of_cert (k := $k) (by assumption) (by decide +kernel) ?_
  unfold $k:ident
  dsimp only
  simp only [List.forall_mem_cons]
  exact ⟨$hs,*, fun _ h => nomatch h⟩))

end NoCompiler
