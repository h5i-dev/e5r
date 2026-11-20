import Examples.Refine.Diff.AB
import Examples.Refine.Diff.AC
import Examples.Refine.Diff.ImgA
import Examples.Refine.Diff.ImgB
import Examples.Refine.Diff.ImgC
import Examples.Sum

/-
The tree diff (item 5) feeding the straight-line equivalence (item 6):
examples/refine/diff/build.sh assembles `sum` (A) and two edits (B: the loop's
add commuted; C: an extra instruction in the loop), and `nocompiler refine`
writes the lockstep pairs and changed regions (Examples/Refine/Diff/AB.lean,
AC.lean; generated, not trusted).

A against B: one straight-line region, the add. `region0_ok` proves C's
`RRegion.Ok` for it from the generated data and the two images, by
`RRegion.ok_of_seqEquiv` and the kernel tier of `seq_equiv`; with the
generated certificate (`cert_ok`, decided by the kernel) `Refines.of_cert`
gives `refines`: B refines A.

A against C: the extra instruction moves the loop's branch offsets, so the
region is the whole block (structured); proving it is item 4's (region
equivalence), not here. The checks below only pin what the diff found.
-/
namespace Examples.Refine.Diff
open NoCompiler

theorem region0_ok : AB.region0.Ok ImgA.code ImgB.code :=
  RRegion.ok_of_seqEquiv (as := AB.region0_as) (bs := AB.region0_bs)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl rfl (by decide) (by decide)
    (by dsimp only [AB.region0, AB.region0_as, AB.region0_bs]; seq_equiv)

/-- The certificate the diff wrote checks (the 8 pairs, and the region's shape and exit). -/
theorem cert_ok : Lockstep.check ImgA.code ImgB.code ImgA.sum_dom ImgB.sum_dom ImgA.sum_entry ImgB.sum_entry
    AB.cert = true := by decide +kernel

/-- B (the loop's add commuted) refines A: from the diff's certificate and the
    region's proof, nothing written by hand but the call. -/
theorem refines : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgB.code ImgB.sum_dom ImgB.sum_entry :=
  Refines.of_cert cert_ok (fun r hr => by simp [AB.cert] at hr; subst hr; exact region0_ok)

/-- A against C: one region, A's 6 instructions at 0x11124 (the block) against C's 7. -/
example : AC.cert.regions.length = 1 ∧ AC.region0.domA = [(0x11124#64, 24)] ∧ AC.region0.domB = [(0x11124#64, 28)] := by
  decide

end Examples.Refine.Diff
