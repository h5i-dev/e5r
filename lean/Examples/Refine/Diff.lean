import Examples.Refine.Diff.AB
import Examples.Refine.Diff.AC
import Examples.Sum

/-
The tree diff (item 5) feeding the automation (NoCompiler/RefineAuto.lean):
examples/refine/diff/build.sh assembles `sum` (A) and two edits (B: the loop's
add commuted; C: `xor t5, t5, t5` inserted in the loop), and `nocompiler
refine --images …` writes, for each, the certificate (lockstep pairs, jump
pairs for the branches whose offsets moved, one region per changed interval)
and the proofs: `region0_ok` by `nocompiler_region`, `refines` by
`nocompiler_refine` (Examples/Refine/Diff/AB.lean, AC.lean). Nothing in them
is trusted: the kernel checks the certificate and every proof.

Here: the generated theorems at `sum`'s specification, and `sum`'s
correctness carried to B and C.
-/
namespace Examples.Refine.Diff
open NoCompiler

theorem refines_b : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgB.code ImgB.sum_dom ImgB.sum_entry := AB.refines _

theorem refines_c : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgC.code ImgC.sum_dom ImgC.sum_entry := AC.refines _

/-- C's one region is the 1-against-2 straight-line piece (the jump pairs keep
    the branches out of it). -/
example : AC.cert.regions.length = 1 ∧ AC.region0.domA = [(0x1112c#64, 4)] ∧
    AC.region0.domB = [(0x1112c#64, 8)] := by decide

end Examples.Refine.Diff
