import Examples.Refine.Diff.AB
import Examples.Refine.Diff.AC
import Examples.Refine.Diff.AD
import Examples.Sum

/-
The tree diff (item 5) feeding the automation (NoCompiler/RefineAuto.lean):
examples/refine/diff/build.sh assembles `sum` (A) and two edits (B: the loop's
add commuted; C: `xor t5, t5, t5` inserted in the loop; D: the counter stepped by -2
then +1), and `nocompiler
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

theorem refines_d : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgD.code ImgD.sum_dom ImgD.sum_entry := AD.refines _

/-- D's region is grown past the changed instruction: A's `addi a1,a1,-1; addi
    a0,a0,8` against D's `addi a1,a1,-2; addi a0,a0,8; addi a1,a1,1`. -/
example : AD.cert.regions.length = 1 ∧ AD.region0.domA = [(0x11130#64, 8)] ∧
    AD.region0.domB = [(0x11130#64, 12)] := by decide

/-- Control: the changed instruction alone (`addi a1,a1,-1` against `-2`, a1
    live) is not an equivalence; the diff found that and took in more. -/
example : ¬ SeqEquiv [11] [11] [.iop .addi 11 11 0xfff#12] [.iop .addi 11 11 0xffe#12] := by
  intro h
  have := h (fun _ => 5) (fun _ => 5) (fun _ _ => rfl) 11 (by simp)
  revert this; decide

end Examples.Refine.Diff
