import Examples.Refine.Diff.AB
import Examples.Refine.Diff.AC
import Examples.Refine.Diff.AD
import Examples.Refine.Relink
import NoCompiler.Auto
import Examples.Refine.Vacuous

/-
The tree diff (item 5) feeding the automation (NoCompiler/RefineAuto.lean):
examples/refine/diff/build.sh assembles `sum` (A) and two edits (B: the loop's
add commuted; C: `xor t5, t5, t5` inserted in the loop; D: the counter stepped by -2
then +1), and `nocompiler
refine --images …` writes, for each, the certificate (lockstep pairs, jump
pairs for the branches whose offsets moved, one region per changed interval)
and the proofs: `region0_ok` by `nocompiler_region`, `refines` by
`nocompiler_refine` (Examples/Refine/Diff/AB.lean, AC.lean). Nothing in them
is trusted: the kernel checks the certificate and every proof. The generated
`refines` takes A's run (`hA : ARuns …`, decision 2026-11-21 (3); the control
is Examples/Refine/Vacuous.lean), here `sum_a_runs`, from `sum_a`.

Here: the generated theorems at `sum`'s specification; `sum_a`, A meets
`sum`'s specification (by `nocompiler_auto` on A's image); and `sum_b`,
`sum_c`, `sum_d`: B, C and D meet it too (outside A's code region,
`Spec.avoid`), each by `Refines.verified` from `sum_a` and the refinement,
never looking at B's, C's or D's code otherwise.
-/
namespace Examples.Refine.Diff
open NoCompiler

/-- A, the original `sum` (examples/refine/diff), meets `sum`'s specification. -/
theorem sum_a : VerifiedImg ImgA.code ImgA.sum_dom ImgA.sum_entry Examples.Sum.spec := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  nocompiler_auto ImgA.sum_func s he
    loop_inv $l1 (fun u => ∃ m, u.reg 11 = BitVec.ofNat 64 m ∧ 0 < m ∧ m ≤ xs.length ∧
        u.reg 10 = a + BitVec.ofNat 64 (8 * (xs.length - m)) ∧
        u.reg 12 = Examples.Sum.sumW (xs.take (xs.length - m)) ∧ u.mem = s.mem)
      measure (fun u => (u.reg 11).toNat)
  case entry_ret_x20 => exact (Vocab.foldl_of_length_zero _ _ xs (by omega)).symm
  case entry_to_l1 => rfl
  case l1_to_l1 =>
    unfold Examples.Sum.sumW
    rw [Vocab.foldl_take_sub_pred _ _ xs m (by omega) (by omega)]; exact BitVec.add_comm _ _
  case l1_ret_x20 =>
    unfold Examples.Sum.sumW
    rw [Vocab.foldl_eq_last _ _ xs m (by omega) (by omega)]; exact BitVec.add_comm _ _

/-- A runs (decision 2026-11-21 (3)): every refinement of A below carries it. -/
theorem sum_a_runs : ARuns Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry :=
  ARuns.of_verified sum_a

theorem refines_b : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgB.code ImgB.sum_dom ImgB.sum_entry := AB.refines _ sum_a_runs

theorem refines_c : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgC.code ImgC.sum_dom ImgC.sum_entry := AC.refines _ sum_a_runs

/-- C's one region is the 1-against-2 straight-line piece (the jump pairs keep
    the branches out of it). -/
example : AC.cert.regions.length = 1 ∧ AC.region0.domA = [(0x1112c#64, 4)] ∧
    AC.region0.domB = [(0x1112c#64, 8)] := by decide

theorem refines_d : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgD.code ImgD.sum_dom ImgD.sum_entry := AD.refines _ sum_a_runs

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

open Examples.Refine.Relink (spec_pcFree spec_obsInv) in
/-- B (the loop's add commuted) meets `sum`'s specification, through `refines_b`. -/
theorem sum_b : VerifiedImg ImgB.code ImgB.sum_dom ImgB.sum_entry
    (Examples.Sum.spec.avoid ImgA.sum_dom) :=
  refines_b.verified sum_a spec_pcFree spec_obsInv

open Examples.Refine.Relink (spec_pcFree spec_obsInv) in
/-- C (an `xor t5, t5, t5` inserted in the loop) meets it, through `refines_c`. -/
theorem sum_c : VerifiedImg ImgC.code ImgC.sum_dom ImgC.sum_entry
    (Examples.Sum.spec.avoid ImgA.sum_dom) :=
  refines_c.verified sum_a spec_pcFree spec_obsInv

open Examples.Refine.Relink (spec_pcFree spec_obsInv) in
/-- D (the counter stepped by -2 then +1) meets it, through `refines_d`. -/
theorem sum_d : VerifiedImg ImgD.code ImgD.sum_dom ImgD.sum_entry
    (Examples.Sum.spec.avoid ImgA.sum_dom) :=
  refines_d.verified sum_a spec_pcFree spec_obsInv

end Examples.Refine.Diff
