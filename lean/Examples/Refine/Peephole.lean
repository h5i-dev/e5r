import Examples.Refine.Relink
import NoCompiler.RefineAuto

/-
Refinement with a changed instruction (docs/isa/refine.md): B is `sum` with
its `addi a0, a2, 0` (`mv a0, a2`) replaced by `add a0, a2, zero`, in place.
The certificate pairs the eight unchanged instructions in lockstep and makes
the changed one a region, proved by `RRegion.Ok.of_instr` from the
equivalence of the two instructions on agreeing states.
-/
namespace Examples.Refine.Peephole
open NoCompiler NoCompiler.Lockstep
open Examples.Refine.Relink (cA DA eA allRegs spec_pcFree spec_obsInv sum_runs)

/-- `add a0, a2, zero`. -/
def addWord : BitVec 32 := 0x00060533#32

/-- B: A's code with the word at 0x111ac replaced. -/
def cB : Code := ⟨cA.base, cA.words.set! 7 addWord⟩

def at_ (i : Nat) : Word := eA + BitVec.ofNat 64 (4 * i)

def region : RRegion where
  pb := at_ 7
  pa := at_ 7
  pbExit := at_ 8
  paExit := at_ 8
  domB := [(at_ 7, 4)]
  domA := [(at_ 7, 4)]
  liveIn := allRegs
  liveOut := allRegs

def cert : Cert where
  pairs := ([0, 1, 2, 3, 4, 5, 6, 8] : List Nat).map fun i => ⟨at_ i, at_ i, allRegs⟩
  regions := [region]

theorem cert_ok : check cA cB DA DA eA eA cert = true := by decide +kernel

theorem region_ok : region.Ok cA cB := by
  refine RRegion.Ok.of_instr (iA := .iop .addi 10 12 0) (iB := .rop .add 10 12 0) rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (fun _ _ _ _ _ => trivial) ?_
  intro sa sb hx hag sa' h
  simp only [exec, Option.some.injEq] at h; subst h
  have h12 : sa.reg 12 = sb.reg 12 := hag.regs 12 (by decide)
  refine ⟨(sb.setReg 10 (evalR .add (sb.reg 12) (sb.reg 0))).setPc (sb.pc + 4), by simp only [exec],
    by simp [hx], by simp [State.reg_setReg_other _ _ _ _ (by decide : (1 : Reg) ≠ 10)],
    by simp, by simp, ?_⟩
  refine (hag.setReg 10 ?_ (fun r hr _ => hr)).setPc _ _
  simp only [evalI, evalR, h12, State.reg_zero]
  rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]

theorem refines : Refines Examples.Sum.spec cA DA eA cB DA eA :=
  Refines.of_cert sum_runs cert_ok (fun r hr => by simp [cert] at hr; subst hr; exact region_ok)

/-- B meets `sum`'s specification, through refinement. -/
theorem sum_peephole : VerifiedImg cB DA eA (Examples.Sum.spec.avoid DA) :=
  refines.verified Examples.Sum.sum_verified spec_pcFree spec_obsInv

/-! ## Negative controls -/

/-- B with `sub a0, zero, a2` instead (a0 = -a2). The certificate's check passes: it decides
    the unchanged pairs and the region's shape, not the region's contents. What rejects this B
    is the region's equivalence (`region_ok`'s obligation), false at a2 = 1. -/
def subWord : BitVec 32 := 0x40c00533#32

example : check cA ⟨cA.base, cA.words.set! 7 subWord⟩ DA DA eA eA cert = true := by decide +kernel
example : decode subWord = some (.rop .sub 10 0 12) := by decide
example : evalI .addi (1 : Word) (BitVec.signExtend 64 (0 : BitVec 12)) ≠ evalR .sub 0 1 := by decide

-- A change outside the region (the loop's `add` becomes `sub`) is rejected by the check.
example : check cA ⟨cA.base, (cA.words.set! 7 addWord).set! 3 0x40c68633#32⟩ DA DA eA eA cert = false := by
  decide +kernel

end Examples.Refine.Peephole

/-! ## The same, by the automation (NoCompiler/RefineAuto.lean) -/
namespace Examples.Refine.Peephole.Auto
open NoCompiler Examples.Refine.Peephole
open Examples.Refine.Relink (cA DA eA sum_runs)

theorem region_ok' : region.Ok cA cB := by
  nocompiler_region region [.iop .addi 10 12 0] [.rop .add 10 12 0]

theorem refines' : Refines Examples.Sum.spec cA DA eA cB DA eA := by
  have hA := sum_runs
  nocompiler_refine Examples.Refine.Peephole.cert [region_ok']

end Examples.Refine.Peephole.Auto
