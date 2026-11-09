import Projects.thermostat.EmptyNextTail
import Projects.thermostat.MainNextArrayView
namespace E5R.Thermostat.EmptyNextTailMemory
open E5R E5R.Thermostat

/-- Only the actual minor word and packed padding bytes change. Neither
    parser spans nor the live App/RX/Head/Next array overlaps these writes. -/
theorem region (ram : Word → BitVec 8) (sp len minor p0 p1 p2 p3 p4 p5 p6 : Word) (off size : Nat)
    (bound : off+size≤5232) (minorApart : off+size≤40 ∨ 44≤off) (padApart : off+size≤4896 ∨ 4903≤off) :
    ViewFrame.Region ram (EmptyNextTail.memory ram sp len minor p0 p1 p2 p3 p4 p5 p6) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold EmptyNextTail.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 4902 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases minorApart with a|a <;> rcases padApart with b|b <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 4900 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases minorApart with a|a <;> rcases padApart with b|b <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 4896 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases minorApart with a|a <;> rcases padApart with b|b <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 40 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases minorApart with a|a <;> rcases padApart with b|b <;> omega))]
theorem minor_word (ram : Word → BitVec 8) (sp len minor p0 p1 p2 p3 p4 p5 p6 : Word) :
    ramRead (EmptyNextTail.memory ram sp len minor p0 p1 p2 p3 p4 p5 p6) (sp+40#32) .w=minor := by
  unfold EmptyNextTail.memory
  rw [FrameOffsets.word _ sp _ 40 4902 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 40 4900 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 40 4896 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

end E5R.Thermostat.EmptyNextTailMemory
