import Projects.thermostat.MainLengthStart
import Projects.thermostat.MainCopyView
import Projects.thermostat.MainHeaderLayout
namespace E5R.Thermostat.MainLengthStartMemory
open E5R E5R.Thermostat

theorem region (ram : Word → BitVec 8) (fp body len filled : Word) (off size : Nat)
    (bound : off+size≤452 ∨ 456≤off) (small : off+size≤65536) :
    ViewFrame.Region ram (MainLengthStart.memory ram fp body len filled) (fp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainLengthStart.memory
  apply StoreBytes.frame
  intro j
  exact FrameOffsets.ne fp off 452 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have := j.isLt;change j.val<4 at this;rcases bound with h|h <;> omega)

theorem frame (ram : Word → BitVec 8) (fp body len filled x : Word)
    (apart : ∀ i : Fin 4, x≠(fp+452#32)+BitVec.ofNat 32 i.val) :
    MainLengthStart.memory ram fp body len filled x=ram x := StoreBytes.frame _ _ _ _ .w apart

theorem total (ram : Word → BitVec 8) (fp body len filled : Word) :
    ramRead (MainLengthStart.memory ram fp body len filled) (fp+452#32) .w=body+len := ramRead_ramWrite_w _ _ _
end E5R.Thermostat.MainLengthStartMemory
