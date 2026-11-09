import Projects.thermostat.RejectNextFront
import Projects.thermostat.RejectNextZeroStage
import Projects.thermostat.MainServeNextStoreFrames
namespace E5R.Thermostat.RejectNextFrames
open E5R E5R.Thermostat
theorem front (ram : Word → BitVec 8) (sp word half : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤3652 ∨ 3653≤off)
    (apart1 : off+size≤4232 ∨ 4238≤off)
    : ViewFrame.Region ram (RejectNextFront.memory ram sp word half) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold RejectNextFront.memory
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 4236 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 4232 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    have hj : j.val<1 := j.isLt
    exact FrameOffsets.ne sp off 3652 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> rcases apart1 with a1|a1 <;> omega))]

theorem zeroStage (ram : Word → BitVec 8) (sp word half : Word) (off size : Nat) (bound : off+size≤5232)
    (apart0 : off+size≤4512 ∨ 4518≤off)
    : ViewFrame.Region ram (RejectNextZeroStage.memory ram sp word half) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold RejectNextZeroStage.memory
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 4516 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 4512 i.val j.val (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;rcases apart0 with a0|a0 <;> omega))]

end E5R.Thermostat.RejectNextFrames
