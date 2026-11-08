import Projects.thermostat.MainCloseCommit
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseCommitFrame
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (sp close : Word) (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3304 ∨ 3305≤off) :
    ViewFrame.Region ram (MainCloseCommit.memory ram sp close) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainCloseCommit.memory
  apply StoreBytes.frame
  intro j
  have zero : j.val=0 := by have hj : j.val<1 := j.isLt;omega
  simpa only [zero,BitVec.add_zero] using FrameOffsets.ne sp off 3304 i.val 0
    (by have := i.isLt;omega) (by decide) (by have := i.isLt;rcases apart with h|h <;>omega)

theorem byte (ram : Word → BitVec 8) (sp close : Word) : MainCloseCommit.memory ram sp close (sp+3304#32)=byteOf close 0 := by
  change ramPut ram (sp+3304#32) (byteOf close 0) (sp+3304#32)=byteOf close 0
  exact ramPut_eq ram (sp+3304#32) (byteOf close 0)
end E5R.Thermostat.MainCloseCommitFrame
