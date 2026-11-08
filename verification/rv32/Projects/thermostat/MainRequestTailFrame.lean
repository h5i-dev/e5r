import Projects.thermostat.MainRequestTailCore
import Projects.thermostat.HeadRegionFrame
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestTailFrame
open E5R E5R.Thermostat

theorem contract (ram : Word → BitVec 8) (sp minor rx used : Word) (off size : Nat) (bound : off+size≤5232)
    (padding : off+size≤3608 ∨ 3616≤off) (raw : off+size≤3640 ∨ 3648≤off) (params : off+size≤3648 ∨ 3684≤off) :
    ViewFrame.Region ram (MainRequestTailCore.memory ram sp minor rx used) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRequestStoreFrames.padding ram sp
    (extend .b false (ramRead ram (sp+4240#32) .b)) (extend .b false (ramRead ram (sp+4241#32) .b))
    (extend .b false (ramRead ram (sp+4242#32) .b)) (extend .b false (ramRead ram (sp+4243#32) .b))
    (extend .b false (ramRead ram (sp+4244#32) .b)) (extend .b false (ramRead ram (sp+4245#32) .b))
    (extend .b false (ramRead ram (sp+4246#32) .b)) off size bound (by rcases padding with h|h <;>omega))
  apply HeadRegionFrame.trans (MainRequestStoreFrames.minor (MainRequestTailCore.padding ram sp) sp minor rx used off size bound (by rcases padding with h|h <;>omega) raw)
  exact MainRequestZero.frame (MainRequestTailCore.minorRaw ram sp minor rx used) sp off size bound params
end E5R.Thermostat.MainRequestTailFrame
