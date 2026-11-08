import Projects.thermostat.MainRequestBuildCore
import Projects.thermostat.MainRequestTailFrame
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestBuildFrame
open E5R E5R.Thermostat

theorem contract (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te minor : Word)
    (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3312 ∨ 3685≤off) :
    ViewFrame.Region ram (MainRequestBuildCore.memory ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te minor) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRequestPrefixFrame.contract ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te off size bound apart)
  exact MainRequestTailFrame.contract _ sp minor rx (BitVec.ofNat 32 used) off size bound
    (by rcases apart with h|h <;>omega) (by rcases apart with h|h <;>omega) (by rcases apart with h|h <;>omega)
end E5R.Thermostat.MainRequestBuildFrame
