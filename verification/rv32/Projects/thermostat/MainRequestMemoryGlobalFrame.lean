import Projects.thermostat.MainRequestMemory
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestMemoryGlobalFrame
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3312 ∨ 3685≤off) :
    ViewFrame.Region ram (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+BitVec.ofNat 32 off) size := by
  exact MainRequestBuildFrame.contract ram sp rx head.len (head.len+amount) (head.len+amount) method path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount)
    (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.minor) off size bound apart
end E5R.Thermostat.MainRequestMemoryGlobalFrame
