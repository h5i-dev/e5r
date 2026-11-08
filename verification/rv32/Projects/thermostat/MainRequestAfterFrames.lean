import Projects.thermostat.MainRequestMemory
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestAfterFrames
open E5R E5R.Thermostat HttpRequestSpec

theorem metadata (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (off size : Nat) (bound : off+size≤5232)
    (copy : off+size≤3344 ∨ 3608≤off) (padding : off+size≤3608 ∨ 3616≤off)
    (raw : off+size≤3640 ∨ 3648≤off) (params : off+size≤3648 ∨ 3684≤off) :
    ViewFrame.Region (MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen)
      (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRamCopy264.frame (MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen) sp 1062 836 off size bound (by decide) copy)
  exact MainRequestTailFrame.contract (MainRequestMemory.copied ram sp rx head amount method path pathLen query queryLen) sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount)) off size bound padding raw params

theorem body (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (off size : Nat) (bound : off+size≤5232)
    (headFields : off+size≤3312 ∨ 3344≤off) (uri : off+size≤3616 ∨ 3632≤off)
    (copy : off+size≤3344 ∨ 3608≤off) (padding : off+size≤3608 ∨ 3616≤off)
    (raw : off+size≤3640 ∨ 3648≤off) (params : off+size≤3648 ∨ 3684≤off) :
    ViewFrame.Region (MainRequestMemory.body ram sp rx head amount method)
      (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRequestStoreFrames.metadata (MainRequestMemory.body ram sp rx head amount method) sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount)
    (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) off size bound headFields uri)
  exact metadata ram sp rx head amount method path pathLen query queryLen off size bound copy padding raw params
end E5R.Thermostat.MainRequestAfterFrames
