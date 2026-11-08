import Projects.thermostat.MainRequestMemory
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestMemoryFrames
open E5R E5R.Thermostat HttpRequestSpec

theorem low (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :
    ViewFrame.Region (MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen)
      (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+3312#32) 32 := by
  apply HeadRegionFrame.trans (MainRamCopy264.frame (MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen) sp 1062 836 3312 32 (by decide) (by decide) (Or.inl (by decide)))
  exact MainRequestTailFrame.contract (MainRequestMemory.copied ram sp rx head amount method path pathLen query queryLen) sp
    (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount)) 3312 32 (by decide) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))

theorem arraySource (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :
    ViewFrame.Region ram (MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen) (sp+4248#32) 264 := by
  apply HeadRegionFrame.trans (MainRequestStoreFrames.body ram sp (BitVec.ofNat 32 head.len+rx)
    (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method 4248 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide)))
  exact MainRequestStoreFrames.metadata (MainRequestMemory.body ram sp rx head amount method) sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount)
    (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2)
    4248 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide))

theorem arrayTail (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :
    ViewFrame.Region (MainRequestMemory.copied ram sp rx head amount method path pathLen query queryLen)
      (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+3344#32) 264 :=
  MainRequestTailFrame.contract _ sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount)) 3344 264 (by decide)
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
end E5R.Thermostat.MainRequestMemoryFrames
