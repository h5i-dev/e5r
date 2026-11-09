import Projects.thermostat.RequestPayloadMemory
set_option autoImplicit false
namespace E5R.Thermostat.RequestPayloadAfter
open E5R E5R.Thermostat

theorem metadata (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te minor : Word)
    (off size : Nat) (bound : off+size≤5232)
    (copy : off+size≤3344 ∨ 3608≤off) (padding : off+size≤3608 ∨ 3616≤off)
    (raw : off+size≤3640 ∨ 3648≤off) (params : off+size≤3648 ∨ 3684≤off) :
    ViewFrame.Region (RequestPayloadPrefix.metadata ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te)
      (RequestPayloadCore.memory ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te minor)
      (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRamCopy264.frame (RequestPayloadPrefix.metadata ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te) sp 1062 836 off size bound (by decide) copy)
  exact RequestPayloadMemory.tail_frame _ sp minor rx (BitVec.ofNat 32 used) off size bound (by omega) (by omega) raw params

theorem body (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te minor : Word)
    (off size : Nat) (bound : off+size≤5232)
    (headFields : off+size≤3312 ∨ 3344≤off) (uri : off+size≤3616 ∨ 3632≤off)
    (copy : off+size≤3344 ∨ 3608≤off) (padding : off+size≤3608 ∨ 3616≤off)
    (raw : off+size≤3640 ∨ 3648≤off) (params : off+size≤3648 ∨ 3684≤off) :
    ViewFrame.Region (RequestPayloadPrefix.body ram sp rx start finish method)
      (RequestPayloadCore.memory ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te minor)
      (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (RequestPayloadMetadataFrame.metadata _ sp path pathLen query queryLen tag pad low
    (extend .h true (ramRead ram (sp+4512#32) .h)) (extend .h true (ramRead ram (sp+4514#32) .h))
    (extend .h true (ramRead ram (sp+4516#32) .h)) ms me ts te off size bound headFields uri)
  exact metadata ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te minor off size bound copy padding raw params
end E5R.Thermostat.RequestPayloadAfter
