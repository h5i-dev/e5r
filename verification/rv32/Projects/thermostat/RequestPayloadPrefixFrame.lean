import Projects.thermostat.RequestPayloadPrefix
set_option autoImplicit false
namespace E5R.Thermostat.RequestPayloadPrefixFrame
open E5R E5R.Thermostat

theorem contract (ram : Word → BitVec 8) (sp rx : Word) (start finish : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te : Word)
    (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3312 ∨ 3685≤off) :
    ViewFrame.Region ram (RequestPayloadPrefix.memory ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRequestStoreFrames.body ram sp (BitVec.ofNat 32 start+rx) (BitVec.ofNat 32 finish-BitVec.ofNat 32 start) method off size bound
    (by rcases apart with h|h <;>omega) (by rcases apart with h|h <;>omega))
  apply HeadRegionFrame.trans (RequestPayloadMetadataFrame.metadata (RequestPayloadPrefix.body ram sp rx start finish method) sp path pathLen query queryLen tag pad low
    (extend .h true (ramRead ram (sp+4512#32) .h)) (extend .h true (ramRead ram (sp+4514#32) .h))
    (extend .h true (ramRead ram (sp+4516#32) .h)) ms me ts te off size bound
    (by rcases apart with h|h <;>omega) (by rcases apart with h|h <;>omega))
  exact MainRamCopy264.frame (RequestPayloadPrefix.metadata ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te) sp 1062 836 off size bound (by decide)
    (by rcases apart with h|h <;>omega)
end E5R.Thermostat.RequestPayloadPrefixFrame
