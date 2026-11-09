import Projects.thermostat.RequestPayloadCore
set_option autoImplicit false
namespace E5R.Thermostat.RequestPayloadMemory
open E5R E5R.Thermostat

/-- Exact instruction-derived body, metadata, copied-array and tail RAM. -/
abbrev body := RequestPayloadPrefix.body
abbrev metadata := RequestPayloadPrefix.metadata
abbrev copied := RequestPayloadPrefix.memory
abbrev memory := RequestPayloadCore.memory

theorem tail_frame (ram : Word → BitVec 8) (sp minor rx used : Word) (off size : Nat)
    (bound : off+size≤5232) (padding : off+size≤3609 ∨ 3616≤off)
    (minorByte : off+size≤3608 ∨ 3609≤off) (raw : off+size≤3640 ∨ 3648≤off)
    (params : off+size≤3648 ∨ 3684≤off) :
    ViewFrame.Region ram (MainRequestTailCore.memory ram sp minor rx used) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainRequestStoreFrames.padding ram sp _ _ _ _ _ _ _ off size bound padding)
  apply HeadRegionFrame.trans (MainRequestStoreFrames.minor (MainRequestTailCore.padding ram sp) sp minor rx used off size bound minorByte raw)
  exact MainRequestZero.frame (MainRequestTailCore.minorRaw ram sp minor rx used) sp off size bound params

/-- All construction stores/copies are confined to the actual Request slot. -/
theorem frame (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te minor : Word)
    (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3312 ∨ 3685≤off) :
    ViewFrame.Region ram (memory ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te minor)
      (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (RequestPayloadPrefixFrame.contract ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te off size bound apart)
  apply tail_frame _ sp minor rx (BitVec.ofNat 32 used) off size bound
  all_goals rcases apart with h|h <;> omega

/-- Relocated array bytes survive the tail's padding/minor/raw/params stores. -/
theorem array_frame (ram : Word → BitVec 8) (sp minor rx used : Word) :
    ViewFrame.Region ram (MainRequestTailCore.memory ram sp minor rx used) (sp+3344#32) 264 :=
  tail_frame ram sp minor rx used 3344 264 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide))
end E5R.Thermostat.RequestPayloadMemory
