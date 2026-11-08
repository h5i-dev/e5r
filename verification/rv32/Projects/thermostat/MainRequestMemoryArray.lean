import Projects.thermostat.MainRequestMemoryFrames
import Projects.thermostat.MainRequestByteValue
import Projects.thermostat.MainNextArrayRelocate
import Projects.thermostat.MainNextArrayFrame
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestMemoryArray
open E5R E5R.Thermostat HttpRequestSpec

theorem array (B : Board) (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (stack : Memory.Block B sp 5232) (view : MainNextArrayView.At ram (sp+4248#32) head) :
    MainNextArrayView.At (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+3344#32) head := by
  have source := MainNextArrayFrame.preserve view (MainRequestMemoryFrames.arraySource ram sp rx head amount method path pathLen query queryLen)
  have copied := MainNextArrayRelocate.contract source
    (MainRamCopy264.bytes (MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen) sp 1062 836 (by decide) stack)
  exact MainNextArrayFrame.preserve copied (MainRequestMemoryFrames.arrayTail ram sp rx head amount method path pathLen query queryLen)

theorem minor (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) (bound : head.minor≤1) :
    MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen (sp+3608#32)=BitVec.ofNat 8 head.minor := by
  let copied := MainRequestMemory.copied ram sp rx head amount method path pathLen query queryLen
  have region := MainRequestZero.frame (MainRequestTailCore.minorRaw copied sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount))) sp 3608 1 (by decide) (Or.inl (by decide))
  have byte := region ⟨0,by decide⟩
  simp only [BitVec.add_zero] at byte
  have stored := MainRequestStoreWords.MinorRawStores_3608 (MainRequestTailCore.padding copied sp) sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount))
  exact byte.trans (stored.trans (MainRequestByteValue.ofNat head.minor (by omega)))
/-- Exact copied header count in the completed Request object. -/
theorem count (B : Board) (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (stack : Memory.Block B sp 5232) (view : MainNextArrayView.At ram (sp+4248#32) head) :
    ramRead (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+3600#32) .w=BitVec.ofNat 32 head.headers.length := by
  simpa only [BitVec.add_assoc,show 3344#32+256#32=3600#32 by decide +kernel] using
    (array B ram sp rx head amount method path pathLen query queryLen stack view).count

end E5R.Thermostat.MainRequestMemoryArray
