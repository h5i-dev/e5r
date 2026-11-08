import Projects.thermostat.MainRequestMemoryArray
import Projects.thermostat.MainRequestHeadAssemble
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestMemoryHead
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (kind : head.framing=.length amount) (amountBound : amount≤1024) (minorBound : head.minor≤1)
    (stack : Memory.Block B sp 5232) (view : MainNextArrayView.At ram (sp+4248#32) head) :
    HeadCompletedView.At (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+3312#32) head := by
  let initialBody := MainRequestMemory.body ram sp rx head amount method
  let staged := MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen
  let after := MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen
  have region := MainRequestMemoryFrames.low ram sp rx head amount method path pathLen query queryLen
  have word (off : Nat) (bound : off+4≤32) :
      ramRead after ((sp+3312#32)+BitVec.ofNat 32 off) .w=ramRead staged ((sp+3312#32)+BitVec.ofNat 32 off) .w := ViewFrame.word region off bound
  have small : (BitVec.ofNat 32 amount).toNat<65536 := by
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : amount<2^32)]
    omega
  refine MainRequestHeadAssemble.contract after (sp+3312#32) head amount kind amountBound ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have read := word 0 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+0#32=3312#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3312 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := word 4 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+4#32=3316#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3316 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := word 8 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+8#32=3320#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestPayloadStored.low_word initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) small)
  · have read := word 12 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+12#32=3324#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestPayloadStored.high_word initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := word 16 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+16#32=3328#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3328 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := word 20 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+20#32=3332#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3332 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := word 24 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+24#32=3336#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3336 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := word 28 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+28#32=3340#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3340 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · simpa only [BitVec.add_assoc,show 3312#32+32#32=3344#32 by decide +kernel] using MainRequestMemoryArray.array B ram sp rx head amount method path pathLen query queryLen stack view
  · simpa only [BitVec.add_assoc,show 3312#32+296#32=3608#32 by decide +kernel] using MainRequestMemoryArray.minor ram sp rx head amount method path pathLen query queryLen minorBound
/-- Exact copied header count in the completed Request object. -/
theorem count (B : Board) (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (kind : head.framing=.length amount) (amountBound : amount≤1024) (minorBound : head.minor≤1) (stack : Memory.Block B sp 5232) (view : MainNextArrayView.At ram (sp+4248#32) head) :
    ramRead (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) (sp+3600#32) .w=BitVec.ofNat 32 head.headers.length := by
  simpa only [BitVec.add_assoc,show 3312#32+288#32=3600#32 by decide +kernel] using
    (contract B ram sp rx head amount method path pathLen query queryLen kind amountBound minorBound stack view).count

end E5R.Thermostat.MainRequestMemoryHead
