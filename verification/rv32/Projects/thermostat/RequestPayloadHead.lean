import Projects.thermostat.RequestPayloadFields
import Projects.thermostat.MainNextArrayRelocate
import Projects.thermostat.MainNextArrayFrame
set_option autoImplicit false
namespace E5R.Thermostat.RequestPayloadHead
open E5R E5R.Thermostat HttpRequestSpec
abbrev sp := RuntimeRequest.sp
abbrev rx := RuntimeRequest.rx

theorem contract (ram : Word → BitVec 8) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) (low : Word)
    (kind : head.framing=.empty ∨ head.framing=.chunked) (minorBound : head.minor≤1)
    (stack : Memory.Block UartPlatform.board sp 5232) (source : MainNextArrayView.At ram (sp+4248#32) head) :
    HeadCompletedView.At (RequestPayloadFields.memory ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low) (sp+3312#32) head := by
  let method := MainRequestBuild.method input head
  let path := rx+BitVec.ofNat 32 head.target.1
  let pathLen := MainRequestBuild.pathLength input head
  let query := MainRequestBuild.queryPtr input head
  let queryLen := MainRequestBuild.queryLength input head
  let tag := HeadCompletedView.framingTag head.framing
  let ms := BitVec.ofNat 32 head.method.1
  let me := BitVec.ofNat 32 head.method.2
  let ts := BitVec.ofNat 32 head.target.1
  let te := BitVec.ofNat 32 head.target.2
  let minor := BitVec.ofNat 32 head.minor
  let initialBody := RequestPayloadPrefix.body ram sp rx head.len (head.len+amount) method
  let staged := RequestPayloadPrefix.metadata ram sp rx head.len (head.len+amount) method path pathLen query queryLen tag 0#32 low ms me ts te
  let copied := RequestPayloadPrefix.memory ram sp rx head.len (head.len+amount) method path pathLen query queryLen tag 0#32 low ms me ts te
  let packed := MainRequestTailCore.padding copied sp
  let minorRaw := MainRequestTailCore.minorRaw copied sp minor rx (BitVec.ofNat 32 rawUsed)
  let after := RequestPayloadFields.memory ram input head amount rawUsed tag 0#32 low
  have fields := RequestPayloadAfter.metadata ram sp rx head.len (head.len+amount) rawUsed method path pathLen query queryLen tag 0#32 low ms me ts te minor
    3312 32 (by decide) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have word (off : Nat) (bound : off+4≤32) : ramRead after ((sp+3312#32)+BitVec.ofNat 32 off) .w=ramRead staged ((sp+3312#32)+BitVec.ofNat 32 off) .w := ViewFrame.word fields off bound
  have bodyFrame := MainRequestStoreFrames.body ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method
    4248 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  have metaFrame := RequestPayloadMetadataFrame.metadata initialBody sp path pathLen query queryLen tag 0#32 low
    (extend .h true (ramRead ram (sp+4512#32) .h)) (extend .h true (ramRead ram (sp+4514#32) .h))
    (extend .h true (ramRead ram (sp+4516#32) .h)) ms me ts te 4248 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  have stagedArray := MainNextArrayFrame.preserve (MainNextArrayFrame.preserve source bodyFrame) metaFrame
  have copiedArray := MainNextArrayRelocate.contract stagedArray (MainRamCopy264.bytes staged sp 1062 836 (by decide) stack)
  have array : MainNextArrayView.At after (sp+3344#32) head := MainNextArrayFrame.preserve copiedArray
    (RequestPayloadMemory.array_frame copied sp minor rx (BitVec.ofNat 32 rawUsed))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,array.bound,?_,?_,?_,?_⟩
  · have read := word 0 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+0#32=3312#32 by decide +kernel] at read ⊢
    exact read.trans (RequestPayloadWords.word_3312 initialBody sp path pathLen query queryLen tag 0#32 low _ _ _ ms me ts te)
  · have read := word 4 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+4#32=3316#32 by decide +kernel] at read ⊢
    exact read.trans (RequestPayloadWords.word_3316 initialBody sp path pathLen query queryLen tag 0#32 low _ _ _ ms me ts te)
  · intro n selected
    rcases kind with selectedEmpty|selectedChunked
    · rw [selectedEmpty] at selected;cases selected
    · rw [selectedChunked] at selected;cases selected
  · have read := word 16 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+16#32=3328#32 by decide +kernel] at read ⊢
    exact read.trans (RequestPayloadWords.word_3328 initialBody sp path pathLen query queryLen tag 0#32 low _ _ _ ms me ts te)
  · have read := word 20 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+20#32=3332#32 by decide +kernel] at read ⊢
    exact read.trans (RequestPayloadWords.word_3332 initialBody sp path pathLen query queryLen tag 0#32 low _ _ _ ms me ts te)
  · have read := word 24 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+24#32=3336#32 by decide +kernel] at read ⊢
    exact read.trans (RequestPayloadWords.word_3336 initialBody sp path pathLen query queryLen tag 0#32 low _ _ _ ms me ts te)
  · have read := word 28 (by decide)
    simp only [BitVec.add_assoc,show 3312#32+28#32=3340#32 by decide +kernel] at read ⊢
    exact read.trans (RequestPayloadWords.word_3340 initialBody sp path pathLen query queryLen tag 0#32 low _ _ _ ms me ts te)
  · simpa only [BitVec.add_assoc,show 3344#32+256#32=3600#32 by decide +kernel,show 3312#32+288#32=3600#32 by decide +kernel] using array.count
  · intro i
    simpa only [BitVec.add_assoc,show 3312#32+32#32=3344#32 by decide +kernel,
      show 3312#32+36#32=3348#32 by decide +kernel,show 3312#32+40#32=3352#32 by decide +kernel,
      show 3312#32+44#32=3356#32 by decide +kernel,show 3344#32+4#32=3348#32 by decide +kernel,
      show 3344#32+8#32=3352#32 by decide +kernel,show 3344#32+12#32=3356#32 by decide +kernel] using array.headers i
  · simpa only [BitVec.add_assoc,show 3344#32+260#32=3604#32 by decide +kernel,show 3312#32+292#32=3604#32 by decide +kernel] using array.length
  · have region := MainRequestZero.frame minorRaw sp 3608 1 (by decide) (Or.inl (by decide))
    have byte := region ⟨0,by decide⟩
    simp only [BitVec.add_zero] at byte
    have stored := MainRequestStoreWords.MinorRawStores_3608 packed sp minor rx (BitVec.ofNat 32 rawUsed)
    have value : after (sp+3608#32)=byteOf minor 0 := byte.trans stored
    rw [show (sp+3312#32)+296#32=sp+3608#32 by rw [BitVec.add_assoc];rfl]
    exact value.trans (MainRequestByteValue.ofNat head.minor (by omega))
end E5R.Thermostat.RequestPayloadHead
