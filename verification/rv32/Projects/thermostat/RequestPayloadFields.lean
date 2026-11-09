import Projects.thermostat.RequestPayloadAfter
import Projects.thermostat.RequestPayloadWords
import Projects.thermostat.RuntimeRequest
set_option autoImplicit false
namespace E5R.Thermostat.RequestPayloadFields
open E5R E5R.Thermostat HttpRequestSpec
abbrev sp := RuntimeRequest.sp
abbrev rx := RuntimeRequest.rx

def memory (ram : Word → BitVec 8) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) (tag pad low : Word) :=
  RequestPayloadCore.memory ram sp rx head.len (head.len+amount) rawUsed (MainRequestBuild.method input head)
    (rx+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength input head) (MainRequestBuild.queryPtr input head)
    (MainRequestBuild.queryLength input head) tag pad low (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2)
    (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.minor)

/-- Actual fields preserve independent encoded and decoded extents, with no
    selected-framing or high-payload-zero assumption in the RAM derivation. -/
theorem contract (ram : Word → BitVec 8) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) (tag pad low : Word)
    (used : head.len+amount≤rawUsed) (bound : rawUsed≤2048) (stack : Memory.Block UartPlatform.board sp 5232) :
    RuntimeRequest.Fields (memory ram input head amount rawUsed tag pad low) input head amount rawUsed := by
  let method := MainRequestBuild.method input head
  let path := rx+BitVec.ofNat 32 head.target.1
  let pathLen := MainRequestBuild.pathLength input head
  let query := MainRequestBuild.queryPtr input head
  let queryLen := MainRequestBuild.queryLength input head
  let ms := BitVec.ofNat 32 head.method.1
  let me := BitVec.ofNat 32 head.method.2
  let ts := BitVec.ofNat 32 head.target.1
  let te := BitVec.ofNat 32 head.target.2
  let minor := BitVec.ofNat 32 head.minor
  let r0 := RequestPayloadPrefix.body ram sp rx head.len (head.len+amount) method
  let staged := RequestPayloadPrefix.metadata ram sp rx head.len (head.len+amount) method path pathLen query queryLen tag pad low ms me ts te
  let copied := RequestPayloadPrefix.memory ram sp rx head.len (head.len+amount) method path pathLen query queryLen tag pad low ms me ts te
  let packed := MainRequestTailCore.padding copied sp
  let minorRaw := MainRequestTailCore.minorRaw copied sp minor rx (BitVec.ofNat 32 rawUsed)
  let after := memory ram input head amount rawUsed tag pad low
  have uri := RequestPayloadAfter.metadata ram sp rx head.len (head.len+amount) rawUsed method path pathLen query queryLen tag pad low ms me ts te minor
    3616 16 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have bo := RequestPayloadAfter.body ram sp rx head.len (head.len+amount) rawUsed method path pathLen query queryLen tag pad low ms me ts te minor
    3632 8 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have mo := RequestPayloadAfter.body ram sp rx head.len (head.len+amount) rawUsed method path pathLen query queryLen tag pad low ms me ts te minor
    3684 1 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide))
  have ra := MainRequestZero.frame minorRaw sp 3640 8 (by decide) (Or.inl (by decide))
  have uriWord (off : Nat) (small : off+4≤16) : ramRead after ((sp+3616#32)+BitVec.ofNat 32 off) .w=ramRead staged ((sp+3616#32)+BitVec.ofNat 32 off) .w := ViewFrame.word uri off small
  have bodyWord (off : Nat) (small : off+4≤8) : ramRead after ((sp+3632#32)+BitVec.ofNat 32 off) .w=ramRead r0 ((sp+3632#32)+BitVec.ofNat 32 off) .w := ViewFrame.word bo off small
  have rawWord (off : Nat) (small : off+4≤8) : ramRead after ((sp+3640#32)+BitVec.ofNat 32 off) .w=ramRead minorRaw ((sp+3640#32)+BitVec.ofNat 32 off) .w := ViewFrame.word ra off small
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,MainRequestZero.bytes minorRaw sp stack⟩
  · have read := uriWord 0 (by decide)
    simp only [BitVec.add_zero] at read
    exact read.trans (RequestPayloadWords.word_3616 r0 sp path pathLen query queryLen tag pad low _ _ _ ms me ts te)
  · have read := uriWord 4 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+4#32=3620#32 by decide +kernel] at read
    exact read.trans (RequestPayloadWords.word_3620 r0 sp path pathLen query queryLen tag pad low _ _ _ ms me ts te)
  · have read := uriWord 8 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+8#32=3624#32 by decide +kernel] at read
    exact read.trans (RequestPayloadWords.word_3624 r0 sp path pathLen query queryLen tag pad low _ _ _ ms me ts te)
  · have read := uriWord 12 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+12#32=3628#32 by decide +kernel] at read
    exact read.trans (RequestPayloadWords.word_3628 r0 sp path pathLen query queryLen tag pad low _ _ _ ms me ts te)
  · have read := bodyWord 0 (by decide)
    simp only [BitVec.add_zero] at read
    exact read.trans (MainRequestStoreWords.BodyStores_3632 ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method)
  · have read := bodyWord 4 (by decide)
    simp only [BitVec.add_assoc,show 3632#32+4#32=3636#32 by decide +kernel] at read
    have value := MainRequestStoreWords.BodyStores_3636 ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method
    have sub : BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len=BitVec.ofNat 32 amount := by
      have actual := BitVec.ofNat_sub_ofNat_of_le (w := 32) (head.len+amount) head.len (by omega) (by omega)
      simpa only [Nat.add_sub_cancel_left] using actual
    exact read.trans (value.trans sub)
  · have read := rawWord 0 (by decide)
    simp only [BitVec.add_zero] at read
    exact read.trans (MainRequestStoreWords.MinorRawStores_3640 packed sp minor rx (BitVec.ofNat 32 rawUsed))
  · have read := rawWord 4 (by decide)
    simp only [BitVec.add_assoc,show 3640#32+4#32=3644#32 by decide +kernel] at read
    exact read.trans (MainRequestStoreWords.MinorRawStores_3644 packed sp minor rx (BitVec.ofNat 32 rawUsed))
  · have byte := mo ⟨0,by decide⟩
    simp only [BitVec.add_zero] at byte
    exact byte.trans (MainRequestStoreWords.BodyStores_3684 ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method)
end E5R.Thermostat.RequestPayloadFields
