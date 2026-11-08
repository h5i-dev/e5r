import Projects.thermostat.MainRequestAfterFrames
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestMemoryViews
open E5R E5R.Thermostat HttpRequestSpec

structure At (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) : Prop where
  path : ramRead ram (sp+3616#32) .w=path
  pathLength : ramRead ram (sp+3620#32) .w=pathLen
  query : ramRead ram (sp+3624#32) .w=query
  queryLength : ramRead ram (sp+3628#32) .w=queryLen
  body : ramRead ram (sp+3632#32) .w=BitVec.ofNat 32 head.len+rx
  bodyLength : ramRead ram (sp+3636#32) .w=BitVec.ofNat 32 amount
  raw : ramRead ram (sp+3640#32) .w=rx
  rawLength : ramRead ram (sp+3644#32) .w=BitVec.ofNat 32 (head.len+amount)
  method : ram (sp+3684#32)=byteOf method 0
  params : ∀ i : Fin 36, ram ((sp+3648#32)+BitVec.ofNat 32 i.val)=0#8

theorem contract (B : Board) (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word)
    (bound : head.len+amount≤2048) (stack : Memory.Block B sp 5232) :
    At (MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen) sp rx head amount method path pathLen query queryLen := by
  let initialBody := MainRequestMemory.body ram sp rx head amount method
  let staged := MainRequestMemory.metadata ram sp rx head amount method path pathLen query queryLen
  let copied := MainRequestMemory.copied ram sp rx head amount method path pathLen query queryLen
  let packed := MainRequestTailCore.padding copied sp
  let minorRaw := MainRequestTailCore.minorRaw copied sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount))
  let after := MainRequestMemory.after ram sp rx head amount method path pathLen query queryLen
  have ur := MainRequestAfterFrames.metadata ram sp rx head amount method path pathLen query queryLen 3616 16 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have bo := MainRequestAfterFrames.body ram sp rx head amount method path pathLen query queryLen 3632 8 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have mo := MainRequestAfterFrames.body ram sp rx head amount method path pathLen query queryLen 3684 1 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide))
  have ra := MainRequestZero.frame minorRaw sp 3640 8 (by decide) (Or.inl (by decide))
  have uriWord (off : Nat) (small : off+4≤16) : ramRead after ((sp+3616#32)+BitVec.ofNat 32 off) .w=ramRead staged ((sp+3616#32)+BitVec.ofNat 32 off) .w := ViewFrame.word ur off small
  have bodyWord (off : Nat) (small : off+4≤8) : ramRead after ((sp+3632#32)+BitVec.ofNat 32 off) .w=ramRead initialBody ((sp+3632#32)+BitVec.ofNat 32 off) .w := ViewFrame.word bo off small
  have rawWord (off : Nat) (small : off+4≤8) : ramRead after ((sp+3640#32)+BitVec.ofNat 32 off) .w=ramRead minorRaw ((sp+3640#32)+BitVec.ofNat 32 off) .w := ViewFrame.word ra off small
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,MainRequestZero.bytes minorRaw sp stack⟩
  · have read := uriWord 0 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+0#32=3616#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3616 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := uriWord 4 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+4#32=3620#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3620 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := uriWord 8 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+8#32=3624#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3624 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := uriWord 12 (by decide)
    simp only [BitVec.add_assoc,show 3616#32+12#32=3628#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MetadataStores_3628 initialBody sp path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2))
  · have read := bodyWord 0 (by decide)
    simp only [BitVec.add_zero] at read ⊢
    exact read.trans (MainRequestStoreWords.BodyStores_3632 ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method)
  · have read := bodyWord 4 (by decide)
    simp only [BitVec.add_assoc,show 3632#32+4#32=3636#32 by decide +kernel] at read ⊢
    have value := MainRequestStoreWords.BodyStores_3636 ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method
    have sub : BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len=BitVec.ofNat 32 amount := by
      have actual := BitVec.ofNat_sub_ofNat_of_le (w := 32) (head.len+amount) head.len (by omega) (by omega)
      have natSub : head.len+amount-head.len=amount := by omega
      simpa only [natSub] using actual
    exact read.trans (value.trans sub)
  · have read := rawWord 0 (by decide)
    simp only [BitVec.add_zero] at read ⊢
    exact read.trans (MainRequestStoreWords.MinorRawStores_3640 packed sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount)))
  · have read := rawWord 4 (by decide)
    simp only [BitVec.add_assoc,show 3640#32+4#32=3644#32 by decide +kernel] at read ⊢
    exact read.trans (MainRequestStoreWords.MinorRawStores_3644 packed sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount)))
  · have byte := mo ⟨0,by decide⟩
    simp only [BitVec.add_zero] at byte
    exact byte.trans (MainRequestStoreWords.BodyStores_3684 ram sp (BitVec.ofNat 32 head.len+rx) (BitVec.ofNat 32 (head.len+amount)-BitVec.ofNat 32 head.len) method)
end E5R.Thermostat.MainRequestMemoryViews
