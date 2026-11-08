import Projects.thermostat.ResponseHeadStart
import Projects.thermostat.ResponseHeadSuffix
import Projects.thermostat.ResponseHeadTag
import Projects.thermostat.ResponseHeadRestore
namespace E5R.Thermostat.ResponseHead
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Actual write_head entry through RET. The prefix, every append/decimal call,
    conditional omissions and saved-register restoration follow the pinned ELF. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (frame dst ctptr : Word)
    (status body : Nat) (ct : List (BitVec 8)) (close : Bool)
    (hlo : 100≤status) (hhi : status≤599) (hbody : body≤832) (hct : ct.length≤16) (hfield : ResponseHeadSpec.Field ct)
    (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hd : Memory.Block B dst 192)
    (hsep : WordRegions.Disjoint frame 96 dst 192)
    (hsrc : ReadBytes.Span B img ram ctptr ct) (hsstack : WordRegions.Disjoint ctptr ct.length frame 96)
    (hsout : WordRegions.Disjoint ctptr ct.length dst 192)
    (h2 : c.get 2=frame+96#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=BitVec.ofNat 32 status) (h13 : c.get 13=ctptr) (h14 : c.get 14=BitVec.ofNat 32 ct.length)
    (h15 : c.get 15=BitVec.ofNat 32 body) (h16 : c.get 16=ResponseHeadBodyMath.boolWord close)
    (hp : c.pc=0x80003e4e#32) :
    ∃ d n after, n≤2247 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ FormatCursor.Returned c d ∧
      d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (ResponseHeadSpec.bytes status ct body close).length ∧
      Bytes.Span B after dst (ResponseHeadSpec.bytes status ct body close) ∧
      (∀ x, (∀ i : Fin 96, x≠frame+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 192, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) := by
  obtain ⟨a,na,ma,ba,ta,qa⟩ := ResponseHeadStart.contract c ram frame dst ctptr status body ct close hlo hhi hbody hct hfield
    hm ha hd hsep hsrc hsstack hsout h2 h10 h11 h12 h13 h14 h15 h16 hp
  obtain ⟨b,nb,after,bb,tb,pb,b2,b10,b11,kb,hbytes,hframe⟩ := ResponseHeadSuffix.contract a ma frame dst ctptr
    status body ct close hlo hhi hbody hct hm ha hd hsep qa.source hsstack hsout qa.written
    qa.cap qa.cachedStatus qa.cachedBody qa.cachedClose qa.pc qa.x1 qa.x10 qa.x11 qa.x12 qa.x13
    qa.x2 qa.x8 qa.x9 qa.x18 qa.x19 qa.x20 qa.x21 qa.x23 qa.x24 qa.x25 qa.x26 qa.x27
  have saved : ResponseHeadSaved.At after frame c := ResponseHeadSaved.envelope qa.saved hframe hsep
  obtain ⟨t,tt,pt,t17,t5,ft,kt⟩ := ResponseHeadTag.contract B b after 1#32
    (BitVec.ofNat 32 (ResponseHeadSpec.bytes status ct body close).length) b10 b11 pb
  have t2 := (ft 2 (by decide) (by decide)).trans b2
  obtain ⟨d,td,pd,d1,d8,d9,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d2,d10,d11,fd,kd⟩ :=
    ResponseHeadRestore.contract B t after frame 1#32 (BitVec.ofNat 32 (ResponseHeadSpec.bytes status ct body close).length)
      t2 t17 t5 hm ha pt
  refine ⟨d,na+nb+3+17,after,by omega,((ta.trans tb).trans tt).trans td,?_,d10,d11,hbytes,?_⟩
  · exact ⟨by rw [pd,saved.x1],d2.trans h2.symm,kd.trans (kt.trans (kb.trans qa.csr)),
      d1.trans saved.x1,d8.trans saved.x8,d9.trans saved.x9,d18.trans saved.x18,d19.trans saved.x19,
      d20.trans saved.x20,d21.trans saved.x21,d22.trans saved.x22,d23.trans saved.x23,d24.trans saved.x24,
      d25.trans saved.x25,d26.trans saved.x26,d27.trans saved.x27⟩
  · intro x hs ho
    exact (hframe x (fun i => hs ⟨i.val,by have := i.isLt;omega⟩) ho).trans (qa.memoryFrame x hs ho)
end E5R.Thermostat.ResponseHead
