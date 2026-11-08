import Projects.thermostat.SendStart
namespace E5R.Thermostat.SendHeader
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

structure Post (c d : Core) (before after : Word → BitVec 8) (frame obj res tx io : Word)
    (status : Nat) (ct payload : List (BitVec 8)) (close head : Bool) : Prop where
  pc : d.pc=0x800003c0#32
  csr : d.sameCsr c
  saved : SendSaved.At after frame c
  payloadBytes : ReadBytes.Span B img after (tx+192#32) payload
  headerBytes : Bytes.Span B after tx (ResponseHeadSpec.bytes status ct payload.length close)
  memoryFrame : ∀ x, (∀ i : Fin 144, x≠frame+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) → (∀ i : Fin 192, x≠tx+BitVec.ofNat 32 i.val) → after x=before x
  bodyPointer : ramRead after (obj+0#32) .w=tx+192#32
  bodyCapacity : ramRead after (obj+4#32) .w=832#32
  cachedIo : ramRead after (obj+16#32) .w=io
  resultTag : d.get 10=1#32
  resultLength : d.get 11=BitVec.ofNat 32 (ResponseHeadSpec.bytes status ct payload.length close).length
  x2 : d.get 2=frame+96#32
  x8 : d.get 8=obj
  x9 : d.get 9=res
  x18 : d.get 18=obj+48#32
  x19 : d.get 19=tx
  x20 : d.get 20=BitVec.ofNat 32 payload.length
  x21 : d.get 21=BitVec.ofNat 32 status
  x22 : d.get 22=ResponseHeadBodyMath.boolWord close
  x23 : d.get 23=ResponseHeadBodyMath.boolWord head
  x24 : d.get 24=c.get 24
  x25 : d.get 25=c.get 25
  x26 : d.get 26=c.get 26
  x27 : d.get 27=c.get 27

theorem contract (c : Core) (ram : Word → BitVec 8) (frame obj res tx io ctptr : Word)
    (raw status : Nat) (ct payload : List (BitVec 8)) (close head : Bool)
    (h : SendInput.Pre c ram frame obj res tx io ctptr raw status ct payload close head) :
    ∃ d n after, n≤2291 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ Post c d ram after frame obj res tx io status ct payload close head := by
  obtain ⟨a,na,ma,ba,ta,qa⟩ := SendStart.contract c ram frame obj res tx io ctptr raw status ct payload close head h
  have stack96 : Memory.Block B frame 96 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) h.stack (by decide : 0<96) (by decide : 0+96≤144)
  have tx192 : Memory.Block B tx 192 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) h.txBlock (by decide : 0<192) (by decide : 0+192≤1024)
  obtain ⟨d,nd,after,bd,td,hr,d10,d11,hbytes,hframe⟩ := ResponseHead.contract a ma frame tx ctptr status payload.length ct close
    (by have := h.statusLo;omega) h.statusHi (SendInput.payload_bound h) h.ctBound h.field stack96 h.stackAligned tx192
    (WordRegions.symm (WordRegions.shrink h.txStack (by decide) (by decide))) qa.source
    (WordRegions.shrink h.ctStack (by omega) (by decide)) (WordRegions.shrink h.ctTx (by omega) (by decide))
    qa.x2 qa.x10 qa.x11 qa.x12 qa.x13 qa.x14 qa.x15 qa.x16 qa.pc
  have objectRegion : ViewFrame.Region ma after obj 89 := fun i => hframe _
    (WordRegions.shrink h.objectStack (by decide) (by decide) i)
    (WordRegions.shrink h.objectTx (by decide) (by decide) i)
  have saved : SendSaved.At after frame c := SendSaved.region qa.saved (by
    intro i
    apply hframe _
    · have hh := StoreWords.offsets frame 108 36 0 96 (by decide) (by decide) (by decide) i
      simpa only [BitVec.add_zero] using hh
    · intro j
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact Ne.symm (h.txStack ⟨j.val,by have := j.isLt;omega⟩ ⟨108+i.val,by have := i.isLt;omega⟩))
  have payloadView : ReadBytes.Span B img after (tx+192#32) payload := ReadFrame.span qa.payloadBytes (by
    intro i
    apply hframe _
    · exact Subregion.left (WordRegions.shrink (n' := 1024) (m' := 96) h.txStack (by decide) (by decide)) 192 payload.length (by have := SendInput.payload_bound h;omega) i
    · have hh := StoreWords.offsets tx 192 payload.length 0 192 (by have := SendInput.payload_bound h;omega) (by decide) (by omega) i
      simpa only [BitVec.add_zero] using hh)
  refine ⟨d,na+nd,after,by omega,ta.trans td,?_,hr.csr.trans qa.csr,saved,payloadView,hbytes,?_,
    (ViewFrame.word objectRegion 0 (by decide)).trans qa.bodyPointer,
    (ViewFrame.word objectRegion 4 (by decide)).trans qa.bodyCapacity,
    (ViewFrame.word objectRegion 16 (by decide)).trans qa.cachedIo,d10,d11,
    hr.sp.trans qa.x2,
    hr.x8.trans qa.x8,
    hr.x9.trans qa.x9,
    hr.x18.trans qa.x18,
    hr.x19.trans qa.x19,
    hr.x20.trans qa.x20,
    hr.x21.trans qa.x21,
    hr.x22.trans qa.x22,
    hr.x23.trans qa.x23,
    hr.x24.trans qa.x24,
    hr.x25.trans qa.x25,
    hr.x26.trans qa.x26,
    hr.x27.trans qa.x27⟩
  · rw [hr.pc,qa.x1];decide +kernel
  · intro x hs ho ht
    exact (hframe x (fun i => hs ⟨i.val,by have := i.isLt;omega⟩) ht).trans (qa.memoryFrame x hs ho)
end E5R.Thermostat.SendHeader
