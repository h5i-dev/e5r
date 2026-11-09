import Projects.thermostat.SendStart
import Projects.thermostat.StackAccess
import Projects.thermostat.StackSendInput
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackSendStart
open E5R E5R.Thermostat SendStart
abbrev B := StackBoard.board
structure Post (c d : Core) (before after : Word → BitVec 8) (frame obj res tx io ctptr : Word)
    (status : Nat) (ct payload : List (BitVec 8)) (close head : Bool) : Prop where
  pc : d.pc=0x80003e4e#32
  csr : d.sameCsr c
  saved : SendSaved.At after frame c
  source : ReadBytes.Span B img after ctptr ct
  payloadBytes : ReadBytes.Span B img after (tx+192#32) payload
  memoryFrame : ∀ x, (∀ i : Fin 144, x≠frame+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) → after x=before x
  bodyPointer : ramRead after (obj+0#32) .w=tx+192#32
  bodyCapacity : ramRead after (obj+4#32) .w=832#32
  cachedIo : ramRead after (obj+16#32) .w=io
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
  x1 : d.get 1=0x800003c0#32
  x10 : d.get 10=tx
  x11 : d.get 11=192#32
  x12 : d.get 12=BitVec.ofNat 32 status
  x13 : d.get 13=ctptr
  x14 : d.get 14=BitVec.ofNat 32 ct.length
  x15 : d.get 15=BitVec.ofNat 32 payload.length
  x16 : d.get 16=ResponseHeadBodyMath.boolWord close

theorem contract (c : Core) (ram : Word → BitVec 8) (frame obj res tx io ctptr : Word)
    (raw status : Nat) (ct payload : List (BitVec 8)) (close head : Bool)
    (h : StackSendInput.Pre c ram frame obj res tx io ctptr raw status ct payload close head) :
    ∃ d n after, n≤44 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ Post c d ram after frame obj res tx io ctptr status ct payload close head := by
  obtain ⟨a,ta,pa,a2,fa,ka⟩ := SendSave.contract B c ram frame h.sp h.stack h.stackAligned h.pc
  let saved := SendSave.memory ram frame c
  have objectRegion : ViewFrame.Region ram saved obj 89 := fun i => SendSaveData.frame ram frame c _ (h.objectStack i)
  have fresh : saved (obj+45#32)=0#8 := (objectRegion ⟨45,by decide⟩).trans h.fresh
  obtain ⟨b,tb,pb,b8,b9,b10,b11,b18,fb,kb⟩ := SendFresh.contract B a saved obj res
    ((fa 10 (by decide)).trans h.resultArg) ((fa 11 (by decide)).trans h.objectArg) h.object fresh pa
  have b2 : b.get 2=frame+96#32 := (fb 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (a2)
  have b24 : b.get 24=c.get 24 := (fb 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fa 24 (by decide))
  have b25 : b.get 25=c.get 25 := (fb 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fa 25 (by decide))
  have b26 : b.get 26=c.get 26 := (fb 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fa 26 (by decide))
  have b27 : b.get 27=c.get 27 := (fb 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (fa 27 (by decide))
  have hh_cap := ReadRegion.read objectRegion 12 .w (by decide)
  have b_cap := hh_cap.trans h.capacity
  have hh_io := ReadRegion.read objectRegion 24 .w (by decide)
  have b_io := hh_io.trans h.ioWord
  have hh_tx := ReadRegion.read objectRegion 8 .w (by decide)
  have b_tx := hh_tx.trans h.txWord
  have hh_ct := ReadRegion.read objectRegion 28 .w (by decide)
  have b_ct := hh_ct.trans h.ctWord
  have hh_len := ReadRegion.read objectRegion 32 .w (by decide)
  have b_len := hh_len.trans h.ctLength
  have hh_body := ReadRegion.read objectRegion 36 .w (by decide)
  have b_body := hh_body.trans h.bodyLength
  have hh_status := ReadRegion.read objectRegion 40 .h (by decide)
  have b_status := (congrArg (extend .h false) hh_status).trans h.statusWord
  have hh_close := ReadRegion.read objectRegion 42 .b (by decide)
  have b_close := (congrArg (extend .b false) hh_close).trans h.closeWord
  have hh_head := ReadRegion.read objectRegion 46 .b (by decide)
  have b_head := (congrArg (extend .b false) hh_head).trans h.headWord
  obtain ⟨d,td,pd,d10,d11,d12,d19,d13,d14,d21,d22,d23,d20,fd,kd⟩ := SendLoad.contract B b saved obj tx io ctptr
    ct.length status raw close head b8 h.object h.objectAligned b_cap b_io b_tx b_ct b_len b_body b_status b_close b_head pb
  let after := SendLoad.memory saved obj tx io ctptr
  have d2 : d.get 2=frame+96#32 := (fd 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b2
  have d8 : d.get 8=obj := (fd 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8
  have d9 : d.get 9=res := (fd 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b9
  have d18 : d.get 18=obj+48#32 := (fd 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b18
  have d24 : d.get 24=c.get 24 := (fd 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b24
  have d25 : d.get 25=c.get 25 := (fd 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b25
  have d26 : d.get 26=c.get 26 := (fd 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b26
  have d27 : d.get 27=c.get 27 := (fd 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b27
  obtain ⟨e,ne,bne,te,pe,e20,fe,ke⟩ := SendClip.contract B d after raw h.rawBound d20 d11 pd
  have used : e.get 20=BitVec.ofNat 32 payload.length := by rw [h.clipped];exact e20
  have e2 : e.get 2=frame+96#32 := (fe 2 (by decide)).trans d2
  have e8 : e.get 8=obj := (fe 8 (by decide)).trans d8
  have e9 : e.get 9=res := (fe 9 (by decide)).trans d9
  have e18 : e.get 18=obj+48#32 := (fe 18 (by decide)).trans d18
  have e19 : e.get 19=tx := (fe 19 (by decide)).trans d19
  have e21 : e.get 21=BitVec.ofNat 32 status := (fe 21 (by decide)).trans d21
  have e22 : e.get 22=ResponseHeadBodyMath.boolWord close := (fe 22 (by decide)).trans d22
  have e23 : e.get 23=ResponseHeadBodyMath.boolWord head := (fe 23 (by decide)).trans d23
  have e24 : e.get 24=c.get 24 := (fe 24 (by decide)).trans d24
  have e25 : e.get 25=c.get 25 := (fe 25 (by decide)).trans d25
  have e26 : e.get 26=c.get 26 := (fe 26 (by decide)).trans d26
  have e27 : e.get 27=c.get 27 := (fe 27 (by decide)).trans d27
  have e13 : e.get 13=ctptr := (fe 13 (by decide)).trans d13
  have e14 : e.get 14=BitVec.ofNat 32 ct.length := (fe 14 (by decide)).trans d14
  obtain ⟨f,tf,pf,f10,f16,f11,f12,f15,f1,ff,kf⟩ := SendHeaderCall.contract B e after tx (BitVec.ofNat 32 payload.length)
    status close h.statusLo h.statusHi e19 used e21 e22 pe
  have allFrame (x : Word) (hs : ∀ i : Fin 144, x≠frame+BitVec.ofNat 32 i.val) (ho : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) : after x=ram x :=
    (SendLoadData.frame saved obj tx io ctptr x ho).trans (SendSaveData.frame ram frame c x hs)
  have source : ReadBytes.Span B img after ctptr ct := ReadFrame.span h.source (fun i => allFrame _ (h.ctStack i) (h.ctObject i))
  have bodyStack := Subregion.left h.txStack 192 payload.length (by have hh := StackSendInput.payload_bound h;omega)
  have bodyObj := Subregion.left (WordRegions.symm h.objectTx) 192 payload.length (by have hh := StackSendInput.payload_bound h;omega)
  have payloadView : ReadBytes.Span B img after (tx+192#32) payload := ReadFrame.span h.payloadBytes (fun i => allFrame _ (bodyStack i) (bodyObj i))
  have savedAfter : SendSaved.At after frame c := SendSaved.region (SendSaved.save ram frame c) (by
    intro i
    apply SendLoadData.frame saved obj tx io ctptr _
    intro j
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Ne.symm (h.objectStack j ⟨108+i.val,by have := i.isLt;omega⟩))
  refine ⟨f,10+7+16+ne+9,after,by omega,(((ta.trans tb).trans td).trans te).trans tf,pf,
    kf.trans (ke.trans (kd.trans (kb.trans ka))),savedAfter,source,payloadView,allFrame,
    SendLoadData.slot0 _ _ _ _ _,SendLoadData.slot4 _ _ _ _ _,SendLoadData.slot16 _ _ _ _ _,
    (ff 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e2,
    (ff 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e8,
    (ff 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e9,
    (ff 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e18,
    (ff 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e19,
    (ff 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans used,
    (ff 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e21,
    (ff 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e22,
    (ff 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e23,
    (ff 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e24,
    (ff 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e25,
    (ff 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e26,
    (ff 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e27,
    f1,
    f10,
    f11,
    f12,
    (ff 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e13,
    (ff 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e14,
    f15,
    f16⟩
end E5R.Thermostat.StackSendStart
