import Projects.thermostat.SendHeader
import Projects.thermostat.SendSelect
import Projects.thermostat.SendHeadUart
import Projects.thermostat.SendBodyUart
import Projects.thermostat.SendFinishData
import Projects.thermostat.SendRestore
namespace E5R.Thermostat.SendTransfer
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- All post-header caller instructions, both actual UART write_all futures,
    flush/result stores and the actual send RET. -/
theorem contract (original c : Core) (before ram : Word → BitVec 8) (frame obj res tx io ctptr : Word)
    (raw status : Nat) (ct payload : List (BitVec 8)) (close head : Bool)
    (h : SendInput.Pre original before frame obj res tx io ctptr raw status ct payload close head)
    (q : SendHeader.Post original c before ram frame obj res tx io status ct payload close head)
    (hs : List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes status ct payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body status head payload).length) :
    ∃ d n after, n≤64+UartWriteAll.time (ResponseHeadSpec.bytes status ct payload.length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body status head payload) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes status ct payload.length close)++UartTxLoop.events (ResponseHeadSpec.body status head payload)) ∧
      FormatCursor.Returned original d ∧ ramRead after (res+0#32) .w=0xffffffff#32 ∧
      ramRead after (res+4#32) .w=ResponseHeadBodyMath.boolWord close ∧ after (obj+45#32)=1#8 ∧
      Bytes.Span B after tx (ResponseHeadSpec.bytes status ct payload.length close) ∧
      (∀ x, (∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) → (∀ i : Fin 8, x≠res+BitVec.ofNat 32 i.val) → after x=ram x) := by
  let header := ResponseHeadSpec.bytes status ct payload.length close
  let body := ResponseHeadSpec.body status head payload
  have hb := SendInput.payload_bound h
  have hn : header.length≤120 := by
    have hh := (ResponseHeadPlan.bounds status ct payload.length close (by have := h.statusLo;omega) h.statusHi h.ctBound hb).1 ⟨11,by decide⟩
    rw [ResponseHeadPlan.all] at hh
    exact hh
  have bbound : body.length≤832 := Nat.le_trans (SendSelect.length payload status head) hb
  have savedObj := Subregion.left (WordRegions.symm h.objectStack) 108 36 (by decide)
  have savedRes := Subregion.left (WordRegions.symm h.resultStack) 108 36 (by decide)
  have bodyObj := Subregion.left (WordRegions.symm h.objectTx) 192 payload.length (by omega)
  have headerObj : WordRegions.Disjoint tx header.length obj 89 := WordRegions.shrink (WordRegions.symm h.objectTx) (by omega) (by decide)
  obtain ⟨a,na,ba,ta,pa,a10,fa,ka⟩ := SendSelect.contract B c ram payload status head h.statusLo h.statusHi q.resultTag q.x20 q.x21 q.x23 q.pc
  have a2 := (fa 2 (by decide) (by decide)).trans q.x2
  have a8 := (fa 8 (by decide) (by decide)).trans q.x8
  have a9 := (fa 9 (by decide) (by decide)).trans q.x9
  have a18 := (fa 18 (by decide) (by decide)).trans q.x18
  have a19 := (fa 19 (by decide) (by decide)).trans q.x19
  have a22 := (fa 22 (by decide) (by decide)).trans q.x22
  have a11 := (fa 11 (by decide) (by decide)).trans q.resultLength
  obtain ⟨b,tb,pb,fb,kb,lower1,frame1⟩ := SendHeadUart.contract a ram obj io tx (BitVec.ofNat 32 body.length)
    (ResponseHeadBodyMath.boolWord close) header hs hn a8 a18 a19 a10 a11 a22 h.object h.objectAligned q.cachedIo
    (ReadBytes.of_ram q.headerBytes) (by have := h.txStrict;omega) headerObj hhs pa
  let m1 := SendHeadUart.memory ram obj io tx (BitVec.ofNat 32 body.length) (ResponseHeadBodyMath.boolWord close) header
  let p1 := SendHeadUart.prepared ram obj io tx (BitVec.ofNat 32 body.length) (ResponseHeadBodyMath.boolWord close) header
  have prefix1 : ViewFrame.Region ram p1 obj 20 := SendHeadUartCallData.prefixRegion _ _ _ _ _ _ _
  have ptr1 := (ViewFrame.word lower1 0 (by decide)).trans ((ViewFrame.word prefix1 0 (by decide)).trans q.bodyPointer)
  have cap1 := (ViewFrame.word lower1 4 (by decide)).trans ((ViewFrame.word prefix1 4 (by decide)).trans q.bodyCapacity)
  have io1 := (ViewFrame.word lower1 16 (by decide)).trans ((ViewFrame.word prefix1 16 (by decide)).trans q.cachedIo)
  have len1 := (ViewFrame.word lower1 20 (by decide)).trans (SendHeadUartCallData.slot20 ram obj io tx (BitVec.ofNat 32 body.length) (ResponseHeadBodyMath.boolWord close) header.length)
  have flagP1 : extend .b false (ramRead p1 (obj+44#32) .b)=ResponseHeadBodyMath.boolWord close := by
    have hh : p1 (obj+44#32)=byteOf (ResponseHeadBodyMath.boolWord close) 0 := SendHeadUartCallData.slot44 _ _ _ _ _ _ _
    rw [Memory.load_byte,hh]
    cases close <;> rfl
  have flag1 := (congrArg (extend .b false) (ReadRegion.read lower1 44 .b (by decide))).trans flagP1
  have source1 : ReadBytes.Span B img m1 (tx+192#32) payload := ReadFrame.span q.payloadBytes (fun i => frame1 _ (bodyObj i))
  have b8 := (fb 8 (by decide) (by decide)).trans a8
  have b18 := (fb 18 (by decide) (by decide)).trans a18
  obtain ⟨d,td,pd,fd,kd,lower2,frame2⟩ := SendBodyUart.contract b m1 obj io (tx+192#32) body bs bbound b8 b18 h.object h.objectAligned
    cap1 len1 ptr1 io1 (SendSelect.span source1) (Subregion.nowrap h.txStrict 192 body.length (by omega))
    (Subregion.left (WordRegions.symm h.objectTx) 192 body.length (by omega)) hbs pb
  let m2 := SendBodyUart.memory m1 obj io (tx+192#32) body
  let p2 := SendBodyUart.prepared m1 obj io (tx+192#32) body
  have prefix2 : ViewFrame.Region m1 p2 obj 48 := SendBodyUartCallData.prefixRegion _ _ _ _ _
  have io2 := (ViewFrame.word lower2 16 (by decide)).trans ((ViewFrame.word prefix2 16 (by decide)).trans io1)
  have flag2 := (congrArg (extend .b false) (ReadRegion.read lower2 44 .b (by decide))).trans
    ((congrArg (extend .b false) (ReadRegion.read prefix2 44 .b (by decide))).trans flag1)
  have d8 := (fd 8 (by decide) (by decide)).trans b8
  have d9 := (fd 9 (by decide) (by decide)).trans ((fb 9 (by decide) (by decide)).trans a9)
  obtain ⟨e,te,pe,e10,e22,e11,fe,ke⟩ := SendFinish.contract B d m2 obj res io (ResponseHeadBodyMath.boolWord close)
    d8 d9 h.object h.objectAligned h.result h.resultAligned io2 flag2 pd
  let final := SendFinish.memory m2 obj res io (ResponseHeadBodyMath.boolWord close)
  have allFrame (x : Word) (ho : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) (hr : ∀ i : Fin 8, x≠res+BitVec.ofNat 32 i.val) : final x=ram x :=
    (SendFinishData.frame m2 obj res io (ResponseHeadBodyMath.boolWord close) x ho hr).trans ((frame2 x ho).trans (frame1 x ho))
  have saved : SendSaved.At final frame original := SendSaved.region q.saved (fun i => allFrame _ (savedObj i) (savedRes i))
  have e2 := (fe 2 (by decide) (by decide) (by decide)).trans ((fd 2 (by decide) (by decide)).trans ((fb 2 (by decide) (by decide)).trans a2))
  obtain ⟨f,tf,pf,f1,f8,f9,f18,f19,f20,f21,f22,f23,f2,ff,kf⟩ := SendRestore.contract B e final frame e2 h.stack h.stackAligned pe
  refine ⟨f,na+(12+UartWriteAll.time header hs)+(12+UartWriteAll.time body bs)+11+11,final,(by change na+(12+UartWriteAll.time header hs)+(12+UartWriteAll.time body bs)+11+11≤64+UartWriteAll.time header hs+UartWriteAll.time body bs;omega),?_,?_,
    SendFinishData.result_value _ _ _ _ _ (WordRegions.symm h.resultObject),SendFinishData.close_value _ _ _ _ _ (WordRegions.symm h.resultObject),
    SendFinishData.done_value _ _ _ _ _ (WordRegions.symm h.resultObject),?_,allFrame⟩
  · simpa only [body,header,List.nil_append,List.append_nil] using ((((ta.observed.trans tb).trans td).trans te.observed).trans tf.observed)
  · refine ⟨by rw [pf,saved.x1],f2.trans h.sp.symm,kf.trans (ke.trans (kd.trans (kb.trans (ka.trans q.csr)))),
      f1.trans saved.x1,f8.trans saved.x8,f9.trans saved.x9,f18.trans saved.x18,f19.trans saved.x19,
      f20.trans saved.x20,f21.trans saved.x21,f22.trans saved.x22,f23.trans saved.x23,?_,?_,?_,?_⟩
    all_goals
      first
      | exact (ff 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((fe 24 (by decide) (by decide) (by decide)).trans ((fd 24 (by decide) (by decide)).trans ((fb 24 (by decide) (by decide)).trans ((fa 24 (by decide) (by decide)).trans q.x24))))
      | exact (ff 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((fe 25 (by decide) (by decide) (by decide)).trans ((fd 25 (by decide) (by decide)).trans ((fb 25 (by decide) (by decide)).trans ((fa 25 (by decide) (by decide)).trans q.x25))))
      | exact (ff 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((fe 26 (by decide) (by decide) (by decide)).trans ((fd 26 (by decide) (by decide)).trans ((fb 26 (by decide) (by decide)).trans ((fa 26 (by decide) (by decide)).trans q.x26))))
      | exact (ff 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((fe 27 (by decide) (by decide) (by decide)).trans ((fd 27 (by decide) (by decide)).trans ((fb 27 (by decide) (by decide)).trans ((fa 27 (by decide) (by decide)).trans q.x27))))
  · apply ViewFrame.span q.headerBytes
    intro i
    apply allFrame _ (headerObj i)
    exact WordRegions.symm (WordRegions.shrink h.resultTx (by decide) (by change header.length≤1024;omega)) i
end E5R.Thermostat.SendTransfer
