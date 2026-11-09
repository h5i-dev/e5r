import Projects.thermostat.LengthPhase
import Projects.thermostat.RequestPhase
import Projects.thermostat.LengthReceivedRequest
set_option autoImplicit false
namespace E5R.Thermostat.LengthCompletePhase
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Completed reactive length reception through real Next/counter/query/
    Request and actual matcher. The saved end register and all layouts are
    conclusions of the upstream length phase, not new interior assumptions. -/
theorem next {c ram g} (h : LengthPhase.Terminal c ram g) :
    ReactiveEnvelope.Envelope (fun m ghost => RequestPhase.At m.core m.ram ghost) ⟨c,ram⟩ g := by
  obtain ⟨s,served,first,head,amount,body,parsed,exactHead,bodyLength,pc,endReg,lengthReady,caller,ghost⟩ := h
  let input := first++body
  have readLength : input.length=head.len+amount := by simp only [input,List.length_append,exactHead,bodyLength]
  have staticE := caller.layout
  obtain ⟨f,next,readyNext,nextRegs,_⟩ := MainNextLength.contract lengthReady pc endReg (by
    rw [readLength];exact Nat.le_refl _)
  let rf := MainNextLengthMemory.memory ram sp head amount
  have capNext : ramRead rf (sp+16#32) .w=ramRead ram (sp+16#32) .w := by
    rw [MainNextLengthMemory.kept_word ram sp head amount 16 (by decide)]
    unfold MainNextLengthPrefix.stored MainNextLengthStores.memory
    rw [FrameOffsets.word _ sp _ 16 5172 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 5168 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 32 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 36 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 24 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 28 .w (by decide) (by decide) (by decide)]
  have staticF : InitRoutes.Layout rf := by
    refine ⟨MainRouterTable.preserve staticE.1 ?_,?_⟩
    · simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainNextLengthMemory.frame ram sp head amount 72 60 (by decide) (by decide)
    · exact capNext.trans staticE.2
  have bankF := MainGprBank.preserve nextRegs caller.bank
  have serveF : MainServeLayout.At rf served := by
    apply MainServeLayout.preserve (before := ram)
    · apply MainServeMemoryFrames.whole (size := 92)
      · simpa only [ViewFrame.Region,show sp+3204#32=MainServeLayout.fp by decide +kernel] using MainNextLengthMemory.frame ram sp head amount 3204 92 (by decide) (by decide)
      · decide
    · exact caller.serve
  have contained := MainHeadContained.bytes _ head parsed
  obtain ⟨g,stage,readyStage,_⟩ := MainServeNext.contract readyNext bankF serveF caller.room (MainNextLengthPayloadWords.contract ram sp head amount) ⟨contained.1,contained.2⟩
  let rg := MainServeNextMemory.memory rf sp
  have staticG : InitRoutes.Layout rg := InitRoutes.layout_preserve rf rg staticF
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainServeNextMemory.frame rf sp 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using MainServeNextMemory.frame rf sp 16 4 (by decide))
  obtain ⟨j,counter,readyCounter,_⟩ := MainRequestTarget.contract readyStage
  let rj := MainRequestCounter.memory rg sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 (head.len+amount))
  have staticJ : InitRoutes.Layout rj := InitRoutes.layout_preserve rg rj staticG
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainRequestCounterMemory.frame rg sp _ _ 72 60 (by decide) (Or.inl (by decide)))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using MainRequestCounterMemory.frame rg sp _ _ 16 4 (by decide) (Or.inl (by decide)))
  obtain ⟨qn,k,_,query,readyQuery,_⟩ := MainRequestQuery.contract readyCounter
  obtain ⟨mn,m,_,method,readyMethod,_⟩ := MainRequestMethod.contract readyQuery
  obtain ⟨d,build,ready,_⟩ := MainRequestBuild.contract readyMethod
    (MainRequestPayloadWords.counter rg sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 (head.len+amount)) (MainServeNextPayloadWords.stored rf sp))
  let after := MainRequestBuild.memory rj input head amount
  have frame (off size : Nat) (bound : off+size≤3312) : ViewFrame.Region rj after (sp+BitVec.ofNat 32 off) size :=
    MainRequestMemoryGlobalFrame.contract rj sp 0x80ffec14#32 head amount (MainRequestBuild.method input head)
      (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength input head)
      (MainRequestBuild.queryPtr input head) (MainRequestBuild.queryLength input head) off size (by omega) (Or.inl bound)
  have staticAfter : InitRoutes.Layout after := InitRoutes.layout_preserve rj after staticJ
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using frame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using frame 16 4 (by decide))
  have future : ViewFrame.Region rj after fp 96 := by
    simpa only [ViewFrame.Region,show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide)
  have headLimit : ramRead after (fp+76#32) .w=1024#32 := (ViewFrame.word future 76 (by decide)).trans readyMethod.stable.layout.head.headLimit
  have bodyLimit : ramRead after (fp+80#32) .w=1024#32 := (ViewFrame.word future 80 (by decide)).trans readyMethod.stable.layout.head.bodyLimit
  have metadata : LoopTransactionMemory.At after (BitVec.ofNat 32 (head.len+amount)) :=
    ⟨headLimit,bodyLimit,by have filled := ready.stable.filled;change ramRead after (fp+84#32) .w=BitVec.ofNat 32 input.length at filled;rw [readLength] at filled;exact filled,ready.usedWord,
      by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show head.len+amount<2^32 by have hb := ready.stable.bound;change input.length≤2048 at hb;rw [readLength] at hb;omega)];have hb := ready.stable.bound;change input.length≤2048 at hb;rw [readLength] at hb;exact hb,
      staticAfter.2,staticAfter.1⟩
  have header : input.take head.len=first := by
    change (first++body).take head.len=first
    rw [←exactHead]
    exact List.take_left
  have payload : RuntimeRequestSpans.body input head amount=body := by
    change ((first++body).drop head.len).take amount=body
    rw [←exactHead,List.drop_left,←bodyLength,List.take_length]
  obtain ⟨nr,last,final,route,post⟩ := RequestPhase.enter (RuntimeRequest.fromFixed ready) metadata header payload parsed
  have steps := (((((next.trans stage).trans counter).trans query).trans method).trans build).trans route
  refine ⟨lengthReady.stable.masked,407+755+17+qn+mn+460+nr,⟨last,final⟩,steps,?_⟩
  rw [ghost]
  exact post
end E5R.Thermostat.LengthCompletePhase
