import Projects.thermostat.HeadReceiveEntry
import Projects.thermostat.RuntimeRequestSpans
import Projects.thermostat.LoopTransactionMemory
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.LengthReceivedRequest
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Generic accepted Content-Length reception to actual Request construction.
    Paths/methods/header policies are arbitrary accepted parser bytes, without
    the narrower Fixed11 grammar. All caller layout and used=filled follow. -/
theorem contract {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (amount : Nat)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (space : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (framing : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire head.len amount) :
    let first := (consume wire fuel []).input
    let input := first++arrivals wire head.len amount
    ∃ n d after,Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan head.len amount) [] ∧
      RuntimeRequest.Ready d after input s head amount (head.len+amount) (served+1) ∧
      input.take head.len=first ∧ RuntimeRequestSpans.body input head amount=arrivals wire head.len amount ∧
      InitRoutes.Layout after ∧ LoopTransactionMemory.At after (BitVec.ofNat 32 (head.len+amount)) := by
  dsimp only
  let first := (consume wire fuel []).input
  let input := first++arrivals wire head.len amount
  obtain ⟨hn,b,rb,header,bodyReady,headLen,bankB,serveB,staticB,original,bounds,csr⟩ := HeadReceiveEntry.contract h wire fuel head headerPlan space headerValid accepted
  have readLength : input.length=head.len+amount := by
    simp only [input,first,List.length_append,arrivals,List.length_map,List.length_range,headLen]
  obtain ⟨ln,e,re,_,lengthSteps,epc,lengthReady,_,e25,bankE,serveE,lowE⟩ := MainLengthBodyRegs.contract_routes bodyReady amount framing wire bodyPlan
    (by simpa only [headLen,Nat.add_sub_cancel_left] using bodyValid)
  simp only [headLen,Nat.add_sub_cancel_left] at lengthSteps lengthReady
  have staticE : InitRoutes.Layout re := InitRoutes.layout_preserve rb re staticB
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub lowE 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub lowE 16 4 (by decide))
  obtain ⟨f,next,readyNext,nextRegs,_⟩ := MainNextLength.contract lengthReady epc e25 (by
    rw [readLength];exact Nat.le_refl _)
  let rf := MainNextLengthMemory.memory re sp head amount
  have capNext : ramRead rf (sp+16#32) .w=ramRead re (sp+16#32) .w := by
    rw [MainNextLengthMemory.kept_word re sp head amount 16 (by decide)]
    unfold MainNextLengthPrefix.stored MainNextLengthStores.memory
    rw [FrameOffsets.word _ sp _ 16 5172 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 5168 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 32 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 36 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 24 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 28 .w (by decide) (by decide) (by decide)]
  have staticF : InitRoutes.Layout rf := by
    refine ⟨MainRouterTable.preserve staticE.1 ?_,?_⟩
    · simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainNextLengthMemory.frame re sp head amount 72 60 (by decide) (by decide)
    · exact capNext.trans staticE.2
  have bankF := MainGprBank.preserve nextRegs (MainGprBank.preserve bankE bankB)
  have serveF : MainServeLayout.At rf served := by
    apply MainServeLayout.preserve (before := re)
    · apply MainServeMemoryFrames.whole (size := 92)
      · simpa only [ViewFrame.Region,show sp+3204#32=MainServeLayout.fp by decide +kernel] using MainNextLengthMemory.frame re sp head amount 3204 92 (by decide) (by decide)
      · decide
    · exact MainServeLayout.preserve serveE serveB
  have parsed : HttpRequestBytes.parse first 1024 1024=.done head := by
    rw [←MainHeaderStreamSpec.exact_result wire fuel [] (by decide +kernel)];exact accepted
  have contained := MainHeadContained.bytes _ head parsed
  obtain ⟨g,stage,readyStage,_⟩ := MainServeNext.contract readyNext bankF serveF h.room (MainNextLengthPayloadWords.contract re sp head amount) ⟨contained.1,contained.2⟩
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
  refine ⟨hn+ln+407+755+17+qn+mn+460,d,after,?_,RuntimeRequest.fromFixed ready,?_,?_,staticAfter,metadata⟩
  · have prefixRun := (header.trans lengthSteps).trans
      (((((next.trans stage).trans counter).trans query).trans method).trans build).observed
    simpa only [after,rj,rg,rf,List.append_nil,List.nil_append,List.length_nil,headLen,Nat.add_sub_cancel_left,Nat.add_assoc] using prefixRun
  · change (first++arrivals wire head.len amount).take head.len=first
    rw [←headLen];exact List.take_left
  · change ((first++arrivals wire head.len amount).drop head.len).take amount=arrivals wire head.len amount
    rw [←headLen,List.drop_left]
    exact List.take_of_length_le (by simp only [arrivals,List.length_map,List.length_range,Nat.le_refl])
end E5R.Thermostat.LengthReceivedRequest
