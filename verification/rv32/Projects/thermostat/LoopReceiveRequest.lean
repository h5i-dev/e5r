import Projects.thermostat.LoopReady
import Projects.thermostat.ApiConsume
import Projects.thermostat.MainRouterRequestFrames
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.LoopReceiveRequest
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- An arbitrary next API request from the reusable UART boundary to the real
    Request object, with actual counter increment and upstream static words.
    Parsing success is derived from the byte grammar, not a premise. -/
theorem contract (r : Fixed11) {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : LoopReady.At c ram s served) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (delivers : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 r.headBytes.length)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire r.headBytes.length r.body.length) :
    ∃ n d after, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs headerPlan 0 r.headBytes.length++MainLengthStreamPlan.logs bodyPlan r.headBytes.length r.body.length) [] ∧
      MainRequestBuild.Ready d after r.bytes s r.head r.body.length (served+1) ∧
      ramRead after 0x80ffeba0#32 .w=2048#32 ∧ MainRouterTable.At after ∧
      ramRead after (fp+76#32) .w=1024#32 ∧ ramRead after (fp+80#32) .w=1024#32 := by
  have exactHead := ApiConsume.exact_head r wire delivers
  have delivered := ApiConsume.delivered r wire delivers
  rw [exactHead] at delivered
  have headLen : r.head.len=r.headBytes.length := rfl
  simp only [headLen,Nat.add_sub_cancel_left] at delivered
  obtain ⟨hn,a,ra,_,header,boundary,_,bankA,serveA,lowA⟩ := MainHeaderStreamRegs.contract_routes wire headerPlan r.headBytes.length
    h.receive (by simp only [List.length_nil,Nat.zero_add];exact Nat.le_trans r.headBound (by decide)) headerValid
  rw [exactHead] at header boundary
  dsimp only at header boundary
  obtain ⟨bn,b,_,_,copy,bodyReady,_,bankB,serveB⟩ := MainHeaderToBodyRegs.contract boundary (ApiFixedHead.accepted r)
  let rb := MainBodyHeadMemory.memory ra sp r.head
  have protectedB : ViewFrame.Region ram rb sp 132 := HeadRegionFrame.trans lowA
    (MainBodyHeadMemory.frame ra sp r.head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide)))
  have staticB : InitRoutes.Layout rb := by
    apply InitRoutes.layout_preserve ram rb ⟨h.routes,h.capacity⟩
    · simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub protectedB 72 60 (by decide)
    · simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub protectedB 16 4 (by decide)
  obtain ⟨ln,e,re,_,lengthSteps,epc,lengthReady,_,e25,bankE,serveE,lowE⟩ := MainLengthBodyRegs.contract_routes bodyReady r.body.length rfl wire bodyPlan
    (by simpa only [headLen,Nat.add_sub_cancel_left] using bodyValid)
  simp only [headLen,Nat.add_sub_cancel_left] at lengthSteps lengthReady
  rw [delivered] at lengthReady
  have staticE : InitRoutes.Layout re := InitRoutes.layout_preserve rb re staticB
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub lowE 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub lowE 16 4 (by decide))
  obtain ⟨f,next,readyNext,nextRegs,_⟩ := MainNextLength.contract lengthReady epc e25 (by
    change r.head.len+r.body.length≤r.bytes.length
    rw [headLen];exact Nat.le_of_eq List.length_append.symm)
  let rf := MainNextLengthMemory.memory re sp r.head r.body.length
  have capNext : ramRead rf (sp+16#32) .w=ramRead re (sp+16#32) .w := by
    rw [MainNextLengthMemory.kept_word re sp r.head r.body.length 16 (by decide)]
    unfold MainNextLengthPrefix.stored MainNextLengthStores.memory
    rw [FrameOffsets.word _ sp _ 16 5172 .h (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 5168 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 32 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 36 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 24 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 16 28 .w (by decide) (by decide) (by decide)]
  have staticF : InitRoutes.Layout rf := by
    refine ⟨MainRouterTable.preserve staticE.1 ?_,?_⟩
    · simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainNextLengthMemory.frame re sp r.head r.body.length 72 60 (by decide) (by decide)
    · exact capNext.trans staticE.2
  have bankF := MainGprBank.preserve nextRegs (MainGprBank.preserve bankE (MainGprBank.preserve bankB (MainGprBank.preserve bankA h.bank)))
  have serveF : MainServeLayout.At rf served := by
    apply MainServeLayout.preserve (before := re)
    · apply MainServeMemoryFrames.whole (size := 92)
      · simpa only [ViewFrame.Region,show sp+3204#32=MainServeLayout.fp by decide +kernel] using MainNextLengthMemory.frame re sp r.head r.body.length 3204 92 (by decide) (by decide)
      · decide
    · exact MainServeLayout.preserve serveE (MainServeLayout.preserve serveB (MainServeLayout.preserve serveA h.serve))
  have parsed : HttpRequestBytes.parse r.headBytes 1024 1024=.done r.head := ApiFixedHead.accepted r
  have contained := MainHeadContained.bytes _ r.head parsed
  obtain ⟨g,stage,readyStage,_⟩ := MainServeNext.contract readyNext bankF serveF h.room (MainNextLengthPayloadWords.contract re sp r.head r.body.length) ⟨contained.1,contained.2⟩
  let rg := MainServeNextMemory.memory rf sp
  have staticG : InitRoutes.Layout rg := InitRoutes.layout_preserve rf rg staticF
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainServeNextMemory.frame rf sp 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using MainServeNextMemory.frame rf sp 16 4 (by decide))
  obtain ⟨j,counter,readyCounter,_⟩ := MainRequestTarget.contract readyStage
  let rj := MainRequestCounter.memory rg sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 (r.head.len+r.body.length))
  have staticJ : InitRoutes.Layout rj := InitRoutes.layout_preserve rg rj staticG
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using MainRequestCounterMemory.frame rg sp _ _ 72 60 (by decide) (Or.inl (by decide)))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using MainRequestCounterMemory.frame rg sp _ _ 16 4 (by decide) (Or.inl (by decide)))
  obtain ⟨qn,k,_,query,readyQuery,_⟩ := MainRequestQuery.contract readyCounter
  obtain ⟨mn,m,_,method,readyMethod,_⟩ := MainRequestMethod.contract readyQuery
  obtain ⟨d,build,ready,_⟩ := MainRequestBuild.contract readyMethod
    (MainRequestPayloadWords.counter rg sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 (r.head.len+r.body.length)) (MainServeNextPayloadWords.stored rf sp))
  let after := MainRequestBuild.memory rj r.bytes r.head r.body.length
  have frame (off size : Nat) (bound : off+size≤3312) : ViewFrame.Region rj after (sp+BitVec.ofNat 32 off) size :=
    MainRequestMemoryGlobalFrame.contract rj sp 0x80ffec14#32 r.head r.body.length (MainRequestBuild.method r.bytes r.head)
      (0x80ffec14#32+BitVec.ofNat 32 r.head.target.1) (MainRequestBuild.pathLength r.bytes r.head)
      (MainRequestBuild.queryPtr r.bytes r.head) (MainRequestBuild.queryLength r.bytes r.head) off size (by omega) (Or.inl bound)
  have staticAfter : InitRoutes.Layout after := InitRoutes.layout_preserve rj after staticJ
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using frame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using frame 16 4 (by decide))
  have future : ViewFrame.Region rj after fp 96 := by
    simpa only [ViewFrame.Region,show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide)
  refine ⟨hn+bn+ln+407+755+17+qn+mn+460,d,after,?_,ready,staticAfter.2,staticAfter.1,?_,?_⟩
  · have prefixRun := ((header.trans copy.observed).trans lengthSteps).trans
      (((((next.trans stage).trans counter).trans query).trans method).trans build).observed
    simpa only [after,rj,rg,rf,List.append_nil,List.nil_append,List.length_nil,headLen,Nat.add_sub_cancel_left,Nat.add_assoc] using prefixRun
  · exact (ViewFrame.word future 76 (by decide)).trans readyMethod.stable.layout.head.headLimit
  · exact (ViewFrame.word future 80 (by decide)).trans readyMethod.stable.layout.head.bodyLimit
end E5R.Thermostat.LoopReceiveRequest
