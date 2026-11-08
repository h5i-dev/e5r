import Projects.thermostat.MainStateMatchReset
import Projects.thermostat.MainReadDecoded
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainReadReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
abbrev sp := MainRouterEntry.sp

/-- The response capacity is stored by actual main route-future construction. -/
theorem reply_capacity (ram : Word → BitVec 8) :
    ramRead (MainRouterSetup.memory ram) 0x80fff9fc#32 .w=832#32 := by
  change ramRead (MainRouterSetup.memory ram) (sp+3692#32) .w=832#32
  unfold MainRouterSetup.memory
  rw [FrameOffsets.word _ sp _ 3692 3936 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3924 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3920 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3916 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3908 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3904 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3900 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3896 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3892 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3912 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3888 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3884 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3880 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3864 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3860 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3856 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3852 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3848 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3868 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3844 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3840 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3836 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3832 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3828 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3820 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3816 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3812 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3808 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3804 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3824 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3800 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3796 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3792 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3788 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3784 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3776 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3772 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3768 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3764 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3760 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3780 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3756 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3752 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3748 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3744 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3740 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3736 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3732 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3728 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3724 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3720 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3716 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3712 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3708 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3704 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3700 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3692 3696 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

/-- One actual GET /state request from reset to exact HTTP/UART completion.
    Pure accepted-head/framing/readiness remain upstream obligations; this
    theorem derives every real routing, decoder and Read-handler layout. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head) (amount : Nat)
    (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length))
    (route : MainRequestSpans.path ((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token ((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) head.method.2)=.get)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close).length)
    (hbs : bs.length=(ReplyJson.snapshot Spec.initial).length) :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let bytes := input++arrivals wire input.length missing
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after close,
      n≤11902+18*(MainRequestSpans.body bytes head amount).length+(77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+
        MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing+
        UartWriteAll.time (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close) (hs close)+
        UartWriteAll.time (ReplyJson.snapshot Spec.initial) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (reads++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close)++
          UartTxLoop.events (ReplyJson.snapshot Spec.initial)) ∧
      Observed.input (reads++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))=bytes ∧
      close=MainCloseSpec.mustClose head.minor 1 (MainRequestSpans.raw bytes head amount) (MainRequestInputs.entries head) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.mie_=false ∧
      AppState.At after Spec.initial ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  obtain ⟨first,a,mid,close,bound,trace,ready,bytes,routes⟩ := MainCloseRequestReset.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨b,entry,entered,_⟩ := MainRouterEntry.contract ready routes
  obtain ⟨e,matched,matchReady,_⟩ := MainStateMatch.contract entered route
  have capacity : ramRead (MainPathStateSave.memory (MainRouterSetup.memory mid) b) 0x80fff9fc#32 .w=832#32 := by
    have region : ViewFrame.Region (MainRouterSetup.memory mid) (MainPathStateSave.memory (MainRouterSetup.memory mid) b) 0x80fff9fc#32 4 := by
      intro i
      rw [MainPathStateSave.memory_eq]
      apply OuterSave.frame
      intro j
      exact Ne.symm (WordZero.separated 0x80ffeb30#32 0x80fff9fc#32 96 4 (by decide +kernel) (by decide +kernel) j i)
    have word := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at word
    exact word.trans (reply_capacity mid)
  obtain ⟨f,future,routeReady,_⟩ := MainReadRouteInput.contract matchReady route method capacity
  obtain ⟨g,decodeCount,decodedRam,decodeBound,decoded,readReady,_⟩ := MainReadDecoded.contract routeReady
  have body : ResponseHeadSpec.body 200 (MainMethod.head (decodedRam 0x80fff9f4#32)) (ReplyJson.snapshot Spec.initial)=ReplyJson.snapshot Spec.initial := by
    rw [readReady.method]
    rfl
  obtain ⟨d,last,after,lastBound,sent,pc,sp,fp,csr,app,inv,_⟩ := ReadRound.contract_exact g decodedRam Spec.initial close readReady.acquiredInput
    readReady.stable.invariant readReady.stable.app readReady.stable.stack readReady.payload readReady.capacity readReady.stable.one readReady.replyCapacity
    readReady.serve.tx readReady.serve.txCapacity readReady.closeByte (hs close) bs (hhs close) (by rw [body];exact hbs)
  rw [body] at lastBound sent
  have receivedPath := trace.trans (entry.trans (matched.trans (future.trans decoded))).observed
  have allSteps := receivedPath.trans sent
  have inputOnly : Observed.input ((MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan (consume wire fuel []).input.length (head.len+amount-(consume wire fuel []).input.length))++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))=
      (consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length (head.len+amount-(consume wire fuel []).input.length) := by
    simp only [Observed.input_append,UartTxLoop.no_input,List.append_nil]
    simpa only [Observed.input_append] using bytes
  refine ⟨first+83+187+28+decodeCount+last,d,after,close,by omega,?_,inputOnly,matchReady.closeSpec,pc,sp,fp,?_,app,inv⟩
  · simpa only [List.append_nil,List.nil_append,Nat.add_assoc] using allSteps
  · exact (congrArg Prod.fst csr).trans readReady.stable.masked
end E5R.Thermostat.MainReadReset
