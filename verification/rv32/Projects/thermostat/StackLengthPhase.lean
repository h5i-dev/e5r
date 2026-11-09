import Projects.thermostat.StackLengthReactive
import Projects.thermostat.StackLengthEnterRegs
import Projects.thermostat.StackHeaderToBodyRegs
import Projects.thermostat.StackEnvelope
import Projects.thermostat.LengthPhase
set_option autoImplicit false
namespace E5R.Thermostat.StackLengthPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec LengthPhase
abbrev B := StackBoard.board
abbrev classify := LengthPhase.classify
abbrev Envelope (I : Machine → State → Prop) (m : Machine) (g : State) :=
  StackEnvelope.Envelope (fun cut => I cut g) m

theorem next {c ram g} (h : At c ram g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ Envelope Cut ⟨d,ram⟩ next := by
  cases h with
  | @polling s served original head amount body eq parsed exactHead live caller =>
    subst g
    obtain ⟨d,reads,step,post,only,bank⟩ := StackLengthReactive.polling_next live o
    have finalCaller := HeaderPhase.preserve_caller caller bank (MainServeLayout.refl ram) (fun _ => rfl)
    have noInput : Observed.input reads=[] := by
      rcases only with nil|⟨v,single⟩
      · rw [nil];rfl
      · rw [single];rfl
    refine ⟨d,reads,⟨s,served,.length original head amount body⟩,step,?_,?_⟩
    · rw [noInput];exact ProtocolStreamTrace.refl _
    · rcases post with waiting|rbr
      · exact ⟨waiting.state.stable.masked,0,⟨d,ram⟩,.refl _,Or.inl (.polling rfl parsed exactHead waiting finalCaller)⟩
      · exact ⟨rbr.state.stable.masked,0,⟨d,ram⟩,.refl _,Or.inl (.rbr rfl parsed exactHead rbr finalCaller)⟩
  | @rbr s served original head amount body eq parsed exactHead live caller =>
    subst g
    let byte := (UartPoll.byte (o 0)).setWidth 8
    let first := c.wr 10 (UartPoll.byte (o 0)) 0x80000c78#32
    let bodyNext := body++[byte]
    have oldShort : body.length<amount := by
      have := live.short
      simp only [List.length_append,exactHead] at this
      omega
    have nextBound : bodyNext.length≤amount := by simp only [bodyNext,List.length_append,List.length_singleton];omega
    obtain ⟨step,post,bank⟩ := StackLengthReactive.rbr_next live o
    have continued := StackLengthReactive.after_rbr post
    change ∃ n e after,n≤21 ∧ Quiet.Steps B img n ⟨first,ram⟩ ⟨e,after⟩ ∧
      MainLengthState.Boundary e after ((original++body)++[byte]) s head amount ∧ e.sameCsr first ∧ e.get 25=BitVec.ofNat 32 (head.len+amount) ∧
      MainGprBank.Frame first e ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 at continued
    obtain ⟨n,e,after,bound,quiet,boundary,csr,total,bankLast,serve,low⟩ := continued
    have boundaryNext : MainLengthState.Boundary e after (original++bodyNext) s head amount := by simpa only [bodyNext,List.append_assoc] using boundary
    have firstCaller := HeaderPhase.preserve_caller caller bank (MainServeLayout.refl ram) (fun _ => rfl)
    have finalCaller := HeaderPhase.preserve_caller firstCaller bankLast serve low
    refine ⟨first,[⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩],classify s served original head amount bodyNext,step,?_,live.state.stable.masked,n,⟨e,after⟩,quiet,?_⟩
    · exact ProtocolStreamTrace.receive (receive_classify s served original body head amount byte oldShort)
    · by_cases full : bodyNext.length=amount
      · have notShort : ¬(original++bodyNext).length<head.len+amount := by simp only [List.length_append,exactHead,full];omega
        have complete : e.pc=0x80000c98#32 ∧ MainLengthState.At e after (original++bodyNext) s head amount := by
          simpa only [MainLengthState.Boundary,notShort,ite_false] using boundaryNext
        exact Or.inr ⟨s,served,original,head,amount,bodyNext,parsed,exactHead,full,complete.1,total,complete.2,finalCaller,by simp only [classify,LengthPhase.classify,full,ite_true]⟩
      · have short : (original++bodyNext).length<head.len+amount := by simp only [List.length_append,exactHead];omega
        have ready : MainLengthState.Ready e after (original++bodyNext) s head amount := by simpa only [MainLengthState.Boundary,short,ite_true] using boundaryNext
        exact Or.inl (.polling (by simp only [classify,LengthPhase.classify,full,ite_false]) parsed exactHead (LengthReactive.enter ready) finalCaller)

theorem safe {c ram g} (h : At c ram g) : ¬Escapes B img ⟨c,ram⟩ := by
  cases h with
  | polling _ _ _ live _ => exact StackLengthWait.safe ⟨live.waiting,live.state.stable.uart,live.state.stable.masked⟩
  | rbr _ _ _ live _ => exact StackLengthWait.exit_safe ⟨live.pc,live.state.stable.uart,live.state.stable.masked⟩


/-- The actual length-dispatch entry establishes the reactive phase or the
    zero-length complete-body cutpoint, from copied parser/layout facts. -/
theorem start {c ram s served original head amount} (h : MainHeaderToBody.Ready c ram original s head)
    (caller : HeaderPhase.Caller c ram served) (parsed : HttpRequestBytes.parse original 1024 1024=.done head)
    (exactHead : original.length=head.len) (kind : head.framing=.length amount) :
    Envelope Cut ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  obtain ⟨n,d,after,lo,hi,quiet,boundary,csr,total,bank,serve,low⟩ := StackLengthEnterRegs.contract_routes h amount kind
  have finalCaller := HeaderPhase.preserve_caller caller bank serve low
  have same : HeaderPhase.classify s served original=LengthPhase.classify s served original head amount [] := by
    unfold HeaderPhase.classify
    rw [parsed]
    dsimp only
    rw [kind]
    by_cases zero : amount=0
    · subst amount;rfl
    · simp only [zero,ite_false,LengthPhase.classify,List.length_nil,Ne.symm zero,LengthPhase.response]
  refine ⟨h.stable.masked,n,⟨d,after⟩,quiet,?_⟩
  rw [same]
  by_cases zero : amount=0
  · have notShort : ¬original.length<head.len+amount := by rw [exactHead,zero];omega
    have complete : d.pc=0x80000c98#32 ∧ MainLengthState.At d after original s head amount := by
      simpa only [MainLengthState.Boundary,notShort,ite_false] using boundary
    refine Or.inr ⟨s,served,original,head,amount,[],parsed,exactHead,by simpa only [List.length_nil] using zero.symm,
      complete.1,total,?_,finalCaller,?_⟩
    · simpa only [List.append_nil] using complete.2
    · simp only [LengthPhase.classify,List.length_nil,zero,ite_true]
  · have short : original.length<head.len+amount := by rw [exactHead];omega
    have ready : MainLengthState.Ready d after original s head amount := by simpa only [MainLengthState.Boundary,short,ite_true] using boundary
    refine Or.inl (At.polling (s := s) (body := []) (amount := amount) ?_ parsed exactHead ?_ finalCaller)
    · simp only [LengthPhase.classify,List.length_nil,Ne.symm zero,ite_false]
    · simpa only [List.append_nil] using LengthReactive.enter ready

/-- Real successful header return through actual copy/dispatch to the length
    phase. Exact consumed-head extent is derived from first-terminal history. -/
theorem from_header {c ram s served original head amount}
    (boundary : MainHeaderLoopTwo.Boundary c ram original s (.done head))
    (parsed : HttpRequestBytes.parse original 1024 1024=.done head)
    (earlier : ∀ k,k<original.length → HttpRequestBytes.parse (original.take k) 1024 1024=.incomplete)
    (caller : HeaderPhase.Caller c ram served) (kind : head.framing=.length amount) :
    Envelope Cut ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  have exactHead := (HeaderPhase.accepted_extent original head earlier parsed).symm
  obtain ⟨n,d,lo,hi,copy,ready,csr,bank,serve⟩ := StackHeaderToBodyRegs.contract boundary parsed
  have low := MainBodyHeadMemory.frame ram MainHeaderToBody.sp head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have finalCaller := HeaderPhase.preserve_caller caller bank serve (by simpa only [BitVec.add_zero] using low)
  obtain ⟨mask,rest,last,quiet,post⟩ := start ready finalCaller parsed exactHead kind
  exact ⟨boundary.2.1.masked,n+rest,last,copy.trans quiet,post⟩
end E5R.Thermostat.StackLengthPhase
