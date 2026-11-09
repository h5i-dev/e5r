import Projects.thermostat.ChunkPhase
import Projects.thermostat.StackChunkReactive
import Projects.thermostat.StackHeaderToBodyRegs
import Projects.thermostat.StackEnvelope
set_option autoImplicit false
namespace E5R.Thermostat.StackChunkPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec ChunkPhase
abbrev B := StackBoard.board
abbrev Envelope (I : Machine → State → Prop) (m : Machine) (g : State) :=
  StackEnvelope.Envelope (fun cut => I cut g) m

/-- A pending exhausted chunk buffer with room reaches the actual LSR cut.
    Caller and dechunked-body/header views survive real descriptor stores. -/
theorem wait {c ram s served original head raw decoder body}
    (context : Context c ram s served original head)
    (live : MainChunkLoopInvariant.At UartPlatform.board c ram sp head.len raw (head.len+body.length) raw decoder)
    (payload : ChunkBufferView.Body ram sp head.len body) (room : raw<2048) :
    Envelope Cut ⟨c,ram⟩ ⟨s,served,.chunked original head raw decoder body⟩ := by
  obtain ⟨d,after,quiet,poll,rxFrame,frame⟩ := StackChunkReactive.setup live rfl room ChunkStackFrame.stack
  have headBound : head.len≤raw := by have := live.writtenRead;omega
  have header : ViewFrame.Region ram after rx head.len := by
    simpa only [show sp+132#32=rx by decide +kernel] using ViewFrame.shrink rxFrame headBound
  have finalContext := preserve context frame header
  have finalBody : ChunkBufferView.Body after sp head.len body := MainChunkStreaming.body_prefix payload live.writtenRead rxFrame
  exact ⟨live.masked,14,⟨d,after⟩,quiet,Or.inl (.polling rfl finalContext poll finalBody)⟩


theorem next {c ram g} (h : At c ram g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ Envelope Cut ⟨d,ram⟩ next := by
  cases h with
  | @polling s served original head raw decoder body eq context live payload =>
    subst g
    obtain ⟨d,reads,step,post,only,core,csr⟩ := StackChunkReactive.polling_next live o
    have frame : ChunkCallerFrame.At c d ram ram sp := ⟨core,(fun _ => rfl),(fun _ _ => rfl),(fun _ => rfl),(fun _ => rfl),csr⟩
    have finalContext := preserve context frame (fun _ => rfl)
    have noInput : Observed.input reads=[] := by
      rcases only with nil|⟨v,single⟩
      · rw [nil];rfl
      · rw [single];rfl
    refine ⟨d,reads,⟨s,served,.chunked original head raw decoder body⟩,step,?_,?_⟩
    · rw [noInput];exact ProtocolStreamTrace.refl _
    · rcases post with waiting|rbr
      · exact ⟨waiting.live.masked,0,⟨d,ram⟩,.refl _,Or.inl (.polling rfl finalContext waiting payload)⟩
      · exact ⟨rbr.live.masked,0,⟨d,ram⟩,.refl _,Or.inl (.rbr rfl finalContext rbr payload)⟩
  | @rbr s served original head raw decoder body eq context live payload =>
    subst g
    let byte := (UartPoll.byte (o 0)).setWidth 8
    let first := c.wr 11 (UartPoll.byte (o 0)) 0x80000e84#32
    let r := ChunkBufferSpec.consume (fun _ => byte) 1 raw (head.len+body.length) decoder body
    obtain ⟨step,post,core,csr⟩ := StackChunkReactive.rbr_next live o
    have firstFrame : ChunkCallerFrame.At c first ram ram sp := ⟨core,(fun _ => rfl),(fun _ _ => rfl),(fun _ => rfl),(fun _ => rfl),csr⟩
    have firstContext := preserve context firstFrame (fun _ => rfl)
    have continued := StackChunkReactive.consume_byte post ChunkStackFrame.stack payload rfl
    change ∃ n e after,n≤132 ∧ Quiet.Steps B img n ⟨first,ram⟩ ⟨e,after⟩ ∧
      MainChunkBuffered.Boundary UartPlatform.board e after sp head.len (raw+1) r ∧ ChunkBufferView.Body after sp head.len r.body ∧
      ViewFrame.Region ram after (sp+132#32) head.len ∧ e.get 24=BitVec.ofNat 32 r.read ∧
      ramRead after (sp+3288#32) .w=BitVec.ofNat 32 (raw+1) ∧ ChunkCallerFrame.At first e ram after sp at continued
    obtain ⟨n,e,after,bound,quiet,boundary,bodyAfter,header,cursor,filled,frame⟩ := continued
    have finalContext := preserve firstContext frame (by simpa only [show sp+132#32=rx by decide +kernel] using header)
    have readEq : r.read=raw+1 := by
      unfold r ChunkBufferSpec.consume
      cases step : chunkStep decoder byte.toNat 1024 with
      | mk state out => cases out <;> rfl
    have writeEq : r.written=head.len+r.body.length := ChunkBufferSpec.body_length (fun _ => byte) 1 raw (head.len+body.length) head.len decoder body rfl
    have inv : ChunkDecodedInvariant.Inv 1024 decoder body.length := by simpa only [Nat.add_sub_cancel_left] using live.live.decoder
    have bodyBound : r.body.length≤1024 := ChunkBufferSpec.decoded_length (fun _ => byte) 1 raw (head.len+body.length) decoder body inv
    have ordered : r.written≤r.read := ChunkSuccessBody.written_read (fun _ => byte) 1 raw (head.len+body.length) decoder body live.live.writtenRead
    have extent : head.len+r.body.length≤r.read := by rw [←writeEq];exact ordered
    have readBound : r.read≤2048 := by rw [readEq];have := live.room;omega
    have filledR : ramRead after (sp+3288#32) .w=BitVec.ofNat 32 r.read := by simpa only [readEq] using filled
    refine ⟨first,[⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩],ChunkPhase.classify s served original head r,step,?_,?_⟩
    · exact ProtocolStreamTrace.receive (receive_classify s served original body head raw decoder byte live.room)
    · cases stop : r.stop with
      | needInput =>
        have loop : MainChunkLoopInvariant.At UartPlatform.board e after sp head.len r.read (head.len+r.body.length) r.read r.state := by
          simpa only [MainChunkBuffered.Boundary,stop,writeEq,readEq] using boundary
        by_cases full : r.read=2048
        · refine ⟨live.live.masked,n,⟨e,after⟩,quiet,Or.inr (Or.inl ⟨s,served,original,head,r.state,r.body,finalContext,?_,bodyAfter,?_⟩)⟩
          · simpa only [full] using loop
          · simp only [ChunkPhase.classify,stop,ProtocolStreamSpec.chunkContinue,full,ite_true]
            rfl
        · have room : r.read<2048 := by omega
          obtain ⟨mask,rest,last,tail,ready⟩ := wait finalContext loop bodyAfter room
          refine ⟨live.live.masked,n+rest,last,quiet.trans tail,?_⟩
          have same : ChunkPhase.classify s served original head r=⟨s,served,.chunked original head r.read r.state r.body⟩ := by
            simp only [ChunkPhase.classify,stop,ProtocolStreamSpec.chunkContinue,full,ite_false]
          rw [same]
          exact ready
      | done =>
        have terminal : MainChunkBuffered.Terminal after sp head.len r e := by simpa only [MainChunkBuffered.Boundary,stop] using boundary
        exact ⟨live.live.masked,n,⟨e,after⟩,quiet,Or.inr (Or.inr ⟨s,served,original,head,r,finalContext,terminal,
          (by rw [stop];intro impossible;cases impossible),bodyAfter,writeEq,bodyBound,extent,readBound,cursor,filledR,rfl⟩)⟩
      | reject status =>
        have terminal : MainChunkBuffered.Terminal after sp head.len r e := by simpa only [MainChunkBuffered.Boundary,stop] using boundary
        exact ⟨live.live.masked,n,⟨e,after⟩,quiet,Or.inr (Or.inr ⟨s,served,original,head,r,finalContext,terminal,
          (by rw [stop];intro impossible;cases impossible),bodyAfter,writeEq,bodyBound,extent,readBound,cursor,filledR,rfl⟩)⟩

theorem safe {c ram g} (h : At c ram g) : ¬Escapes B img ⟨c,ram⟩ := by
  cases h with
  | polling _ _ live _ => exact StackChunkWait.safe ⟨live.waiting,live.live.uart,live.live.masked⟩
  | rbr _ _ live _ => exact StackChunkWait.exit_safe ⟨live.pc,live.live.uart,live.live.masked⟩
/-- First-terminal header history derives an empty encoded-body buffer;
    actual chunk initialization then enters the reactive UART phase. -/
theorem start {c ram s served original head} (h : MainHeaderToBody.Ready c ram original s head)
    (caller : HeaderPhase.Caller c ram served) (parsed : HttpRequestBytes.parse original 1024 1024=.done head)
    (exactHead : original.length=head.len) (kind : head.framing=.chunked) :
    Envelope Cut ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  have context : Context c ram s served original head := by
    refine ⟨caller,h.stable.app,h.stable.invariant,h.stable.stack,h.stable.fp,h.stable.uart,h.stable.one,h.two,
      h.stable.bytes,exactHead,parsed,kind,?_,?_,h.stable.layout.head.headLimit,h.stable.layout.head.bodyLimit⟩
    · simpa only [show fp+116#32=sp+3320#32 by decide +kernel] using h.view
    · simpa only [show fp+444#32=sp+3648#32 by decide +kernel] using h.consumed
  have chunkLayout : MainChunkLayout.At ram sp :=
    ⟨h.stable.layout.head.rx,h.stable.layout.capacity,h.stable.layout.head.config,h.stable.layout.head.bodyLimit,h.stable.layout.filledPtr⟩
  have stack : Memory.Block B sp 4928 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 4928) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have startPtr : c.get 23=sp+3680#32 := caller.bank.future
  have filled : ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 head.len := by
    simpa only [show sp+3288#32=fp+84#32 by decide +kernel,exactHead] using h.stable.layout.filled
  have room : head.len<2048 := by have := h.bounds.length.2;have := Nat.min_le_right original.length 1024;omega
  obtain ⟨d,after,init,loop,frame,header⟩ := ChunkCallerStart.contract B c ram sp head.len head.len
    (by simpa only [kind,MainBodyHeadDispatch.At] using h.cut) h.stable.sp h.stable.fp startPtr h.length h.stable.one
    h.stable.uart h.stable.masked stack (by decide) chunkLayout filled (Nat.le_refl _) (by omega)
  have originalStack : Memory.Block UartPlatform.board sp 4928 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 4928) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have loop := ChunkStackFrame.loop loop originalStack
  have finalContext := preserve context frame (ViewFrame.shrink header (by omega))
  have payload : ChunkBufferView.Body after sp head.len [] := fun i => Fin.elim0 i
  have pending : HeaderPhase.classify s served original=⟨s,served,.chunked original head head.len cStart []⟩ := by
    unfold HeaderPhase.classify
    rw [parsed]
    dsimp only
    rw [kind]
  obtain ⟨mask,n,last,quiet,post⟩ := wait finalContext loop payload room
  exact ⟨h.stable.masked,12+n,last,init.trans quiet,by rw [pending];exact post⟩

theorem from_header {c ram s served original head}
    (boundary : MainHeaderLoopTwo.Boundary c ram original s (.done head))
    (parsed : HttpRequestBytes.parse original 1024 1024=.done head)
    (earlier : ∀ k,k<original.length → HttpRequestBytes.parse (original.take k) 1024 1024=.incomplete)
    (caller : HeaderPhase.Caller c ram served) (kind : head.framing=.chunked) :
    Envelope Cut ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  have exactHead := (HeaderPhase.accepted_extent original head earlier parsed).symm
  obtain ⟨n,d,lo,hi,copy,ready,csr,bank,serve⟩ := StackHeaderToBodyRegs.contract boundary parsed
  have low := MainBodyHeadMemory.frame ram MainHeaderToBody.sp head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have finalCaller := HeaderPhase.preserve_caller caller bank serve (by simpa only [BitVec.add_zero] using low)
  obtain ⟨mask,rest,last,quiet,post⟩ := start ready finalCaller parsed exactHead kind
  exact ⟨boundary.2.1.masked,n+rest,last,copy.trans quiet,post⟩

end E5R.Thermostat.StackChunkPhase
