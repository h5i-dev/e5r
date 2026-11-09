import Projects.thermostat.ChunkReactive
import Projects.thermostat.HeaderPhase
import Projects.thermostat.ChunkCallerPreserve
import Projects.thermostat.ChunkSuccessBody
set_option autoImplicit false
namespace E5R.Thermostat.ChunkPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32
abbrev rx := 0x80ffec14#32

/-- Persistent caller data is independent of encoded body bytes that actual
    in-place decoding overwrites. Filled/read/write/decoder live elsewhere. -/
structure Context (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served : Nat) (original : List (BitVec 8)) (head : Head) : Prop where
  caller : HeaderPhase.Caller c ram served
  app : AppState.At ram s
  invariant : Spec.Inv s
  stack : Memory.Block B 0x80ff0000#32 65536
  frame : c.get 8=fp
  uart : c.get 19=0x10000000#32
  one : c.get 22=1#32
  two : c.get 18=2#32
  header : Bytes.At ram rx original
  length : original.length=head.len
  parsed : HttpRequestBytes.parse original 1024 1024=.done head
  kind : head.framing=.chunked
  view : HeadCompletedView.At ram (sp+3320#32) head
  consumed : ramRead ram (sp+3648#32) .w=BitVec.ofNat 32 head.len
  headLimit : ramRead ram (fp+76#32) .w=1024#32
  bodyLimit : ramRead ram (fp+80#32) .w=1024#32

theorem preserve {c d before after s served original head} (h : Context c before s served original head)
    (frame : ChunkCallerFrame.At c d before after sp) (header : ViewFrame.Region before after rx head.len) :
    Context d after s served original head := by
  obtain ⟨app,bank,serve,capacity,routes⟩ := ChunkCallerPreserve.contract frame h.app h.caller.bank h.caller.serve h.caller.layout.2 h.caller.layout.1
  have copied : ViewFrame.Region before after (sp+3320#32) 304 := by
    simpa only [BitVec.add_assoc,show 3292#32+28#32=3320#32 by decide +kernel] using HeadRegionFrame.sub frame.futureHigh 28 304 (by decide)
  refine ⟨⟨bank,serve,h.caller.room,routes,capacity⟩,app,h.invariant,h.stack,
    (frame.core 8 (by decide)).trans h.frame,(frame.core 19 (by decide)).trans h.uart,
    (frame.core 22 (by decide)).trans h.one,(frame.core 18 (by decide)).trans h.two,
    ?_,h.length,h.parsed,h.kind,MainCopyView.head copied head h.view,?_,?_,?_⟩
  · intro i
    exact (header ⟨i.val,by have := i.isLt;have := h.length;omega⟩).trans (h.header i)
  · have word := ViewFrame.word frame.futureHigh 356 (by decide)
    simpa only [BitVec.add_assoc,show 3292#32+356#32=3648#32 by decide +kernel] using word.trans h.consumed
  · have word := ViewFrame.word frame.futureLow 76 (by decide)
    simpa only [show sp+3204#32=fp by decide +kernel] using word.trans h.headLimit
  · have word := ViewFrame.word frame.futureLow 80 (by decide)
    simpa only [show sp+3204#32=fp by decide +kernel] using word.trans h.bodyLimit

def response (s : Spec.Snapshot) (served : Nat) (original body : List (BitVec 8)) (head : Head) :=
  ProtocolStreamSpec.dispatch ⟨s,served,.head original⟩ original body head

def error (s : Spec.Snapshot) (served status : Nat) := ProtocolStreamSpec.reject ⟨s,served,.head []⟩ status

def classify (s : Spec.Snapshot) (served : Nat) (original : List (BitVec 8)) (head : Head) (r : ChunkBufferSpec.Result) : State :=
  match r.stop with
  | .needInput => ProtocolStreamSpec.chunkContinue ⟨s,served,.head original⟩ original head r.read r.state r.body
  | .done => response s served original r.body head
  | .reject status => error s served status

theorem receive_classify (s : Spec.Snapshot) (served : Nat) (original body : List (BitVec 8)) (head : Head)
    (raw : Nat) (decoder : CState) (byte : BitVec 8) (room : raw<2048) :
    ProtocolStreamSpec.receive ⟨s,served,.chunked original head raw decoder body⟩ byte=
      some (classify s served original head (ChunkBufferSpec.consume (fun _ => byte) 1 raw (head.len+body.length) decoder body)) := by
  simp only [ProtocolStreamSpec.receive,room,ite_true,ChunkBufferSpec.consume]
  cases step : chunkStep decoder byte.toNat 1024 with
  | mk next out => cases out <;> rfl


inductive At (c : Core) (ram : Word → BitVec 8) (g : State) : Prop where
  | polling {s served original head raw decoder body} : g=⟨s,served,.chunked original head raw decoder body⟩ →
      Context c ram s served original head →
      ChunkReactive.Polling c ram sp head.len raw (head.len+body.length) raw decoder →
      ChunkBufferView.Body ram sp head.len body → At c ram g
  | rbr {s served original head raw decoder body} : g=⟨s,served,.chunked original head raw decoder body⟩ →
      Context c ram s served original head →
      ChunkReactive.Rbr c ram sp head.len raw (head.len+body.length) raw decoder →
      ChunkBufferView.Body ram sp head.len body → At c ram g

def Capacity (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  ∃ s served original head decoder body,Context c ram s served original head ∧
    MainChunkLoopInvariant.At B c ram sp head.len 2048 (head.len+body.length) 2048 decoder ∧
    ChunkBufferView.Body ram sp head.len body ∧ g=error s served 413

def Terminal (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  ∃ s served original head r,Context c ram s served original head ∧ MainChunkBuffered.Terminal ram sp head.len r c ∧
    r.stop≠.needInput ∧ ChunkBufferView.Body ram sp head.len r.body ∧ r.written=head.len+r.body.length ∧
    r.body.length≤1024 ∧ head.len+r.body.length≤r.read ∧ r.read≤2048 ∧ c.get 24=BitVec.ofNat 32 r.read ∧
    ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 r.read ∧ g=classify s served original head r

def Cut (m : Machine) (g : State) := At m.core m.ram g ∨ Capacity m.core m.ram g ∨ Terminal m.core m.ram g

/-- A pending exhausted chunk buffer with room reaches the actual LSR cut.
    Caller and dechunked-body/header views survive real descriptor stores. -/
theorem wait {c ram s served original head raw decoder body}
    (context : Context c ram s served original head)
    (live : MainChunkLoopInvariant.At B c ram sp head.len raw (head.len+body.length) raw decoder)
    (payload : ChunkBufferView.Body ram sp head.len body) (room : raw<2048) :
    ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ ⟨s,served,.chunked original head raw decoder body⟩ := by
  obtain ⟨d,after,quiet,poll,rxFrame,frame⟩ := ChunkReactive.setup live rfl room
  have headBound : head.len≤raw := by have := live.writtenRead;omega
  have header : ViewFrame.Region ram after rx head.len := by
    simpa only [show sp+132#32=rx by decide +kernel] using ViewFrame.shrink rxFrame headBound
  have finalContext := preserve context frame header
  have finalBody : ChunkBufferView.Body after sp head.len body := MainChunkStreaming.body_prefix payload live.writtenRead rxFrame
  exact ⟨live.masked,14,⟨d,after⟩,quiet,Or.inl (.polling rfl finalContext poll finalBody)⟩


theorem next {c ram g} (h : At c ram g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ ReactiveEnvelope.Envelope Cut ⟨d,ram⟩ next := by
  cases h with
  | @polling s served original head raw decoder body eq context live payload =>
    subst g
    obtain ⟨d,reads,step,post,only,core,csr⟩ := ChunkReactive.polling_next live o
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
    obtain ⟨step,post,core,csr⟩ := ChunkReactive.rbr_next live o
    have firstFrame : ChunkCallerFrame.At c first ram ram sp := ⟨core,(fun _ => rfl),(fun _ _ => rfl),(fun _ => rfl),(fun _ => rfl),csr⟩
    have firstContext := preserve context firstFrame (fun _ => rfl)
    have continued := ChunkReactive.consume_byte post payload rfl
    change ∃ n e after,n≤132 ∧ Quiet.Steps B img n ⟨first,ram⟩ ⟨e,after⟩ ∧
      MainChunkBuffered.Boundary B e after sp head.len (raw+1) r ∧ ChunkBufferView.Body after sp head.len r.body ∧
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
    refine ⟨first,[⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩],classify s served original head r,step,?_,?_⟩
    · exact ProtocolStreamTrace.receive (receive_classify s served original body head raw decoder byte live.room)
    · cases stop : r.stop with
      | needInput =>
        have loop : MainChunkLoopInvariant.At B e after sp head.len r.read (head.len+r.body.length) r.read r.state := by
          simpa only [MainChunkBuffered.Boundary,stop,writeEq,readEq] using boundary
        by_cases full : r.read=2048
        · refine ⟨live.live.masked,n,⟨e,after⟩,quiet,Or.inr (Or.inl ⟨s,served,original,head,r.state,r.body,finalContext,?_,bodyAfter,?_⟩)⟩
          · simpa only [full] using loop
          · simp only [classify,stop,ProtocolStreamSpec.chunkContinue,full,ite_true]
            rfl
        · have room : r.read<2048 := by omega
          obtain ⟨mask,rest,last,tail,ready⟩ := wait finalContext loop bodyAfter room
          refine ⟨live.live.masked,n+rest,last,quiet.trans tail,?_⟩
          have same : classify s served original head r=⟨s,served,.chunked original head r.read r.state r.body⟩ := by
            simp only [classify,stop,ProtocolStreamSpec.chunkContinue,full,ite_false]
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
  | polling _ _ live _ => exact MainChunkWaitSafety.safe ⟨live.waiting,live.live.uart,live.live.masked⟩
  | rbr _ _ live _ => exact MainChunkWaitSafety.exit_safe ⟨live.pc,live.live.uart,live.live.masked⟩
/-- First-terminal header history derives an empty encoded-body buffer;
    actual chunk initialization then enters the reactive UART phase. -/
theorem start {c ram s served original head} (h : MainHeaderToBody.Ready c ram original s head)
    (caller : HeaderPhase.Caller c ram served) (parsed : HttpRequestBytes.parse original 1024 1024=.done head)
    (exactHead : original.length=head.len) (kind : head.framing=.chunked) :
    ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  have context : Context c ram s served original head := by
    refine ⟨caller,h.stable.app,h.stable.invariant,h.stable.stack,h.stable.fp,h.stable.uart,h.stable.one,h.two,
      h.stable.bytes,exactHead,parsed,kind,?_,?_,h.stable.layout.head.headLimit,h.stable.layout.head.bodyLimit⟩
    · simpa only [show fp+116#32=sp+3320#32 by decide +kernel] using h.view
    · simpa only [show fp+444#32=sp+3648#32 by decide +kernel] using h.consumed
  have chunkLayout : MainChunkLayout.At ram sp :=
    ⟨h.stable.layout.head.rx,h.stable.layout.capacity,h.stable.layout.head.config,h.stable.layout.head.bodyLimit,h.stable.layout.filledPtr⟩
  have stack : Memory.Block B sp 4928 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 4928) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have startPtr : c.get 23=sp+3680#32 := caller.bank.future
  have filled : ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 head.len := by
    simpa only [show sp+3288#32=fp+84#32 by decide +kernel,exactHead] using h.stable.layout.filled
  have room : head.len<2048 := by have := h.bounds.length.2;have := Nat.min_le_right original.length 1024;omega
  obtain ⟨d,after,init,loop,frame,header⟩ := ChunkCallerStart.contract B c ram sp head.len head.len
    (by simpa only [kind,MainBodyHeadDispatch.At] using h.cut) h.stable.sp h.stable.fp startPtr h.length h.stable.one
    h.stable.uart h.stable.masked stack (by decide) chunkLayout filled (Nat.le_refl _) (by omega)
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
    ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  have exactHead := (HeaderPhase.accepted_extent original head earlier parsed).symm
  obtain ⟨n,d,lo,hi,copy,ready,csr,bank,serve⟩ := MainHeaderToBodyRegs.contract boundary parsed
  have low := MainBodyHeadMemory.frame ram MainHeaderToBody.sp head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have finalCaller := HeaderPhase.preserve_caller caller bank serve (by simpa only [BitVec.add_zero] using low)
  obtain ⟨mask,rest,last,quiet,post⟩ := start ready finalCaller parsed exactHead kind
  exact ⟨boundary.2.1.masked,n+rest,last,copy.trans quiet,post⟩

end E5R.Thermostat.ChunkPhase
