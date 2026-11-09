import Projects.thermostat.ReceivePhases
import Projects.thermostat.SendPhase
import Projects.thermostat.ReplyMetadata
import Projects.thermostat.MainCompletion
import Projects.thermostat.RuntimeResponseTail
import Projects.thermostat.MainResponseExtractedReply
set_option autoImplicit false
namespace E5R.Thermostat.NormalSendPhase
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual ordinary main Send entry and all recurrence facts. The persisted
    response state is committed; it need not equal the pending logical state
    during the real handler's sequential stores. -/
structure Ready (c : Core) (ram : Word → BitVec 8) (response : ApiWriteHttpSpec.Reply)
    (served : Nat) (used : Word) (json close headOnly : Bool) : Prop where
  input : SendInput.Pre c ram 0x80ffeb00#32 0x80fff878#32 0x80fffd38#32 0x80fff414#32 0x80ffffc7#32
    (MainResponseExtractedReply.pointer json) response.payload.length response.status response.mime response.payload close headOnly
  spWord : c.get 2=sp
  fpWord : c.get 8=fp
  uart : c.get 19=0x10000000#32
  one : c.get 22=1#32
  two : c.get 18=2#32
  minusTwo : c.get 24=0xfffffffe#32
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  returnAddress : c.get 1=0x80001784#32
  masked : c.mie_=false
  app : AppState.At ram response.state
  invariant : Spec.Inv response.state
  stack : Memory.Block B 0x80ff0000#32 65536
  serve : MainServeLayout.At ram served
  room : close=false → served<100
  metadata : LoopTransactionMemory.At ram used

def call {c ram response served used json close headOnly} (h : Ready c ram response served used json close headOnly) : SendPhase.Call :=
  ⟨c,ram,0x80ffeb00#32,0x80fff878#32,0x80fffd38#32,0x80fff414#32,0x80ffffc7#32,MainResponseExtractedReply.pointer json,
    response.payload.length,response.status,response.mime,response.payload,close,headOnly,h.input,h.masked⟩

def Pending (response : ApiWriteHttpSpec.Reply) (served : Nat) (close : Bool) (g : State) : Prop :=
  ∃ p,g.phase=.reply p ∧ p.response=response ∧ p.close=close ∧ p.nextCount=(if close then 0 else served)

def Active (m : Machine) (g : State) : Prop :=
  ∃ c ram response served used json close headOnly,∃ h : Ready c ram response served used json close headOnly,
    SendPhase.Active (call h) m g ∧ Pending response served close g

def Cut (m : Machine) (g : State) : Prop := Active m g ∨ ReceivePhases.Cut m g

/-- Actual ordinary Send RET through completion dispatch and keep/restart.
    Filled=used, layouts and counter bounds are upstream derived facts. -/
theorem finish {original before response served used json close headOnly c ram g}
    (h : Ready original before response served used json close headOnly)
    (returned : SendPhase.Returned (call h) ⟨c,ram⟩ g) (pending : Pending response served close g) :
    ∃ next,ProtocolStreamTrace.Trace g [] [] next ∧ ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ next := by
  obtain ⟨ret,result,closeWord,done,headerBytes,frame,queue⟩ := returned
  dsimp only [call] at ret result closeWord done headerBytes frame
  have pc : c.pc=0x80001784#32 := by rw [ret.pc,h.returnAddress];decide +kernel
  have object : Memory.Block B fp 1324 := by
    have block := Memory.sub_block h.stack (off := 63508) (m := 1324) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have tag : ramRead ram (fp+1316#32) .w=0xffffffff#32 := by
    simpa only [show fp+1316#32=0x80fffd38#32 by decide +kernel,BitVec.add_zero] using result
  have flag : ramRead ram (fp+1320#32) .w=ResponseHeadBodyMath.boolWord close := by
    simpa only [show fp+1320#32=0x80fffd38#32+4#32 by decide +kernel] using closeWord
  obtain ⟨e,complete,epc,e10,e21,regs,csr⟩ := MainCompletion.contract B c ram fp close
    (ret.x8.trans h.fpWord) (ret.x24.trans h.minusTwo) object (by decide) tag flag pc
  have region (ptr : Word) (len : Nat) (hs : WordRegions.Disjoint ptr len 0x80ffeb00#32 144)
      (ho : WordRegions.Disjoint ptr len 0x80fff878#32 89) (hr : WordRegions.Disjoint ptr len 0x80fffd38#32 8)
      (ht : WordRegions.Disjoint ptr len 0x80fff414#32 192) : ViewFrame.Region before ram ptr len :=
    fun i => frame _ (hs i) (ho i) (hr i) (ht i)
  have low : ViewFrame.Region before ram sp 132 := region sp 132
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have future : ViewFrame.Region before ram fp 96 := region fp 96
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have capFrame : ViewFrame.Region before ram 0x80ffeba0#32 4 := by
    simpa only [show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub low 16 4 (by decide)
  have routeFrame : ViewFrame.Region before ram 0x80ffebd8#32 60 := by
    simpa only [show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub low 72 60 (by decide)
  have app : AppState.At ram response.state := AppState.preserve before ram response.state h.app (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub low 44 25 (by decide))
  have memory := LoopTransactionMemory.preserve h.metadata future capFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink future (by decide))) h.serve
  have masked : c.mie_=false := (congrArg Prod.fst ret.csr).trans h.masked
  obtain ⟨n,d,after,bound,restart,ready⟩ := LoopReady.completed e ram response.state served used close epc
    ((regs 2 (by decide) (by decide)).trans (ret.sp.trans h.spWord))
    ((regs 8 (by decide) (by decide)).trans (ret.x8.trans h.fpWord))
    ((regs 19 (by decide) (by decide)).trans (ret.x19.trans h.uart))
    ((regs 22 (by decide) (by decide)).trans (ret.x22.trans h.one))
    ((regs 18 (by decide) (by decide)).trans (ret.x18.trans h.two)) ((congrArg Prod.fst csr).trans masked)
    h.stack app h.invariant ⟨e21,(regs 23 (by decide) (by decide)).trans (ret.x23.trans h.future),
      (regs 26 (by decide) (by decide)).trans (ret.x26.trans h.three)⟩ serve h.room memory.capacity memory.routes
    memory.headLimit memory.bodyLimit memory.filled memory.consumed memory.bound
  obtain ⟨p,phase,remaining⟩ := queue
  obtain ⟨q,phaseQ,responseEq,closeEq,nextCount⟩ := pending
  have same : q=p := Phase.reply.inj (phaseQ.symm.trans phase)
  subst q
  have nextState : (State.mk p.response.state p.nextCount (.head []))=⟨response.state,if close then 0 else served,.head []⟩ := by rw [responseEq,nextCount]
  refine ⟨⟨response.state,if close then 0 else served,.head []⟩,?_,masked,8+n,⟨d,after⟩,complete.trans restart,?_⟩
  · rw [←nextState]
    exact ProtocolStreamTrace.complete phase remaining
  · exact Or.inr (Or.inl (Or.inl (HeaderPhase.enter ready)))
theorem send_reply {a m g} (h : SendPhase.Cut a m g) : ∃ p,g.phase=.reply p := by
  rcases h with active|returned
  · cases active with
    | head _ _ _ uart | body _ _ _ _ _ _ uart =>
      cases uart.2.2.1 with
      | loading phase _ _ | polling phase _ _ | before phase _ _ | emitting phase _ _ | branch phase _ _ => exact ⟨_,phase⟩
  · obtain ⟨ret,result,close,done,bytes,frame,p,phase,empty⟩ := returned
    exact ⟨p,phase⟩

theorem boundary {original before response served used json close headOnly m g}
    (h : Ready original before response served used json close headOnly)
    (post : SendPhase.Cut (call h) m g) (pending : Pending response served close g) :
    ∃ next,ProtocolStreamTrace.Trace g [] [] next ∧ ReactiveEnvelope.Envelope Cut m next := by
  rcases post with active|returned
  · have masked : m.core.mie_=false := by
      cases active with
      | head _ _ _ uart | body _ _ _ _ _ _ uart => exact UartTxPhase.masked uart.2.2.1
    exact ⟨g,ProtocolStreamTrace.refl _,masked,0,m,.refl _,Or.inl ⟨original,before,response,served,used,json,close,headOnly,h,active,pending⟩⟩
  · exact finish h returned pending

theorem next {m g} (h : Active m g) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img m o=⟨.ok d m.ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧ ReactiveEnvelope.Envelope Cut ⟨d,m.ram⟩ next := by
  obtain ⟨original,before,response,served,used,json,close,headOnly,ready,active,pending⟩ := h
  obtain ⟨d,reads,evs,mid,step,trace,mask,n,last,quiet,post⟩ := SendPhase.next active o
  have noInput := SendPhase.no_input active o
  rw [step] at noInput
  have traceNoInput : ProtocolStreamTrace.Trace g [] (Observed.output evs) mid := by simpa only [noInput] using trace
  obtain ⟨p,phase⟩ := send_reply post
  obtain ⟨q,phaseQ,responseEq,closeEq,nextCount⟩ := pending
  obtain ⟨snapshotFrame,countFrame,responseFrame,closeFrame,nextFrame⟩ := ReplyMetadata.pending phaseQ phase traceNoInput
  have pendingNext : Pending response served close mid :=
    ⟨p,phase,responseFrame.trans responseEq,closeFrame.trans closeEq,nextFrame.trans nextCount⟩
  obtain ⟨next,tau,maskLast,k,final,tail,finalPost⟩ := boundary ready post pendingNext
  refine ⟨d,reads,evs,next,step,?_,mask,n+k,final,quiet.trans tail,finalPost⟩
  simpa only [List.append_nil] using ProtocolStreamTrace.trans trace tau

theorem safe {m g} (h : Active m g) : ¬Escapes B img m := by
  obtain ⟨original,before,response,served,used,json,close,headOnly,ready,active,pending⟩ := h
  exact SendPhase.safe active

/-- The caller supplies the concrete preparation and its independently
    established reply/close/head correspondence, rather than UART progress. -/
def Entry (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  ∃ response served used json close headOnly,∃ h : Ready c ram response served used json close headOnly,
    Pending response served close g ∧ ∃ p,g.phase=.reply p ∧ p.remaining=SendPhase.header (call h)++SendPhase.body (call h)

theorem start {c ram g} (h : Entry c ram g) :
    ∃ next,ProtocolStreamTrace.Trace g [] [] next ∧ ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ next := by
  obtain ⟨response,served,used,json,close,headOnly,ready,family,pending,phase,queue⟩ := h
  obtain ⟨mask,n,last,quiet,post⟩ := SendPhase.start (call ready) phase queue
  obtain ⟨next,tau,maskLast,k,final,tail,finalPost⟩ := boundary ready post family
  exact ⟨next,tau,mask,n+k,final,quiet.trans tail,finalPost⟩

end E5R.Thermostat.NormalSendPhase
