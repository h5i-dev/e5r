import Projects.thermostat.RefusalPhase
import Projects.thermostat.ReceivePhases
import Projects.thermostat.SendPhase
import Projects.thermostat.ReplyMetadata
set_option autoImplicit false
namespace E5R.Thermostat.RefusalSendPhase
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

def call {c ram s served status} (h : RefusalPhase.Ready c ram s served status) : SendPhase.Call :=
  ⟨c,ram,0x80ffeb00#32,0x80fff878#32,0x80fffd38#32,0x80fff414#32,0x80ffffc7#32,1#32,
    0,status,[],[],true,false,h.input,h.masked⟩

def Pending (s : Spec.Snapshot) (served status : Nat) (g : State) : Prop :=
  g.snapshot=s ∧ g.served=served ∧ ∃ p,g.phase=.reply p ∧ p.response=⟨s,status,[],[]⟩ ∧ p.close=true ∧ p.nextCount=0

def Active (m : Machine) (g : State) : Prop :=
  ∃ c ram s served status,∃ h : RefusalPhase.Ready c ram s served status,SendPhase.Active (call h) m g ∧ Pending s served status g

def Cut (m : Machine) (g : State) : Prop := Active m g ∨ ReceivePhases.Cut m g

/-- The real rejected Send return, success branch and outer restart reach
    the reusable RX boundary; only then is the reply committed in the stream. -/
theorem finish {original before s served status c ram g} (h : RefusalPhase.Ready original before s served status)
    (returned : SendPhase.Returned (call h) ⟨c,ram⟩ g) (pending : Pending s served status g) :
    ∃ next,ProtocolStreamTrace.Trace g [] [] next ∧ ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ next := by
  obtain ⟨ret,result,closeWord,done,headerBytes,frame,queue⟩ := returned
  dsimp only [call] at ret result closeWord done headerBytes frame
  have pc : c.pc=0x80001c0a#32 := by rw [ret.pc,h.returnAddress];decide +kernel
  have object : Memory.Block B fp 1320 := by
    have block := Memory.sub_block h.stack (off := 63508) (m := 1320) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have tag : ramRead ram (fp+1316#32) .w=0xffffffff#32 := by
    simpa only [call,show fp+1316#32=0x80fffd38#32 by decide +kernel,BitVec.add_zero] using result
  obtain ⟨e,complete,epc,e10,e20,regs,csr⟩ := RejectResponseComplete.contract B c ram (ret.x8.trans h.fpWord)
    (ret.x21.trans h.caller.bank.minusOne) (ret.x24.trans h.minusTwo) tag object pc
  have low : ViewFrame.Region before ram sp 132 := by
    intro i
    exact frame _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
  have app : AppState.At ram s := AppState.preserve before ram s h.app (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub low 44 25 (by decide))
  have static : InitRoutes.Layout ram := InitRoutes.layout_preserve before ram h.caller.layout
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub low 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub low 16 4 (by decide))
  have bank : MainGprBank.At e :=
    ⟨(regs 21 (by decide) (by decide)).trans (ret.x21.trans h.caller.bank.minusOne),
      (regs 23 (by decide) (by decide)).trans (ret.x23.trans h.caller.bank.future),
      (regs 26 (by decide) (by decide)).trans (ret.x26.trans h.caller.bank.three)⟩
  have masked : c.mie_=false := (congrArg Prod.fst ret.csr).trans h.masked
  obtain ⟨d,after,restart,ready,serve,capacityFrame,routeFrame,bankFrame⟩ := LoopClose.contract e ram s epc
    ((regs 2 (by decide) (by decide)).trans (ret.sp.trans h.spWord))
    ((regs 8 (by decide) (by decide)).trans (ret.x8.trans h.fpWord))
    ((regs 19 (by decide) (by decide)).trans (ret.x19.trans h.uart))
    ((regs 22 (by decide) (by decide)).trans (ret.x22.trans h.one))
    ((regs 18 (by decide) (by decide)).trans (ret.x18.trans h.two)) ((congrArg Prod.fst csr).trans masked)
    h.stack app h.invariant static.2
  have final : LoopReady.At d after s 0 :=
    ⟨ready,MainGprBank.preserve bankFrame bank,serve,by decide,
      by simpa only [BitVec.add_zero] using (ViewFrame.word capacityFrame 0 (by decide)).trans static.2,
      MainRouterTable.preserve static.1 routeFrame⟩
  obtain ⟨p,phase,remaining⟩ := queue
  obtain ⟨snapshot,count,q,phaseQ,response,close,nextCount⟩ := pending
  have same : q=p := Phase.reply.inj (phaseQ.symm.trans phase)
  subst q
  have nextState : (State.mk p.response.state p.nextCount (.head []))=⟨s,0,.head []⟩ := by rw [response,nextCount]
  refine ⟨⟨s,0,.head []⟩,?_,masked,6+118,⟨d,after⟩,complete.trans restart,?_⟩
  · rw [←nextState]
    exact ProtocolStreamTrace.complete phase remaining
  · exact Or.inr (Or.inl (Or.inl (HeaderPhase.enter final)))
theorem send_reply {a m g} (h : SendPhase.Cut a m g) : ∃ p,g.phase=.reply p := by
  rcases h with active|returned
  · cases active with
    | head _ _ _ uart | body _ _ _ _ _ _ uart =>
      cases uart.2.2.1 with
      | loading phase _ _ | polling phase _ _ | before phase _ _ | emitting phase _ _ | branch phase _ _ => exact ⟨_,phase⟩
  · obtain ⟨ret,result,close,done,bytes,frame,p,phase,empty⟩ := returned
    exact ⟨p,phase⟩

theorem boundary {original before s served status m g} (h : RefusalPhase.Ready original before s served status)
    (post : SendPhase.Cut (call h) m g) (pending : Pending s served status g) :
    ∃ next,ProtocolStreamTrace.Trace g [] [] next ∧ ReactiveEnvelope.Envelope Cut m next := by
  rcases post with active|returned
  · have masked : m.core.mie_=false := by
      cases active with
      | head _ _ _ uart | body _ _ _ _ _ _ uart => exact UartTxPhase.masked uart.2.2.1
    exact ⟨g,ProtocolStreamTrace.refl _,masked,0,m,.refl _,Or.inl ⟨original,before,s,served,status,h,active,pending⟩⟩
  · exact finish h returned pending

/-- Each actual sender instruction, including the last byte's real return
    and restart continuation, preserves the pending response metadata. -/
theorem next {m g} (h : Active m g) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img m o=⟨.ok d m.ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧ ReactiveEnvelope.Envelope Cut ⟨d,m.ram⟩ next := by
  obtain ⟨original,before,s,served,status,ready,active,pending⟩ := h
  obtain ⟨d,reads,evs,mid,step,trace,mask,n,last,quiet,post⟩ := SendPhase.next active o
  have noInput := SendPhase.no_input active o
  rw [step] at noInput
  have traceNoInput : ProtocolStreamTrace.Trace g [] (Observed.output evs) mid := by simpa only [noInput] using trace
  obtain ⟨p,phase⟩ := send_reply post
  obtain ⟨snapshot,count,q,phaseQ,response,close,nextCount⟩ := pending
  obtain ⟨snapshotFrame,countFrame,responseFrame,closeFrame,nextFrame⟩ := ReplyMetadata.pending phaseQ phase traceNoInput
  have pendingNext : Pending s served status mid :=
    ⟨snapshotFrame.trans snapshot,countFrame.trans count,p,phase,responseFrame.trans response,closeFrame.trans close,nextFrame.trans nextCount⟩
  obtain ⟨next,tau,maskLast,k,final,tail,finalPost⟩ := boundary ready post pendingNext
  refine ⟨d,reads,evs,next,step,?_,mask,n+k,final,quiet.trans tail,finalPost⟩
  simpa only [List.append_nil] using ProtocolStreamTrace.trans trace tau

theorem safe {m g} (h : Active m g) : ¬Escapes B img m := by
  obtain ⟨original,before,s,served,status,ready,active,pending⟩ := h
  exact SendPhase.safe active

/-- Refusal setup starts the same actual renderer/transmitter and retains
    the pure response family through the real quiet entry prefix. -/
theorem start {c ram g} (h : RefusalPhase.At c ram g) :
    ∃ next,ProtocolStreamTrace.Trace g [] [] next ∧ ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ next := by
  obtain ⟨s,served,status,ready,ghost⟩ := h
  rw [ghost]
  let model := ProtocolStreamSpec.reject ⟨s,served,.head []⟩ status
  let pending : ProtocolStreamSpec.Pending :=
    ⟨⟨s,status,[],[]⟩,true,0,ResponseHeadSpec.bytes status [] 0 true++ResponseHeadSpec.body status false []⟩
  have phase : model.phase=.reply pending := rfl
  have queue : pending.remaining=SendPhase.header (call ready)++SendPhase.body (call ready) := rfl
  have family : Pending s served status model := ⟨rfl,rfl,pending,phase,rfl,rfl,rfl⟩
  obtain ⟨mask,n,last,quiet,post⟩ := SendPhase.start (call ready) phase queue
  obtain ⟨next,tau,maskLast,k,final,tail,finalPost⟩ := boundary ready post family
  exact ⟨next,tau,mask,n+k,final,quiet.trans tail,finalPost⟩

end E5R.Thermostat.RefusalSendPhase
