import Projects.thermostat.StackReceivePhases
import Projects.thermostat.StackSenderEntry
import Projects.thermostat.StackRequestPrepare
set_option autoImplicit false
namespace E5R.Thermostat.StackFirmwareStream
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := StackBoard.board
def At (m : Machine) (g : State) : Prop :=
  ReceivePhases.Active m g ∨ StackNormalSendPhase.Active m g ∨ StackRefusalSendPhase.Active m g

theorem receive_boundary {m g} (h : ReceivePhases.Cut m g) : StackPhaseEnvelope.Envelope At m g := by
  rcases h with active|request|refusal
  · have mask : m.core.mie_=false := by
      rcases active with header|length|chunk
      · cases header with
        | polling _ _ live _ | rbr _ _ live _ => exact live.stable.masked
      · cases length with
        | polling _ _ _ live _ | rbr _ _ _ live _ => exact live.state.stable.masked
      · cases chunk with
        | polling _ _ live _ | rbr _ _ live _ => exact live.live.masked
    exact ⟨mask,0,m,.refl _,Or.inl active⟩
  · exact StackPhaseEnvelope.bind (StackRequestPrepare.contract request) (fun _ entry =>
      StackPhaseEnvelope.map (StackSenderEntry.normal entry) (fun _ post => Or.inr (Or.inl post)))
  · exact StackPhaseEnvelope.map (StackSenderEntry.refusal refusal) (fun _ post => Or.inr (Or.inr post))

theorem normal_boundary {m g} (h : StackNormalSendPhase.Cut m g) : StackPhaseEnvelope.Envelope At m g := by
  rcases h with active|receive
  · have mask : m.core.mie_=false := by
      obtain ⟨original,before,response,served,used,json,close,headOnly,ready,send,pending⟩ := active
      exact StackSenderEntry.masked send
    exact ⟨mask,0,m,.refl _,Or.inr (Or.inl active)⟩
  · exact receive_boundary receive

theorem refusal_boundary {m g} (h : StackRefusalSendPhase.Cut m g) : StackPhaseEnvelope.Envelope At m g := by
  rcases h with active|receive
  · have mask : m.core.mie_=false := by
      obtain ⟨original,before,s,served,status,ready,send,pending⟩ := active
      exact StackSenderEntry.masked send
    exact ⟨mask,0,m,.refl _,Or.inr (Or.inr active)⟩
  · exact receive_boundary receive

theorem next {m g} (h : At m g) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img m o=⟨.ok d m.ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧ StackPhaseEnvelope.Envelope At ⟨d,m.ram⟩ next := by
  rcases h with receive|normal|refusal
  · obtain ⟨d,reads,next,step,trace,post⟩ := StackReceivePhases.next receive o
    exact ⟨d,reads,[],next,step,trace,StackPhaseEnvelope.bind post (fun _ cut => receive_boundary cut)⟩
  · obtain ⟨d,reads,evs,next,step,trace,post⟩ := StackNormalSendPhase.next normal o
    exact ⟨d,reads,evs,next,step,trace,StackPhaseEnvelope.bind post (fun _ cut => normal_boundary cut)⟩
  · obtain ⟨d,reads,evs,next,step,trace,post⟩ := StackRefusalSendPhase.next refusal o
    exact ⟨d,reads,evs,next,step,trace,StackPhaseEnvelope.bind post (fun _ cut => refusal_boundary cut)⟩

theorem safe {m g} (h : At m g) : ¬Escapes B img m := by
  rcases h with receive|normal|refusal
  · exact StackReceivePhases.safe receive
  · exact StackNormalSendPhase.safe normal
  · exact StackRefusalSendPhase.safe refusal

/-- The concrete monitored invariant, including each actual sender's narrow
    byte views. This is proved closed, never supplied by the environment. -/
def Cut (m : Machine) : Prop := ∃ g,At m g

theorem closed : StackEnvelope.Closed Cut := by
  intro m h mask
  obtain ⟨g,h⟩ := h
  refine ⟨safe h,?_⟩
  intro d reads evs actual
  have monitored := StackEnvelope.same_step (safe h) actual
  cases monitored with
  | instr o value =>
    obtain ⟨e,log,events,next,step,trace,post⟩ := next h o
    rw [step] at value
    cases value
    obtain ⟨masked,n,last,quiet,live⟩ := post
    exact ⟨masked,n,last,quiet,next,live⟩
  | irq code enabled branch => simp [irqEnabled,mask] at enabled

/-- The same real initialized receive cut is reached from architectural reset
    on both boards. No Request, desired outcome or future UART slot is assumed. -/
theorem initial {m} (h : FirmwareStream.Reset m) : StackEnvelope.Envelope Cut m := by
  obtain ⟨a,ram,original,ready⟩ := LoopReady.reset m.core m.ram h.1 h.2.2.1 h.2.2.2
  obtain ⟨b,after,restricted,post⟩ := StackBoard.boot (ram := m.ram) h.1 h.2.2.1
  have same : (⟨b,after⟩ : Machine)=⟨a,ram⟩ :=
    DetRunUnique.steps (StackBoardSimulation.quiet_steps restricted).det original.det
  have quiet : Quiet.Steps B img 2550 m ⟨a,ram⟩ := by
    rw [←same]
    exact restricted
  exact ⟨h.2.1,2550,⟨a,ram⟩,quiet,ProtocolStreamSpec.initial,Or.inl (Or.inl (HeaderPhase.enter ready))⟩

/-- All actual original-board finite prefixes succeed under the64KiB RAM
    monitor with exactly the same machine, read log and write events. -/
theorem observed {m reads evs} (actual : Observed.Reach UartPlatform.board img FirmwareStream.Reset m reads evs) :
    StackEnvelope.Envelope Cut m ∧ ¬Escapes B img m ∧ Observed.Reach B img FirmwareStream.Reset m reads evs :=
  StackEnvelope.reach (fun _ h => initial h) closed actual
end E5R.Thermostat.StackFirmwareStream
