import Projects.thermostat.StreamRequestPrepare
import Projects.thermostat.SenderEntry
set_option autoImplicit false
namespace E5R.Thermostat.FirmwareStream
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- Concrete actual UART cuts. All parser/router/handler/return code between
    them is covered by checked quiet instruction certificates. -/
def At (m : Machine) (g : State) : Prop :=
  ReceivePhases.Active m g ∨ NormalSendPhase.Active m g ∨ RefusalSendPhase.Active m g

theorem receive_boundary {m g} (h : ReceivePhases.Cut m g) : ReactiveEnvelope.Envelope At m g := by
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
  · exact ReactiveEnvelope.bind (RequestPrepare.contract request) (fun _ entry =>
      ReactiveEnvelope.map (SenderEntry.normal entry) (fun _ post => Or.inr (Or.inl post)))
  · exact ReactiveEnvelope.map (SenderEntry.refusal refusal) (fun _ post => Or.inr (Or.inr post))

theorem normal_boundary {m g} (h : NormalSendPhase.Cut m g) : ReactiveEnvelope.Envelope At m g := by
  rcases h with active|receive
  · have mask : m.core.mie_=false := by
      obtain ⟨original,before,response,served,used,json,close,headOnly,ready,send,pending⟩ := active
      exact SenderEntry.masked send
    exact ⟨mask,0,m,.refl _,Or.inr (Or.inl active)⟩
  · exact receive_boundary receive

theorem refusal_boundary {m g} (h : RefusalSendPhase.Cut m g) : ReactiveEnvelope.Envelope At m g := by
  rcases h with active|receive
  · have mask : m.core.mie_=false := by
      obtain ⟨original,before,s,served,status,ready,send,pending⟩ := active
      exact SenderEntry.masked send
    exact ⟨mask,0,m,.refl _,Or.inr (Or.inr active)⟩
  · exact receive_boundary receive

theorem next {m g} (h : At m g) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img m o=⟨.ok d m.ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧ ReactiveEnvelope.Envelope At ⟨d,m.ram⟩ next := by
  rcases h with receive|normal|refusal
  · obtain ⟨d,reads,next,step,trace,post⟩ := ReceivePhases.next receive o
    exact ⟨d,reads,[],next,step,trace,ReactiveEnvelope.bind post (fun _ cut => receive_boundary cut)⟩
  · obtain ⟨d,reads,evs,next,step,trace,post⟩ := NormalSendPhase.next normal o
    exact ⟨d,reads,evs,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => normal_boundary cut)⟩
  · obtain ⟨d,reads,evs,next,step,trace,post⟩ := RefusalSendPhase.next refusal o
    exact ⟨d,reads,evs,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => refusal_boundary cut)⟩

theorem safe {m g} (h : At m g) : ¬Escapes B img m := by
  rcases h with receive|normal|refusal
  · exact ReceivePhases.safe receive
  · exact NormalSendPhase.safe normal
  · exact RefusalSendPhase.safe refusal

/-- Every case of the actual global cutpoint obligation is discharged. This
    is no longer a generic theorem with desired firmware closure as a premise. -/
theorem closed : ReactiveEnvelope.Closed At := by
  intro m g h mask
  refine ⟨safe h,?_⟩
  intro d reads evs actual
  cases actual with
  | instr o value =>
    obtain ⟨e,log,events,next,step,trace,post⟩ := next h o
    rw [step] at value
    cases value
    exact ⟨next,by simpa only [step] using trace,post⟩
  | irq code enabled branch => simp [irqEnabled,mask] at enabled

/-- Loader/image map, architectural reset MIE and legal reset privilege.
    No received request, future readiness or interior layout is a premise. -/
def Reset (m : Machine) : Prop := m.core.pc=0x80000000#32 ∧ m.core.mie_=false ∧
  (m.core.mpp=0 ∨ m.core.mpp=3) ∧ Memory.Block B 0x80ff0000#32 65536

theorem initial {m} (h : Reset m) : ReactiveEnvelope.Envelope At m ProtocolStreamSpec.initial := by
  exact ReactiveEnvelope.bind (ReceivePhases.reset h.1 h.2.2.1 h.2.2.2 h.2.1) (fun _ post => receive_boundary post)

/-- All finite actual execution prefixes, including arbitrary partial RX/TX
    and perpetual-not-ready prefixes, refine the pure stream machine and have
    no fault/unsupported escape. Explicit PC/stack/panic bounds are separate. -/
theorem observed_prefix {m reads evs} (actual : Observed.Reach B img Reset m reads evs) :
    ∃ g,ReactiveEnvelope.Envelope At m g ∧ ProtocolStreamTrace.Trace ProtocolStreamSpec.initial
      (Observed.input reads) (Observed.output evs) g ∧ ¬Escapes B img m :=
  ReactiveEnvelope.reach (fun _ h => initial h) closed actual

theorem platform_prefix {m evs} (actual : E5R.Reach B img Reset m evs) :
    ¬Escapes B img m ∧ ∃ reads g,Observed.Reach B img Reset m reads evs ∧ ReactiveEnvelope.Envelope At m g ∧
      ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g :=
  ReactiveEnvelope.platform_reach (fun _ h => initial h) closed actual
end E5R.Thermostat.FirmwareStream
