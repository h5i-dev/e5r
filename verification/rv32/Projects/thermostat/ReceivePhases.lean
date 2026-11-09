import Projects.thermostat.EmptyPhase
import Projects.thermostat.LengthCompletePhase
import Projects.thermostat.ChunkCompletePhase
import Projects.thermostat.RefusalPhase
import Projects.thermostat.ReactiveEnvelopeComposition
set_option autoImplicit false
namespace E5R.Thermostat.ReceivePhases
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec
abbrev B := UartPlatform.board

def Active (m : Machine) (g : State) : Prop :=
  HeaderPhase.At m.core m.ram g ∨ LengthPhase.At m.core m.ram g ∨ ChunkPhase.At m.core m.ram g

def Boundary (m : Machine) (g : State) : Prop := RequestPhase.At m.core m.ram g ∨ RefusalPhase.At m.core m.ram g

def Cut (m : Machine) (g : State) : Prop := Active m g ∨ Boundary m g

theorem length_boundary {m g} (h : LengthPhase.Cut m g) : ReactiveEnvelope.Envelope Cut m g := by
  rcases h with live|terminal
  · have mask : m.core.mie_=false := by
      cases live with
      | polling _ _ _ live _ => exact live.state.stable.masked
      | rbr _ _ _ live _ => exact live.state.stable.masked
    exact ⟨mask,0,m,.refl _,Or.inl (Or.inr (Or.inl live))⟩
  · exact ReactiveEnvelope.map (LengthCompletePhase.next terminal) (fun _ post => Or.inr (Or.inl post))

theorem chunk_boundary {m g} (h : ChunkPhase.Cut m g) : ReactiveEnvelope.Envelope Cut m g := by
  rcases h with live|capacity|terminal
  · have mask : m.core.mie_=false := by
      cases live with
      | polling _ _ live _ => exact live.live.masked
      | rbr _ _ live _ => exact live.live.masked
    exact ⟨mask,0,m,.refl _,Or.inl (Or.inr (Or.inr live))⟩
  · exact ReactiveEnvelope.map (RefusalPhase.from_chunk_capacity capacity) (fun _ post => Or.inr (Or.inr post))
  · obtain ⟨s,served,original,head,r,context,terminal,stop,body,writeEq,bodyBound,extent,readBound,cursor,filled,ghost⟩ := terminal
    cases outcome : r.stop with
    | needInput => exact False.elim (stop outcome)
    | done =>
      rw [ghost]
      exact ReactiveEnvelope.map (ChunkCompletePhase.next context terminal outcome body writeEq bodyBound extent readBound cursor filled)
        (fun _ post => Or.inr (Or.inl post))
    | reject status =>
      rw [ghost]
      exact ReactiveEnvelope.map (RefusalPhase.from_chunk_reject context terminal outcome) (fun _ post => Or.inr (Or.inr post))

theorem header_boundary {m g} (h : HeaderPhase.Cut m g) : ReactiveEnvelope.Envelope Cut m g := by
  rcases h with live|terminal
  · have mask : m.core.mie_=false := by
      cases live with
      | polling _ _ live _ => exact live.stable.masked
      | rbr _ _ live _ => exact live.stable.masked
    exact ⟨mask,0,m,.refl _,Or.inl (Or.inl live)⟩
  · obtain ⟨original,s,served,boundary,complete,earlier,caller,ghost⟩ := terminal
    cases parsed : HttpRequestBytes.parse original 1024 1024 with
    | incomplete => exact False.elim (complete parsed)
    | reject status =>
      rw [parsed] at boundary
      rw [ghost]
      exact ReactiveEnvelope.map (RefusalPhase.from_header boundary parsed caller) (fun _ post => Or.inr (Or.inr post))
    | done head =>
      rw [parsed] at boundary
      rw [ghost]
      cases kind : head.framing with
      | empty => exact ReactiveEnvelope.map (EmptyPhase.from_header boundary parsed earlier caller kind) (fun _ post => Or.inr (Or.inl post))
      | length amount => exact ReactiveEnvelope.bind (LengthPhase.from_header boundary parsed earlier caller kind) (fun _ post => length_boundary post)
      | chunked => exact ReactiveEnvelope.bind (ChunkPhase.from_header boundary parsed earlier caller kind) (fun _ post => chunk_boundary post)

/-- All receive-side terminal outcomes now lead through actual quiet code to
    another receive cut or the concrete router/refusal send boundary. The
    handler and sender still owe their own total reactive closure cases. -/
theorem next {m g} (h : Active m g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img m o=⟨.ok d m.ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ ReactiveEnvelope.Envelope Cut ⟨d,m.ram⟩ next := by
  rcases h with header|length|chunk
  · obtain ⟨d,reads,next,step,trace,post⟩ := HeaderPhase.next header o
    exact ⟨d,reads,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => header_boundary cut)⟩
  · obtain ⟨d,reads,next,step,trace,post⟩ := LengthPhase.next length o
    exact ⟨d,reads,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => length_boundary cut)⟩
  · obtain ⟨d,reads,next,step,trace,post⟩ := ChunkPhase.next chunk o
    exact ⟨d,reads,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => chunk_boundary cut)⟩

theorem safe {m g} (h : Active m g) : ¬Escapes B img m := by
  rcases h with header|length|chunk
  · exact HeaderPhase.safe header
  · exact LengthPhase.safe length
  · exact ChunkPhase.safe chunk

theorem reset {c ram} (pc : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3)
    (stack : Memory.Block B 0x80ff0000#32 65536) (masked : c.mie_=false) :
    ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ ProtocolStreamSpec.initial := by
  exact ReactiveEnvelope.bind (HeaderPhase.reset c ram pc mpp masked stack) (fun _ post => header_boundary post)
end E5R.Thermostat.ReceivePhases
