import Projects.thermostat.ReceivePhases
import Projects.thermostat.StackLengthCompletePhase
import Projects.thermostat.StackChunkCompletePhase
import Projects.thermostat.StackRefusalPhase
import Projects.thermostat.StackEmptyPhase
import Projects.thermostat.StackLengthPhase
import Projects.thermostat.StackChunkPhase
import Projects.thermostat.StackHeaderPhase
import Projects.thermostat.StackPhaseEnvelope
set_option autoImplicit false
namespace E5R.Thermostat.StackReceivePhases
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec ReceivePhases
abbrev B := StackBoard.board
theorem length_boundary {m g} (h : LengthPhase.Cut m g) : StackPhaseEnvelope.Envelope Cut m g := by
  rcases h with live|terminal
  · have mask : m.core.mie_=false := by
      cases live with
      | polling _ _ _ live _ => exact live.state.stable.masked
      | rbr _ _ _ live _ => exact live.state.stable.masked
    exact ⟨mask,0,m,.refl _,Or.inl (Or.inr (Or.inl live))⟩
  · exact StackPhaseEnvelope.map (StackLengthCompletePhase.next terminal) (fun _ post => Or.inr (Or.inl post))

theorem chunk_boundary {m g} (h : ChunkPhase.Cut m g) : StackPhaseEnvelope.Envelope Cut m g := by
  rcases h with live|capacity|terminal
  · have mask : m.core.mie_=false := by
      cases live with
      | polling _ _ live _ => exact live.live.masked
      | rbr _ _ live _ => exact live.live.masked
    exact ⟨mask,0,m,.refl _,Or.inl (Or.inr (Or.inr live))⟩
  · exact StackPhaseEnvelope.map (StackRefusalPhase.from_chunk_capacity capacity) (fun _ post => Or.inr (Or.inr post))
  · obtain ⟨s,served,original,head,r,context,terminal,stop,body,writeEq,bodyBound,extent,readBound,cursor,filled,ghost⟩ := terminal
    cases outcome : r.stop with
    | needInput => exact False.elim (stop outcome)
    | done =>
      rw [ghost]
      exact StackPhaseEnvelope.map (StackChunkCompletePhase.next context terminal outcome body writeEq bodyBound extent readBound cursor filled)
        (fun _ post => Or.inr (Or.inl post))
    | reject status =>
      rw [ghost]
      exact StackPhaseEnvelope.map (StackRefusalPhase.from_chunk_reject context terminal outcome) (fun _ post => Or.inr (Or.inr post))

theorem header_boundary {m g} (h : HeaderPhase.Cut m g) : StackPhaseEnvelope.Envelope Cut m g := by
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
      exact StackPhaseEnvelope.map (StackRefusalPhase.from_header boundary parsed caller) (fun _ post => Or.inr (Or.inr post))
    | done head =>
      rw [parsed] at boundary
      rw [ghost]
      cases kind : head.framing with
      | empty => exact StackPhaseEnvelope.map (StackEmptyPhase.from_header boundary parsed earlier caller kind) (fun _ post => Or.inr (Or.inl post))
      | length amount => exact StackPhaseEnvelope.bind (StackLengthPhase.from_header boundary parsed earlier caller kind) (fun _ post => length_boundary post)
      | chunked => exact StackPhaseEnvelope.bind (StackChunkPhase.from_header boundary parsed earlier caller kind) (fun _ post => chunk_boundary post)

/-- All receive-side terminal outcomes now lead through actual quiet code to
    another receive cut or the concrete router/refusal send boundary. The
    handler and sender still owe their own total reactive closure cases. -/
theorem next {m g} (h : Active m g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img m o=⟨.ok d m.ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ StackPhaseEnvelope.Envelope Cut ⟨d,m.ram⟩ next := by
  rcases h with header|length|chunk
  · obtain ⟨d,reads,next,step,trace,post⟩ := StackHeaderPhase.next header o
    exact ⟨d,reads,next,step,trace,StackPhaseEnvelope.bind post (fun _ cut => header_boundary cut)⟩
  · obtain ⟨d,reads,next,step,trace,post⟩ := StackLengthPhase.next length o
    exact ⟨d,reads,next,step,trace,StackPhaseEnvelope.bind post (fun _ cut => length_boundary cut)⟩
  · obtain ⟨d,reads,next,step,trace,post⟩ := StackChunkPhase.next chunk o
    exact ⟨d,reads,next,step,trace,StackPhaseEnvelope.bind post (fun _ cut => chunk_boundary cut)⟩

theorem safe {m g} (h : Active m g) : ¬Escapes B img m := by
  rcases h with header|length|chunk
  · exact StackHeaderPhase.safe header
  · exact StackLengthPhase.safe length
  · exact StackChunkPhase.safe chunk

end E5R.Thermostat.StackReceivePhases
