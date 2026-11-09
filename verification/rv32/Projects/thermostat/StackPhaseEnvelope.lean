import Projects.thermostat.StackEnvelope
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackPhaseEnvelope
open E5R E5R.Thermostat ProtocolStreamSpec 
abbrev B := StackBoard.board
abbrev Envelope (I : Machine → State → Prop) (m : Machine) (g : State) := StackEnvelope.Envelope (fun cut => I cut g) m
theorem bind {I J : Machine → State → Prop} {m g} (h : Envelope I m g)
    (next : ∀ d,I d g → Envelope J d g) : Envelope J m g := by
  obtain ⟨mask,n,d,quiet,post⟩ := h
  obtain ⟨lastMask,k,e,tail,final⟩ := next d post
  exact ⟨mask,n+k,e,quiet.trans tail,final⟩

theorem map {I J : Machine → State → Prop} {m g} (h : Envelope I m g)
    (next : ∀ d,I d g → J d g) : Envelope J m g := by
  obtain ⟨mask,n,d,quiet,post⟩ := h
  exact ⟨mask,n,d,quiet,next d post⟩
end E5R.Thermostat.StackPhaseEnvelope
