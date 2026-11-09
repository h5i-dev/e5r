import Projects.thermostat.ReactiveEnvelope
set_option autoImplicit false
namespace E5R.Thermostat.ReactiveEnvelope
open E5R E5R.Thermostat

/-- Compose actual quiet continuations between the named receive/send cuts.
    This does not discharge either cut's reactive closure obligation. -/
theorem bind {I J : Machine → Ghost → Prop} {m g} (h : Envelope I m g)
    (next : ∀ d,I d g → Envelope J d g) : Envelope J m g := by
  obtain ⟨mask,n,d,quiet,post⟩ := h
  obtain ⟨lastMask,k,e,tail,final⟩ := next d post
  exact ⟨mask,n+k,e,quiet.trans tail,final⟩

theorem map {I J : Machine → Ghost → Prop} {m g} (h : Envelope I m g)
    (next : ∀ d,I d g → J d g) : Envelope J m g := by
  obtain ⟨mask,n,d,quiet,post⟩ := h
  exact ⟨mask,n,d,quiet,next d post⟩
end E5R.Thermostat.ReactiveEnvelope
