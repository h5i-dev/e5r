import Projects.thermostat.ProtocolStreamTrace
set_option autoImplicit false
namespace E5R.Thermostat.ReplyMetadata
open E5R E5R.Thermostat ProtocolStreamSpec

/-- An output-only pure prefix stays in the same response or has committed
    that response and is waiting for its next input byte. -/
def During (initial : State) (p : Pending) (m : State) : Prop :=
  (m.snapshot=initial.snapshot ∧ m.served=initial.served ∧
    ∃ q,m.phase=.reply q ∧ q.response=p.response ∧ q.close=p.close ∧ q.nextCount=p.nextCount) ∨
  m=⟨p.response.state,p.nextCount,.head []⟩

theorem advance {initial p m next label} (h : During initial p m) (step : ProtocolStreamSpec.Step m label next)
    (noInput : ProtocolStreamTrace.input label.toList=[]) : During initial p next := by
  cases step with
  | idle => exact h
  | receive received => simp only [Option.toList_some,ProtocolStreamTrace.input,List.filterMap_cons,List.filterMap_nil] at noInput;cases noInput
  | @transmit current byte rest phase bytes =>
    rcases h with ⟨snapshot,served,q,oldPhase,response,close,count⟩|complete
    · have same : q=current := Phase.reply.inj (oldPhase.symm.trans phase)
      subst q
      exact Or.inl ⟨snapshot,served,{current with remaining:=rest},rfl,response,close,count⟩
    · rw [complete] at phase;cases phase
  | @complete current phase empty =>
    rcases h with ⟨snapshot,served,q,oldPhase,response,close,count⟩|complete
    · have same : q=current := Phase.reply.inj (oldPhase.symm.trans phase)
      subst q
      exact Or.inr (by rw [response,count])
    · rw [complete] at phase;cases phase

theorem run {initial p a b actions} (h : During initial p a) (path : Run a actions b)
    (noInput : ProtocolStreamTrace.input actions=[]) : During initial p b := by
  induction path with
  | refl => exact h
  | @step b c label old path step ih =>
    have split : ProtocolStreamTrace.input old=[] ∧ ProtocolStreamTrace.input label.toList=[] := by
      apply List.append_eq_nil_iff.mp
      simpa only [ProtocolStreamTrace.input,List.filterMap_append] using noInput
    exact advance (ih split.1) step split.2

/-- If an output-only prefix still ends in a pending reply, its snapshot,
    counter and response/close/next-count metadata cannot have changed. -/
theorem pending {a b p q output} (first : a.phase=.reply p) (last : b.phase=.reply q)
    (trace : ProtocolStreamTrace.Trace a [] output b) :
    b.snapshot=a.snapshot ∧ b.served=a.served ∧ q.response=p.response ∧ q.close=p.close ∧ q.nextCount=p.nextCount := by
  obtain ⟨actions,path,noInput,out⟩ := trace
  have initial : During a p a := Or.inl ⟨rfl,rfl,p,first,rfl,rfl,rfl⟩
  rcases run initial path noInput with ⟨snapshot,served,r,phase,response,close,count⟩|complete
  · have same : r=q := Phase.reply.inj (phase.symm.trans last)
    subst r
    exact ⟨snapshot,served,response,close,count⟩
  · rw [complete] at last;cases last
end E5R.Thermostat.ReplyMetadata
