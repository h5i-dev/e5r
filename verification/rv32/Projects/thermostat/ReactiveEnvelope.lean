import Projects.thermostat.ProtocolStreamTrace
import Projects.thermostat.QuietPrefix
set_option autoImplicit false
namespace E5R.Thermostat.ReactiveEnvelope
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev Ghost := ProtocolStreamSpec.State

def Envelope (I : Machine → Ghost → Prop) (m : Machine) (g : Ghost) : Prop :=
  m.core.mie_=false ∧ ∃ n d,Quiet.Steps B img n m d ∧ I d g

/-- The explicit proof obligation at each actual UART/control cutpoint.
    This rule is not a firmware theorem until concrete I supplies every case. -/
def Closed (I : Machine → Ghost → Prop) : Prop :=
  ∀ m g,I m g → m.core.mie_=false → ¬Escapes B img m ∧
    ∀ d reads evs,Observed.Step B img m d reads evs →
      ∃ next,ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧ Envelope I d next

/-- Quiet instruction suffixes preserve the abstract stream state. Actual
    MMIO steps are handled only by the independently supplied cutpoint proof. -/
theorem advance {I} (closed : Closed I) {m g} (h : Envelope I m g) :
    ¬Escapes B img m ∧ ∀ d reads evs,Observed.Step B img m d reads evs →
      ∃ next,ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧ Envelope I d next := by
  obtain ⟨masked,n,last,quiet,post⟩ := h
  cases quiet with
  | refl => exact closed m g post masked
  | @step n a mid last first rest =>
    refine ⟨Trace.no_escape first.det masked,?_⟩
    intro d reads evs actual
    obtain ⟨rfl,rfl,rfl⟩ := QuietPrefix.unique_step first masked actual
    exact ⟨g,ProtocolStreamTrace.refl g,Interrupt.step_masked masked first.det.toStep,n,last,rest,post⟩

/-- Universal observed-prefix safety and stream correspondence, conditional
    on a proved complete collection of concrete phase cutpoints. No readiness
    or finite-response assumption is used in this induction. -/
theorem reach {Init : Machine → Prop} {I : Machine → Ghost → Prop}
    (initial : ∀ m,Init m → Envelope I m ProtocolStreamSpec.initial) (closed : Closed I)
    {m reads evs} (actual : Observed.Reach B img Init m reads evs) :
    ∃ g,Envelope I m g ∧ ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g ∧
      ¬Escapes B img m := by
  induction actual with
  | @init m hi =>
    have env := initial m hi
    exact ⟨_,env,ProtocolStreamTrace.refl _,(advance closed env).1⟩
  | @step m d oldReads reads oldEvs evs path step ih =>
    obtain ⟨g,env,trace,safe⟩ := ih
    obtain ⟨next,one,post⟩ := (advance closed env).2 d reads evs step
    refine ⟨next,post,?_,(advance closed post).1⟩
    simpa only [Observed.input_append,Observed.output_append] using ProtocolStreamTrace.trans trace one

/-- Platform Reach is the same actual execution after erasing instrumentation;
    the accepted RBR trace is recovered, rather than postulated as input. -/
theorem platform_reach {Init : Machine → Prop} {I : Machine → Ghost → Prop}
    (initial : ∀ m,Init m → Envelope I m ProtocolStreamSpec.initial) (closed : Closed I)
    {m evs} (actual : E5R.Reach B img Init m evs) :
    ¬Escapes B img m ∧ ∃ reads g,Observed.Reach B img Init m reads evs ∧ Envelope I m g ∧
      ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g := by
  obtain ⟨reads,observed⟩ := Observed.reach_complete actual
  obtain ⟨g,env,trace,safe⟩ := reach initial closed observed
  exact ⟨safe,reads,g,observed,env,trace⟩
end E5R.Thermostat.ReactiveEnvelope
