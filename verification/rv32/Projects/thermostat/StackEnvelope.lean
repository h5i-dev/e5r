import Projects.thermostat.FirmwareStream
import Projects.thermostat.StackBoardSimulation
set_option autoImplicit false
namespace E5R.Thermostat.StackEnvelope
open E5R E5R.Thermostat
abbrev narrow := StackBoard.board
abbrev broad := UartPlatform.board

def Envelope (I : Machine → Prop) (m : Machine) : Prop :=
  m.core.mie_=false ∧ ∃ n cut,Quiet.Steps narrow img n m cut ∧ I cut

/-- The remaining concrete obligation at each original UART cut. It must be
    discharged for every cut before a global stack-access claim is available. -/
def Closed (I : Machine → Prop) : Prop := ∀ m,I m → m.core.mie_=false →
  ¬Escapes narrow img m ∧ ∀ d reads evs,Observed.Step broad img m d reads evs → Envelope I d

/-- A successful monitored step equals the original step with the same
    nondeterministic choice, including all accepted read and write events. -/
theorem same_step {m d reads evs} (safe : ¬Escapes narrow img m)
    (actual : Observed.Step broad img m d reads evs) : Observed.Step narrow img m d reads evs := by
  cases actual with
  | instr o value =>
    cases small : Observed.stepInstr narrow img m o with
    | mk result log =>
      cases result with
      | fault f =>
        have fault : E5R.stepInstr narrow img m o=.fault f :=
          (Observed.erase_step narrow img m o).symm.trans (by rw [small])
        exact False.elim (safe (Or.inl ⟨o,f,fault⟩))
      | ok c ram events =>
        have success : (Observed.stepInstr narrow img m o).value=.ok c ram events := by rw [small]
        have agrees := StackBoardSimulation.instruction success
        rw [agrees,small] at value
        cases value
        have step := Observed.Step.instr (B := narrow) (img := img) (m := m) o success
        simpa only [agrees] using step
  | irq code enabled branch => exact .irq code enabled branch

theorem advance {I m} (closed : Closed I) (h : Envelope I m) :
    ¬Escapes narrow img m ∧ ∀ d reads evs,Observed.Step broad img m d reads evs → Envelope I d := by
  obtain ⟨masked,n,cut,quiet,post⟩ := h
  cases quiet with
  | refl => exact closed m post masked
  | @step n a mid cut first rest =>
    refine ⟨Trace.no_escape first.det masked,?_⟩
    intro d reads evs actual
    obtain ⟨rfl,rfl,rfl⟩ := QuietPrefix.unique_step (StackBoardSimulation.quiet_step first) masked actual
    exact ⟨Interrupt.step_masked masked first.det.toStep,n,cut,rest,post⟩

/-- Every actual original-board prefix also executes under the narrower RAM
    monitor. This rule assumes no input readiness, no final response, and no
    desired internal state. Its concrete Closed obligation remains explicit. -/
theorem reach {Init I} (initial : ∀ m,Init m → Envelope I m) (closed : Closed I)
    {m reads evs} (actual : Observed.Reach broad img Init m reads evs) :
    Envelope I m ∧ ¬Escapes narrow img m ∧ Observed.Reach narrow img Init m reads evs := by
  induction actual with
  | @init m hi =>
    have env := initial m hi
    exact ⟨env,(advance closed env).1,.init hi⟩
  | step path step ih =>
    have env := (advance closed ih.1).2 _ _ _ step
    exact ⟨env,(advance closed env).1,.step ih.2.2 (same_step ih.2.1 step)⟩

def Cut (m : Machine) : Prop := ∃ g,FirmwareStream.At m g

/-- Actual reset initializes the same original cut invariant, while all2550
    instructions also execute with RAM restricted to the64KiB stack arena. -/
theorem initial {m} (h : FirmwareStream.Reset m) : Envelope Cut m := by
  obtain ⟨a,ram,original,ready⟩ := LoopReady.reset m.core m.ram h.1 h.2.2.1 h.2.2.2
  obtain ⟨b,after,restricted,post⟩ := StackBoard.boot (ram := m.ram) h.1 h.2.2.1
  have same : (⟨b,after⟩ : Machine)=⟨a,ram⟩ :=
    DetRunUnique.steps (StackBoardSimulation.quiet_steps restricted).det original.det
  have quiet : Quiet.Steps narrow img 2550 m ⟨a,ram⟩ := by
    rw [←same]
    exact restricted
  exact ⟨h.2.1,2550,⟨a,ram⟩,quiet,ProtocolStreamSpec.initial,Or.inl (Or.inl (HeaderPhase.enter ready))⟩
end E5R.Thermostat.StackEnvelope
