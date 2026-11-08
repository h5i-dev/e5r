import Theories.Logic
import Projects.thermostat.Observed
namespace E5R.Thermostat.ObservedDet
open E5R E5R.Thermostat

/-- A silent-result deterministic path lifts to an observed path with an
    explicit existential read log. Ignored device reads cannot be erased. -/
theorem complete {B img n a b} (h : DetSteps B img n a b) :
    ∃ reads, Observed.Steps B img n a b reads [] := by
  induction h with
  | refl m => exact ⟨[],.refl m⟩
  | step hs _ ih =>
    obtain ⟨r0,hr0⟩ := Observed.step_complete hs.toStep
    obtain ⟨r1,hr1⟩ := ih
    exact ⟨r0++r1,by simpa only [List.nil_append] using Observed.Steps.step hr0 hr1⟩
end E5R.Thermostat.ObservedDet
