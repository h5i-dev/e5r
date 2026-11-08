-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Proof
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open E5R
namespace E5R.Thermostat
theorem run_sound_quiet {image : List Segment} {B : Board} {n : Nat} {c d : Core}
    (h : run image n c = some d) (ram : Word → BitVec 8) :
    Quiet.Steps B image n ⟨c, ram⟩ ⟨d, ram⟩ := by
  induction n generalizing c with
  | zero => simp [run] at h; subst d; exact .refl _
  | succ n ih =>
    simp only [run] at h
    split at h
    · contradiction
    · rename_i ha
      cases hd : fetchDecode image c.pc with
      | none => simp [hd] at h
      | some pair =>
        obtain ⟨i, len⟩ := pair
        simp only [hd] at h
        cases he : exec c len i <;> simp only [he] at h
        case done d' =>
          exact .step (Quiet.step_of (by simpa using ha) hd (fun o => by rw [he]; rfl)) (ih h)
        all_goals contradiction

end E5R.Thermostat
