import Projects.thermostat.RamRun
import Projects.thermostat.Quiet
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RamRunQuiet
open E5R E5R.Thermostat

/-- The existing checked evaluator accepts only RAM/ROM accesses. Its complete
    instrumented result therefore retains the original accepted-read log. -/
theorem effect_sound {B img e ram m} (h : RamRun.effect B img e ram = some m) :
    ∀ o i evs reads, Observed.interp B img o e ram i evs reads = ⟨.ok m.core m.ram evs,reads⟩ := by
  induction e generalizing ram with
  | done c => simp only [RamRun.effect, Option.some.injEq] at h; subst m; intros; rfl
  | load w a atomic k ih =>
    cases atomic with
    | true => contradiction
    | false =>
      simp only [RamRun.effect] at h
      split at h
      · rename_i ha
        split at h
        · rename_i hr
          intro o i evs reads
          simp only [Observed.interp, ha, ne_eq, not_true_eq_false, ↓reduceIte, hr]
          exact ih _ h o i evs reads
        · rename_i hr
          cases hv : romRead? img a.toNat w.bytes false with
          | none => simp [hv] at h
          | some v =>
            simp only [hv] at h
            intro o i evs reads
            simp only [Observed.interp, ha, ne_eq, not_true_eq_false, ↓reduceIte, hr, hv]
            exact ih _ h o i evs reads
      · contradiction
  | store w a v atomic k ih =>
    cases atomic with
    | true => contradiction
    | false =>
      simp only [RamRun.effect] at h
      split at h
      · rename_i ha
        intro o i evs reads
        simp only [Observed.interp, ha.1, ne_eq, not_true_eq_false, ↓reduceIte, ha.2]
        exact ih h o i evs reads
      · contradiction
  | trap | unsupported | choose | pick => contradiction

theorem sound {B img n m m'} (h : RamRun.run B img n m = some m') : Quiet.Steps B img n m m' := by
  induction n generalizing m with
  | zero => simp only [RamRun.run, Option.some.injEq] at h; subst m'; exact .refl _
  | succ n ih =>
    simp only [RamRun.run] at h
    split at h
    · contradiction
    · rename_i ha
      cases hd : fetchDecode img m.core.pc with
      | none => simp [hd] at h
      | some pair =>
        obtain ⟨i, len⟩ := pair
        simp only [hd] at h
        cases he : RamRun.effect B img (exec m.core len i) m.ram with
        | none => simp [he] at h
        | some m1 =>
          simp only [he] at h
          exact .step (Quiet.step_of (by simpa using ha) hd (fun o => effect_sound he o 0 [] [])) (ih h)

end E5R.Thermostat.RamRunQuiet
