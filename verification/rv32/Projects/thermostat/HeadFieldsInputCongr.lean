import Projects.thermostat.HeadFieldsStepSpec
import Projects.thermostat.HeadActionCongr
import Projects.thermostat.HeadFieldCongr
namespace E5R.Thermostat.HeadFieldsInputCongr
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem header_parsed (g : Nat → Nat) (i cap le : Nat) (parsed : HdrLine)
    (value : HeadFieldLineSpec.next g i cap=.header le parsed) : headerLine g i le=parsed := by
  unfold HeadFieldLineSpec.next at value
  dsimp only at value
  split at value
  next more => cases value
  next notMore =>
    split at value
    next bad => cases value
    next notBad =>
      split at value
      next empty => cases value
      next nonempty => cases value;rfl

theorem header_bounds (g : Nat → Nat) (i e ne vs ve : Nat) (parsed : headerLine g i e=.ok ne vs ve) :
    i<ne ∧ ne<vs ∧ vs≤ve ∧ ve≤e := by
  unfold headerLine at parsed
  dsimp only at parsed
  split at parsed
  next invalid => cases parsed
  next nameRange =>
    split at parsed
    next notColon => cases parsed
    next colon =>
      split at parsed
      next invalidValue => cases parsed
      next validValue =>
        cases parsed
        have nameGe := scan_ge isTchar g i e
        have nameLt : scan isTchar g i e<e := by omega
        have valueGe := scan_ge isOws g (scan isTchar g i e+1) e
        have valueLe := scan_le isOws g (scan isTchar g i e+1) e (by omega)
        exact ⟨by omega,by omega,trimEnd_ge g _ _ valueLe,trimEnd_le g _ _⟩

theorem line_congr (g h : Nat → Nat) (i cap : Nat) (inside : i<cap) (agree : ∀ k, k<cap → g k=h k) :
    HeadFieldLineSpec.next g i cap=HeadFieldLineSpec.next h i cap := by
  unfold HeadFieldLineSpec.next
  dsimp only
  rw [HeadLineScanSpec.line_congr g h i cap agree,
    HeadLineScanSpec.term_congr g h (lineEnd h i cap) cap agree]
  have upper : lineEnd h i cap≤cap := scan_le notEol h i cap (by omega)
  rw [HeadFieldCongr.header_congr g h i (lineEnd h i cap) (fun k hk => agree k (by omega))]

theorem one_congr (g h : Nat → Nat) (i cap minor : Nat) (f : Fields) (inside : i<cap)
    (agree : ∀ k, k<cap → g k=h k) : HeadFieldsStepSpec.one g i cap minor f=HeadFieldsStepSpec.one h i cap minor f := by
  unfold HeadFieldsStepSpec.one
  rw [line_congr g h i cap inside agree]
  cases value : HeadFieldLineSpec.next h i cap with
  | more => rfl
  | bad status => rfl
  | done len => rfl
  | header le parsed =>
    obtain ⟨leLower,leUpper⟩ := HeadFieldsStepSpec.header_bound h i cap le parsed inside value
    cases parsed with
    | bad status => rfl
    | ok ne vs ve =>
      dsimp only
      have parsed := header_parsed h i cap le (.ok ne vs ve) value
      obtain ⟨nameLower,valueLower,valueOrder,valueUpper⟩ := header_bounds h i le ne vs ve parsed
      rw [HeadActionSpec.factor,HeadActionSpec.factor,
        HeadActionCongr.action_congr g h f i ne vs ve le minor 1024 cap (by omega) (by omega) agree]
end E5R.Thermostat.HeadFieldsInputCongr
