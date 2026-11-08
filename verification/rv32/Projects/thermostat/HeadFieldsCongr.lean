import Projects.thermostat.HeadFieldsInputCongr
import Projects.thermostat.HeadFieldsProgress
namespace E5R.Thermostat.HeadFieldsCongr
open E5R E5R.Thermostat HttpRequestSpec

/-- Only the bounded receive slice must agree; no equality of wrapping-address
    functions outside the parser's read limit is asserted. -/
theorem fields (g h : Nat → Nat) (cap minor i : Nat) (f : Fields)
    (agree : ∀ k, k<cap → g k=h k) :
    HttpRequestSpec.fields g cap minor 1024 i f=HttpRequestSpec.fields h cap minor 1024 i f := by
  by_cases inside : i<cap
  · rw [HeadFieldsStepSpec.fields_eq g i cap minor f inside,HeadFieldsStepSpec.fields_eq h i cap minor f inside,
      HeadFieldsInputCongr.one_congr g h i cap minor f inside agree]
    cases selected : HeadFieldsStepSpec.one h i cap minor f with
    | more => rfl
    | bad status => rfl
    | done nextFields len => rfl
    | again index nextFields =>
      obtain ⟨progress,_,_⟩ := HeadFieldsProgress.again h i cap minor index f nextFields inside selected
      exact fields g h cap minor index nextFields agree
  · rw [HttpRequestSpec.fields,ite_eq_right inside,HttpRequestSpec.fields,ite_eq_right inside]
termination_by cap-i
 decreasing_by omega
end E5R.Thermostat.HeadFieldsCongr
