import Projects.thermostat.HeadFieldsInputCongr
import Projects.thermostat.HeadHeaderDecisionSpec
namespace E5R.Thermostat.HeadFieldsProgress
open E5R E5R.Thermostat HttpRequestSpec

theorem add_length (g : Nat → Nat) (f nextFields : Fields) (ns ne vs ve le minor : Nat)
    (accepted : addHeader g f ns ne vs ve le minor 1024=.ok nextFields) :
    nextFields.headers.length=f.headers.length+1 := by
  rw [HeadHeaderDecisionSpec.addHeader] at accepted
  cases selected : HeadHeaderDecisionSpec.result g f ns ne vs ve le minor with
  | bad status => rw [selected] at accepted;cases accepted
  | ok flags =>
    rw [selected] at accepted
    dsimp only [HeadActionSpec.append] at accepted
    cases accepted
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add]

theorem again (g : Nat → Nat) (i cap minor index : Nat) (f nextFields : Fields) (inside : i<cap)
    (selected : HeadFieldsStepSpec.one g i cap minor f=.again index nextFields) :
    i<index ∧ index<cap ∧ nextFields.headers.length=f.headers.length+1 := by
  unfold HeadFieldsStepSpec.one at selected
  cases line : HeadFieldLineSpec.next g i cap with
  | more => rw [line] at selected;cases selected
  | bad status => rw [line] at selected;cases selected
  | done len => rw [line] at selected;cases selected
  | header le parsed =>
    rw [line] at selected
    obtain ⟨lo,hi⟩ := HeadFieldsStepSpec.header_bound g i cap le parsed inside line
    cases parsed with
    | bad status => cases selected
    | ok ne vs ve =>
      dsimp only at selected
      cases added : addHeader g f i ne vs ve le minor 1024 with
      | bad status => rw [added] at selected;cases selected
      | ok flags =>
        rw [added] at selected
        dsimp only at selected
        split at selected
        next more =>
          cases selected
          exact ⟨by omega,more,add_length g f nextFields i ne vs ve le minor added⟩
        next exhausted => cases selected
end E5R.Thermostat.HeadFieldsProgress
