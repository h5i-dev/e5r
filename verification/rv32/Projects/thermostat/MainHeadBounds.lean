import Projects.thermostat.HeadFieldsClBound
import Projects.thermostat.HeadFieldsInputCongr
import Projects.thermostat.HeadFieldsResultSpec
import Projects.thermostat.HeadRequestSuccess
import Projects.thermostat.HttpRequestBytes
namespace E5R.Thermostat.MainHeadBounds
open E5R E5R.Thermostat HttpRequestSpec

/-- Every recorded slice is ordered and contained in the consumed head. -/
def FieldAt (cap : Nat) (f : Field) : Prop := f.ns<f.ne ∧ f.ne<f.vs ∧ f.vs≤f.ve ∧ f.ve≤cap

theorem add (g : Nat → Nat) (f nextFields : Fields) (ns ne vs ve le minor max cap : Nat)
    (old : ∀ entry∈f.headers, FieldAt cap entry) (new : FieldAt cap ⟨ns,ne,vs,ve⟩)
    (accepted : addHeader g f ns ne vs ve le minor max=.ok nextFields) :
    ∀ entry∈nextFields.headers, FieldAt cap entry := by
  rw [HeadActionSpec.factor] at accepted
  split at accepted
  next full => cases accepted
  next room =>
    cases action : HeadActionSpec.action g f ns ne vs ve le minor max with
    | bad status => rw [action] at accepted;cases accepted
    | ok updated =>
      rw [action] at accepted
      cases accepted
      intro entry belongs
      rcases List.mem_append.mp belongs with previous | last
      · exact old entry previous
      · have equal := List.mem_singleton.mp last
        subst entry
        exact new

theorem fields (g : Nat → Nat) (cap minor max i : Nat) (f result : Fields) (len : Nat)
    (old : ∀ entry∈f.headers, FieldAt cap entry)
    (accepted : HttpRequestSpec.fields g cap minor max i f=.done result len) :
    len≤cap ∧ (∀ entry∈result.headers, FieldAt cap entry) := by
  rw [HttpRequestSpec.fields] at accepted
  split at accepted
  next inside =>
    try dsimp only at accepted
    split at accepted
    next more => cases accepted
    next notMore =>
      split at accepted
      next bad => cases accepted
      next notBad =>
        have lineBound := HeadFieldsResultSpec.term g (lineEnd g i cap) cap notMore notBad
        split at accepted
        next empty => cases accepted;exact ⟨lineBound,old⟩
        next nonempty =>
          cases line : headerLine g i (lineEnd g i cap) with
          | bad status => rw [line] at accepted;cases accepted
          | ok ne vs ve =>
            rw [line] at accepted
            try dsimp only at accepted
            cases added : addHeader g f i ne vs ve (lineEnd g i cap) minor max with
            | bad status => rw [added] at accepted;cases accepted
            | ok updated =>
              rw [added] at accepted
              have shape := HeadFieldsInputCongr.header_bounds g i (lineEnd g i cap) ne vs ve line
              have new : FieldAt cap ⟨i,ne,vs,ve⟩ := ⟨shape.1,shape.2.1,shape.2.2.1,by change ve≤cap;have := shape.2.2.2;omega⟩
              exact fields g cap minor max ((lineEnd g i cap)+2) updated result len
                (add g f updated i ne vs ve (lineEnd g i cap) minor max cap old new added) accepted
  next outside => cases accepted
termination_by cap-i
 decreasing_by have := HttpRequestSpec.scan_ge notEol g i cap;unfold lineEnd at *;omega

theorem request (g : Nat → Nat) (j ms me ts te minor : Nat)
    (accepted : requestLine g 0 j=.ok ms me ts te minor) :
    ms=0 ∧ 0<me ∧ me<ts ∧ ts<te ∧ te<j ∧ minor≤1 := by
  have shape := HeadRequestSuccess.shape g j ms me ts te minor accepted
  unfold requestLine at accepted
  try dsimp only at accepted
  split at accepted
  next bad => cases accepted
  next good =>
    split at accepted
    next bad => cases accepted
    next good =>
      try dsimp only at accepted
      split at accepted
      next bad => cases accepted
      next targetRange =>
        split at accepted
        next bad => cases accepted
        next good =>
          try dsimp only at accepted
          split at accepted
          next bad => cases accepted
          next notThree =>
            split at accepted
            next bad => cases accepted
            next notTwo =>
              cases accepted
              have m := scan_ge isTchar g 0 j
              have t := scan_ge isTargetByte g (scan isTchar g 0 j+1) j
              exact ⟨rfl,by omega,by omega,by omega,by omega,shape.2.2⟩
end E5R.Thermostat.MainHeadBounds
