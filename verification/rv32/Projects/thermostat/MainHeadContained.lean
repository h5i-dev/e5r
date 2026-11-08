import Projects.thermostat.MainHeadAcceptedBounds
namespace E5R.Thermostat.MainHeadContained
open E5R E5R.Thermostat HttpRequestSpec

theorem field_widen {small large : Nat} {entry : Field} (h : MainHeadBounds.FieldAt small entry) (le : small≤large) : MainHeadBounds.FieldAt large entry :=
  ⟨h.1,h.2.1,h.2.2.1,Nat.le_trans h.2.2.2 le⟩

/-- All stored header slices precede the completed head, even when the parser
    was called on a buffer that also contains body/pipelined bytes. -/
theorem fields (g : Nat → Nat) (cap minor max i : Nat) (f result : Fields) (len : Nat)
    (old : ∀ entry∈f.headers, MainHeadBounds.FieldAt i entry)
    (accepted : HttpRequestSpec.fields g cap minor max i f=.done result len) :
    i+2≤len ∧ (∀ entry∈result.headers, MainHeadBounds.FieldAt len entry) := by
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
        have leLower := scan_ge notEol g i cap
        split at accepted
        next empty =>
          cases accepted
          refine ⟨by unfold lineEnd at *;omega,?_⟩
          intro entry belongs
          exact field_widen (old entry belongs) (by unfold lineEnd at *;omega)
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
              have newer : MainHeadBounds.FieldAt (lineEnd g i cap+2) ⟨i,ne,vs,ve⟩ := ⟨shape.1,shape.2.1,shape.2.2.1,by change ve≤lineEnd g i cap+2;have := shape.2.2.2;omega⟩
              have previous : ∀ entry∈f.headers, MainHeadBounds.FieldAt (lineEnd g i cap+2) entry := by
                intro entry belongs
                exact field_widen (old entry belongs) (by unfold lineEnd at *;omega)
              have next := MainHeadBounds.add g f updated i ne vs ve (lineEnd g i cap) minor max (lineEnd g i cap+2) previous newer added
              obtain ⟨lower,contained⟩ := fields g cap minor max (lineEnd g i cap+2) updated result len next accepted
              exact ⟨by unfold lineEnd at *;omega,contained⟩
  next outside => cases accepted
termination_by cap-i
 decreasing_by have := HttpRequestSpec.scan_ge notEol g i cap;unfold lineEnd at *;omega

/-- Request spans and header fields lie inside head.len itself, as required
    by the later raw[..used] construction. The read limit alone is insufficient. -/
theorem accepted (input : List Nat) (maxHead maxBody : Nat) (head : Head)
    (parsed : parseHead input maxHead maxBody=.done head) :
    head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry) := by
  let cap := readLimit input.length maxHead
  let g := window input cap
  let j := lineEnd g 0 cap
  unfold parseHead at parsed
  dsimp only at parsed
  split at parsed
  next more => split at parsed <;> cases parsed
  next notMore =>
    split at parsed
    next bad => cases parsed
    next notBad =>
      cases req : requestLine g 0 j with
      | bad status => rw [req] at parsed;cases parsed
      | ok ms me ts te minor =>
        rw [req] at parsed
        dsimp only at parsed
        have request := MainHeadBounds.request g j ms me ts te minor req
        cases found : HttpRequestSpec.fields g cap minor maxBody (j+2) Fields.empty with
        | more => rw [found] at parsed;dsimp only at parsed;split at parsed <;> cases parsed
        | bad status => rw [found] at parsed;cases parsed
        | done f len =>
          rw [found] at parsed
          dsimp only at parsed
          split at parsed
          next missing => cases parsed
          next host =>
            cases parsed
            have contained := fields g cap minor maxBody (j+2) Fields.empty f len (by intro entry impossible;cases impossible) found
            exact ⟨by change te<len;have := request.2.2.2.2.1;have := contained.1;omega,contained.2⟩

theorem bytes (input : List (BitVec 8)) (head : Head) (parsed : HttpRequestBytes.parse input 1024 1024=.done head) :
    head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry) := accepted _ _ _ _ parsed
end E5R.Thermostat.MainHeadContained
