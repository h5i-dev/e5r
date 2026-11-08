import Projects.thermostat.HeadNameChecked
namespace E5R.Thermostat.HeadNameSpec
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- A rejected actual name/colon prefix is a rejection of the full independent
    headerLine specification, regardless of the remaining value bytes. -/
theorem reject (g : Nat → Nat) (start finish : Nat) (hi : start<finish)
    (bad : ¬HeadNameChecked.good g start (scan isTchar g start finish) finish) :
    headerLine g start finish=HdrLine.bad 400 := by
  let k := scan isTchar g start finish
  have lower : start≤k := scan_ge isTchar g start finish
  change ¬HeadNameChecked.good g start k finish at bad
  change (if k=start ∨ finish≤k then HdrLine.bad 400 else if g k≠58 then HdrLine.bad 400 else _) = _
  by_cases early : k=start ∨ finish≤k
  · simp only [early,ite_true]
  · have ne : g k≠58 := by
      intro eq
      exact bad ⟨by omega,by omega,eq⟩
    simp [early,ne]

/-- Once the name and exact colon are accepted, only field bytes and OWS
    remain to implement the independent headerLine result. -/
theorem accepted (g : Nat → Nat) (start finish : Nat)
    (good : HeadNameChecked.good g start (scan isTchar g start finish) finish) :
    headerLine g start finish=
      let k := scan isTchar g start finish
      if !allIn isFieldByte g (k+1) finish then HdrLine.bad 400
      else let vs := scan isOws g (k+1) finish; .ok k vs (trimEnd g vs finish) := by
  let k := scan isTchar g start finish
  change HeadNameChecked.good g start k finish at good
  change (if k=start ∨ finish≤k then HdrLine.bad 400 else if g k≠58 then HdrLine.bad 400 else _) = _
  have early : ¬(k=start ∨ finish≤k) := by obtain ⟨lower,upper,_⟩ := good;omega
  simp only [early,good.2.2,ne_eq,not_true_eq_false,ite_false]
end E5R.Thermostat.HeadNameSpec
