import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadActionSpec
open E5R E5R.Thermostat HttpRequestSpec

/-- Factor the existing independent addHeader rule at the emitted boundary
    between flag/value updates and the common header-array append. -/
def action (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor maxBody : Nat) : Added :=
  let kind := classify g ns ne
  if kind=1 then
    if f.host then .bad 400 else .ok {f with host := true}
  else if kind=2 then
    if f.hasCl ∨ f.te ∨ ve≠le then .bad 400 else
    match contentLength g vs ve maxBody with
    | .bad status => .bad status
    | .ok value => .ok {f with hasCl := true, cl := value}
  else if kind=3 then
    if minor=0 ∨ f.te ∨ f.hasCl ∨ ve≠le then .bad 400
    else if !eqCi g vs ve litChunked then .bad 501
    else .ok {f with te := true}
  else .ok f

def append (old : Fields) (entry : Field) : Added → Added
  | .bad status => .bad status
  | .ok f => .ok {f with headers := old.headers++[entry]}

theorem factor (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor maxBody : Nat) :
    addHeader g f ns ne vs ve le minor maxBody=
      (if maxHeaders≤f.headers.length then .bad 431
       else append f ⟨ns,ne,vs,ve⟩ (action g f ns ne vs ve le minor maxBody)) := by
  by_cases full : maxHeaders≤f.headers.length
  · simp only [addHeader,full,ite_true]
  · simp only [addHeader,full,ite_false]
    unfold action
    by_cases host : classify g ns ne=1
    · simp only [host,ite_true]
      cases f.host <;> rfl
    · simp only [host,ite_false]
      by_cases cl : classify g ns ne=2
      · simp only [cl,ite_true]
        by_cases bad : f.hasCl ∨ f.te ∨ ve≠le
        · simp only [bad,ite_true];rfl
        · simp only [bad,ite_false]
          cases contentLength g vs ve maxBody <;> rfl
      · simp only [cl,ite_false]
        by_cases te : classify g ns ne=3
        · simp only [te,ite_true]
          by_cases bad : minor=0 ∨ f.te ∨ f.hasCl ∨ ve≠le
          · simp only [bad,ite_true];rfl
          · simp only [bad,ite_false]
            cases eqCi g vs ve litChunked <;> rfl
        · simp only [te,ite_false];rfl
end E5R.Thermostat.HeadActionSpec
