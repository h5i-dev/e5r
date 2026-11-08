import Projects.thermostat.HeadActionSpec
namespace E5R.Thermostat.HeadHeaderDecisionSpec
open E5R E5R.Thermostat HttpRequestSpec

def result (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor : Nat) : Added :=
  if 16≤f.headers.length then .bad 431 else HeadActionSpec.action g f ns ne vs ve le minor 1024

theorem action_headers (g : Nat → Nat) (f next : Fields) (ns ne vs ve le minor : Nat)
    (accepted : HeadActionSpec.action g f ns ne vs ve le minor 1024=.ok next) : next.headers=f.headers := by
  by_cases host : classify g ns ne=1
  · simp only [HeadActionSpec.action,host,ite_true] at accepted
    cases flag : f.host <;> simp only [flag,Bool.false_eq_true,ite_true,ite_false] at accepted
    · cases accepted;rfl
    · cases accepted
  · by_cases cl : classify g ns ne=2
    · by_cases bad : f.hasCl ∨ f.te ∨ ve≠le
      · simp only [HeadActionSpec.action,host,cl,bad,ite_false,ite_true] at accepted
        cases accepted
      · cases number : contentLength g vs ve 1024 with
        | bad status =>
          simp only [HeadActionSpec.action,host,cl,bad,number,ite_false,ite_true] at accepted
          cases accepted
        | ok value =>
          simp only [HeadActionSpec.action,host,cl,bad,number,ite_false,ite_true] at accepted
          cases accepted;rfl
    · by_cases te : classify g ns ne=3
      · by_cases bad : minor=0 ∨ f.te ∨ f.hasCl ∨ ve≠le
        · simp only [HeadActionSpec.action,host,cl,te,bad,ite_false,ite_true] at accepted
          cases accepted
        · cases coding : eqCi g vs ve litChunked <;>
            simp only [HeadActionSpec.action,host,cl,te,bad,coding,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at accepted
          · cases accepted
          · cases accepted;rfl
      · simp only [HeadActionSpec.action,host,cl,te,ite_false] at accepted
        cases accepted;rfl

theorem accepted (g : Nat → Nat) (f next : Fields) (ns ne vs ve le minor : Nat)
    (ok : result g f ns ne vs ve le minor=.ok next) : next.headers=f.headers ∧ next.headers.length<16 := by
  unfold result at ok
  split at ok
  next full => cases ok
  next room =>
    have headers := action_headers g f next ns ne vs ve le minor ok
    exact ⟨headers,by rw [headers];omega⟩

theorem addHeader (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor : Nat) :
    HttpRequestSpec.addHeader g f ns ne vs ve le minor 1024=
      HeadActionSpec.append f ⟨ns,ne,vs,ve⟩ (result g f ns ne vs ve le minor) := by
  rw [HeadActionSpec.factor]
  unfold result
  by_cases full : 16≤f.headers.length
  · simp only [show maxHeaders=16 by rfl,full,ite_true,HeadActionSpec.append]
  · simp only [show maxHeaders=16 by rfl,full,ite_false]
end E5R.Thermostat.HeadHeaderDecisionSpec
