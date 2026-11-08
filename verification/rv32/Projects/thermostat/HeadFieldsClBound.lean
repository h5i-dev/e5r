import Projects.thermostat.HeadClNumberBound
namespace E5R.Thermostat.HeadFieldsClBound
open E5R E5R.Thermostat HttpRequestSpec

theorem content (g : Nat → Nat) (s e max value : Nat)
    (accepted : contentLength g s e max=.ok value) : value≤max := by
  unfold contentLength at accepted
  split at accepted
  next empty => cases accepted
  next positive => exact HeadClNumberBound.bound g e max 0 s value (by omega) accepted

theorem add (g : Nat → Nat) (f nextFields : Fields) (ns ne vs ve le minor max : Nat)
    (bound : f.cl≤max) (accepted : addHeader g f ns ne vs ve le minor max=.ok nextFields) : nextFields.cl≤max := by
  unfold addHeader at accepted
  dsimp only at accepted
  split at accepted
  next full => cases accepted
  next room =>
    by_cases host : classify g ns ne=1
    · simp only [host,ite_true] at accepted
      cases flag : f.host <;> simp only [flag,Bool.false_eq_true,ite_false,ite_true] at accepted
      · cases accepted;exact bound
      · cases accepted
    · simp only [host,ite_false] at accepted
      by_cases cl : classify g ns ne=2
      · simp only [cl,ite_true] at accepted
        split at accepted
        next bad => cases accepted
        next good =>
          cases number : contentLength g vs ve max with
          | bad status => rw [number] at accepted;cases accepted
          | ok value =>
            rw [number] at accepted
            cases accepted
            exact content g vs ve max value number
      · simp only [cl,ite_false] at accepted
        by_cases te : classify g ns ne=3
        · simp only [te,ite_true] at accepted
          split at accepted
          next bad => cases accepted
          next good =>
            split at accepted
            next bad => cases accepted
            next good => cases accepted;exact bound
        · simp only [te,ite_false] at accepted
          cases accepted;exact bound

theorem fields (g : Nat → Nat) (cap minor max i : Nat) (f result : Fields) (len : Nat)
    (bound : f.cl≤max) (accepted : HttpRequestSpec.fields g cap minor max i f=.done result len) : result.cl≤max := by
  rw [HttpRequestSpec.fields] at accepted
  split at accepted
  next inside =>
    dsimp only at accepted
    split at accepted
    next more => cases accepted
    next notMore =>
      split at accepted
      next bad => cases accepted
      next notBad =>
        split at accepted
        next empty => cases accepted;exact bound
        next nonempty =>
          cases line : headerLine g i (lineEnd g i cap) with
          | bad status => rw [line] at accepted;cases accepted
          | ok ne vs ve =>
            rw [line] at accepted
            dsimp only at accepted
            cases added : addHeader g f i ne vs ve (lineEnd g i cap) minor max with
            | bad status => rw [added] at accepted;cases accepted
            | ok updated =>
              rw [added] at accepted
              exact fields g cap minor max ((lineEnd g i cap)+2) updated result len
                (add g f updated i ne vs ve (lineEnd g i cap) minor max bound added) accepted
  next outside => cases accepted
termination_by cap-i
 decreasing_by have := HttpRequestSpec.scan_ge notEol g i cap;unfold lineEnd at *;omega

theorem initialized (g : Nat → Nat) (cap minor i : Nat) (result : Fields) (len : Nat)
    (accepted : HttpRequestSpec.fields g cap minor 1024 i Fields.empty=.done result len) : result.cl≤1024 :=
  fields g cap minor 1024 i Fields.empty result len (by decide) accepted
end E5R.Thermostat.HeadFieldsClBound
