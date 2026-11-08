import Projects.thermostat.HeadVersionSpec
namespace E5R.Thermostat.HeadRequestSuccess
open E5R E5R.Thermostat HttpRequestSpec

theorem shape (g : Nat → Nat) (j ms me ts te minor : Nat)
    (accepted : requestLine g 0 j=.ok ms me ts te minor) : ms=0 ∧ ts=me+1 ∧ minor≤1 := by
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
      next good =>
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
              have bound := HeadVersionSpec.version_le g (scan isTargetByte g (scan isTchar g 0 j+1) j+1) j
              exact ⟨rfl,rfl,by omega⟩
end E5R.Thermostat.HeadRequestSuccess
