import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadClNumberBound
open E5R E5R.Thermostat HttpRequestSpec

theorem bound (g : Nat → Nat) (e max acc p v : Nat) (ha : acc≤max)
    (result : clLoop g e max acc p=.ok v) : v≤max := by
  rw [clLoop] at result
  split at result
  next inside =>
    split at result
    next invalid => cases result
    next numeric =>
      split at result
      next tooLarge => cases result
      next accepted =>
        exact bound g e max (acc*10+(g p-48)) (p+1) v (by omega) result
  next outside => cases result;exact ha
termination_by e-p
 decreasing_by omega
end E5R.Thermostat.HeadClNumberBound
