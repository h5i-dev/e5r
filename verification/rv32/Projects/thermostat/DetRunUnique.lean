import Theories.Logic
namespace E5R.Thermostat.DetRunUnique
open E5R

/-- Deterministic certificates of the same length from the same machine have
    the same endpoint. This says nothing about whether device reads occurred. -/
theorem step {B img m a b} (h : DetStep B img m a) (k : DetStep B img m b) : a=b := by
  have eq : Result.ok a.core a.ram []=Result.ok b.core b.ram [] := (h (fun _ => 0#32)).symm.trans (k (fun _ => 0#32))
  cases a
  cases b
  cases eq
  rfl

theorem steps {B img n m a b} (h : DetSteps B img n m a) (k : DetSteps B img n m b) : a=b := by
  induction h generalizing b with
  | refl m => cases k;rfl
  | @step n start mid finish hs tail ih =>
    cases k with
    | @step _ _ mid' _ ks rest =>
      have eq := step hs ks
      cases eq
      exact ih rest
end E5R.Thermostat.DetRunUnique
