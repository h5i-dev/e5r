import Theories.Logic
namespace E5R.Thermostat.Infinite
open E5R

/-- An infinite original-platform execution with no device-write events.
    Logical transitions carry no physical timing or scheduler fairness claim. -/
def NoWrites (B : Board) (img : List Segment) (f : Nat → Machine) : Prop :=
  ∀ t, Step B img (f t) (f (t+1)) []

theorem prepend {B img n a b} (h : DetSteps B img n a b) :
    ∀ f : Nat → Machine, f 0 = b → NoWrites B img f →
      ∃ g : Nat → Machine, g 0 = a ∧ NoWrites B img g := by
  induction h with
  | refl => intro f h0 hf;exact ⟨f,h0,hf⟩
  | @step n a a1 b hs _ ih =>
    intro f h0 hf
    obtain ⟨g,hg0,hg⟩ := ih f h0 hf
    let out : Nat → Machine := fun t => match t with | 0 => a | k+1 => g k
    refine ⟨out,rfl,?_⟩
    intro t
    cases t with
    | zero =>
      change Step B img a (g 0) []
      rw [hg0]
      exact hs.toStep
    | succ k => exact hg k

theorem reachable {B img a f} (h0 : f 0 = a) (hf : NoWrites B img f) :
    ∀ n, Reach B img (fun m => m = a) (f n) [] := by
  intro n
  induction n with
  | zero => exact .init h0
  | succ n ih => simpa using Reach.step ih (hf n)
end E5R.Thermostat.Infinite
