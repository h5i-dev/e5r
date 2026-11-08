import Projects.thermostat.MainHeaderStreamSpec
set_option autoImplicit false
namespace E5R.Thermostat.MainHeaderStreamSpec
open E5R E5R.Thermostat

/-- A request head cannot depend on bytes beyond its receive budget. Used to
    share accepted heads between valid and malformed command-body witnesses. -/
theorem consume_congr (left right : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8))
    (agree : ∀ k, input.length≤k → k<input.length+fuel → left k=right k) :
    consume left fuel input=consume right fuel input := by
  induction fuel generalizing input with
  | zero => rfl
  | succ fuel ih =>
    have byte := agree input.length (by omega) (by omega)
    simp only [consume,byte]
    cases parsed : HttpRequestBytes.parse (input++[right input.length]) 1024 1024 with
    | incomplete =>
      have same := ih (input++[right input.length]) (by
        intro k lower upper
        simp only [List.length_append,List.length_cons,List.length_nil] at lower upper
        exact agree k (by omega) (by omega))
      rw [same]
    | reject status => rfl
    | done head => rfl
end E5R.Thermostat.MainHeaderStreamSpec
