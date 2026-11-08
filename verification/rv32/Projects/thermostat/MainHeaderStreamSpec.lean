import Projects.thermostat.HttpRequestBytes
namespace E5R.Thermostat.MainHeaderStreamSpec
open E5R E5R.Thermostat HttpRequestSpec

structure Run where
  received : Nat
  input : List (BitVec 8)
  result : HeadR
  deriving DecidableEq, Repr

/-- Consume at most fuel stream bytes, stopping at the first completed parser
    result. Fuel exhaustion is a receive-wait boundary, not input arrival. -/
def consume (wire : Nat → BitVec 8) : Nat → List (BitVec 8) → Run
  | 0,input => ⟨0,input,.incomplete⟩
  | fuel+1,input =>
    let next := input++[wire input.length]
    match HttpRequestBytes.parse next 1024 1024 with
    | .incomplete => let r := consume wire fuel next;{ r with received := r.received+1 }
    | .reject status => ⟨1,next,.reject status⟩
    | .done h => ⟨1,next,.done h⟩

def arrivals (wire : Nat → BitVec 8) (first count : Nat) := (List.range count).map (fun i => wire (first+i))

theorem arrivals_succ (wire : Nat → BitVec 8) (first count : Nat) :
    arrivals wire first (count+1)=wire first::arrivals wire (first+1) count := by
  rw [arrivals,List.range_succ_eq_map]
  simp only [List.map_cons,List.map_map,Function.comp_def,Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [show first+(i+1)=first+1+i by omega]

theorem received_le (wire : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8)) : (consume wire fuel input).received≤fuel := by
  induction fuel generalizing input with
  | zero => simp only [consume];omega
  | succ fuel ih =>
    rw [consume]
    dsimp only
    cases parsed : HttpRequestBytes.parse (input++[wire input.length]) 1024 1024 with
    | incomplete => exact Nat.succ_le_succ (ih _)
    | reject status => dsimp only;omega
    | done h => dsimp only;omega

theorem input_length (wire : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8)) :
    (consume wire fuel input).input.length=input.length+(consume wire fuel input).received := by
  induction fuel generalizing input with
  | zero => simp only [consume,Nat.add_zero]
  | succ fuel ih =>
    rw [consume]
    dsimp only
    cases parsed : HttpRequestBytes.parse (input++[wire input.length]) 1024 1024 with
    | incomplete =>
      have h := ih (input++[wire input.length])
      simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    | reject status => simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
    | done h => simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add]

theorem input_bytes (wire : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8)) :
    (consume wire fuel input).input=input++arrivals wire input.length (consume wire fuel input).received := by
  induction fuel generalizing input with
  | zero => simp only [consume,arrivals,List.range_zero,List.map_nil,List.append_nil]
  | succ fuel ih =>
    rw [consume]
    dsimp only
    cases parsed : HttpRequestBytes.parse (input++[wire input.length]) 1024 1024 with
    | incomplete =>
      have h := ih (input++[wire input.length])
      simpa only [arrivals_succ,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,List.append_assoc,List.singleton_append] using h
    | reject status => simp [arrivals]
    | done h => simp [arrivals]

theorem exhausted (wire : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8))
    (waiting : (consume wire fuel input).result=.incomplete) : (consume wire fuel input).received=fuel := by
  induction fuel generalizing input with
  | zero => rfl
  | succ fuel ih =>
    rw [consume] at waiting ⊢
    dsimp only at waiting ⊢
    cases parsed : HttpRequestBytes.parse (input++[wire input.length]) 1024 1024 with
    | incomplete =>
      rw [parsed] at waiting
      exact congrArg (fun n => n+1) (ih _ waiting)
    | reject status => rw [parsed] at waiting;cases waiting
    | done h => rw [parsed] at waiting;cases waiting

theorem exact_result (wire : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8))
    (initial : HttpRequestBytes.parse input 1024 1024=.incomplete) :
    (consume wire fuel input).result=HttpRequestBytes.parse (consume wire fuel input).input 1024 1024 := by
  induction fuel generalizing input with
  | zero => exact initial.symm
  | succ fuel ih =>
    rw [consume]
    dsimp only
    cases parsed : HttpRequestBytes.parse (input++[wire input.length]) 1024 1024 with
    | incomplete => exact ih _ parsed
    | reject status => exact parsed.symm
    | done h => exact parsed.symm

theorem complete_progress (wire : Nat → BitVec 8) (fuel : Nat) (input : List (BitVec 8))
    (initial : HttpRequestBytes.parse input 1024 1024=.incomplete)
    (complete : HttpRequestBytes.parse (input++arrivals wire input.length fuel) 1024 1024≠.incomplete) :
    (consume wire fuel input).result≠.incomplete := by
  intro waiting
  have count := exhausted wire fuel input waiting
  have bytes := input_bytes wire fuel input
  rw [count] at bytes
  have parsed := exact_result wire fuel input initial
  rw [bytes,waiting] at parsed
  exact complete parsed.symm
end E5R.Thermostat.MainHeaderStreamSpec
