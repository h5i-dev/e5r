import Projects.thermostat.WireSpec
namespace E5R.Thermostat.AuthSpec
open E5R E5R.Thermostat

/-- Byte OR/XOR accumulation, with no early exit on unequal bytes. -/
def diff : List (BitVec 8) → List (BitVec 8) → BitVec 8 → BitVec 8
  | [],_,a => a
  | _,[],a => a
  | x::xs,y::ys,a => diff xs ys (a ||| (x ^^^ y))

theorem diff_zero (xs ys : List (BitVec 8)) (a : BitVec 8) (hl : xs.length = ys.length) :
    diff xs ys a = 0#8 ↔ a = 0#8 ∧ xs = ys := by
  induction xs generalizing ys a with
  | nil =>
    have hy : ys = [] := by apply List.eq_nil_of_length_eq_zero;simpa only [List.length_nil] using hl.symm
    subst ys;simp only [diff,and_true]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      rw [diff,ih ys _ ht]
      simp only [BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,List.cons.injEq,and_assoc]

/-- Lookup/prefix are byte operations; the actual header implementation must
    later establish the selected first value and exact Bearer prefix. -/
def token (header : Option (List (BitVec 8))) : Option (List (BitVec 8)) := do
  let h ← header
  if (WireSpec.ascii "Bearer ").isPrefixOf h then some (h.drop 7) else none

def authorized (header : Option (List (BitVec 8))) (key : List (BitVec 8)) : Bool :=
  match token header with
  | none => false
  | some t => decide (t = key)

theorem token_good : token (some (WireSpec.ascii "Bearer dev-key")) = some (WireSpec.ascii "dev-key") := by decide +kernel
theorem bad_case : authorized (some (WireSpec.ascii "bearer dev-key")) (WireSpec.ascii "dev-key") = false := by decide +kernel
end E5R.Thermostat.AuthSpec
