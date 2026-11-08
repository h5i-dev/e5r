import Projects.thermostat.Spec
namespace E5R.Thermostat.DecimalSpec
open E5R

def digit (b : BitVec 8) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

def number : List (BitVec 8) → Nat → Nat
 | [], a => a
 | b::bs, a => number bs (10*a+(b.toNat-48))

/-- Independent byte grammar for the application's decimal parser. It does
    not trim, accept '+', or permit more than five digits after the sign. -/
def finish (negative : Bool) (digits : List (BitVec 8)) : Option (BitVec 16) :=
  if 1 ≤ digits.length ∧ digits.length ≤ 5 ∧ digits.all digit = true then
    let n := number digits 0
    if n ≤ (if negative then 32768 else 32767) then
      some (BitVec.ofInt 16 (if negative then -(Int.ofNat n) else Int.ofNat n))
    else none
  else none

def parse : List (BitVec 8) → Option (BitVec 16)
 | [] => none
 | b::bs => if b = 45#8 then finish true bs else finish false (b::bs)

theorem number_bound (digits : List (BitVec 8)) (h : digits.all digit = true) (a : Nat) :
    number digits a < 10^digits.length*(a+1) := by
  induction digits generalizing a with
  | nil => simp [number]
  | cons b bs ih =>
    have hd : digit b = true ∧ bs.all digit = true := by simpa only [List.all_cons,Bool.and_eq_true] using h
    have hb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by simpa only [digit,decide_eq_true_eq] using hd.1
    have hn : 10*a+(b.toNat-48)+1 ≤ 10*(a+1) := by omega
    have hi := ih hd.2 (10*a+(b.toNat-48))
    change number bs (10*a+(b.toNat-48)) < 10^(bs.length+1)*(a+1)
    exact Nat.lt_of_lt_of_le hi (by
      calc
        10^bs.length*(10*a+(b.toNat-48)+1) ≤ 10^bs.length*(10*(a+1)) := Nat.mul_le_mul_left _ hn
        _ = 10^(bs.length+1)*(a+1) := by rw [Nat.pow_succ,Nat.mul_assoc])

theorem short_bound (digits : List (BitVec 8)) (hg : digits.all digit = true) (hl : digits.length ≤ 5) :
    number digits 0 ≤ 99999 := by
  have hn := number_bound digits hg 0
  have hc : digits.length = 0 ∨ digits.length = 1 ∨ digits.length = 2 ∨ digits.length = 3 ∨ digits.length = 4 ∨ digits.length = 5 := by omega
  have hp : 10^digits.length ≤ 100000 := by
    rcases hc with h|h|h|h|h|h
    all_goals simp [h]
  omega

theorem minus_prefix (ds : List (BitVec 8)) : parse (45#8::ds) = finish true ds := by simp [parse]

theorem empty : parse [] = none := rfl
theorem bare_minus : parse [45#8] = none := by decide +kernel
theorem leading_plus : parse [43#8,49#8] = none := by decide +kernel
theorem high_positive : parse [51#8,50#8,55#8,54#8,55#8] = some (32767#16) := by decide +kernel
theorem positive_overflow : parse [51#8,50#8,55#8,54#8,56#8] = none := by decide +kernel
theorem low_negative : parse [45#8,51#8,50#8,55#8,54#8,56#8] = some (32768#16) := by decide +kernel
theorem negative_overflow : parse [45#8,51#8,50#8,55#8,54#8,57#8] = none := by decide +kernel
theorem six_digits : parse [48#8,48#8,48#8,48#8,48#8,48#8] = none := by decide +kernel
theorem embedded_space : parse [49#8,32#8,50#8] = none := by decide +kernel
theorem negative_zero : parse [45#8,48#8] = some (0#16) := by decide +kernel
end E5R.Thermostat.DecimalSpec
