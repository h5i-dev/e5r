import Projects.thermostat.Literal
namespace E5R.Thermostat.MemcmpSpec
open E5R E5R.Thermostat

def value : List (BitVec 8) → List (BitVec 8) → Word
  | [],_ => 0#32
  | _,[] => 0#32
  | a::as,b::bs => if a = b then value as bs else BitVec.ofNat 32 a.toNat-BitVec.ofNat 32 b.toNat

theorem zero_iff (xs ys : List (BitVec 8)) (hl : xs.length = ys.length) : value xs ys = 0#32 ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := by apply List.eq_nil_of_length_eq_zero;simpa only [List.length_nil] using hl.symm
    subst ys;simp [value]
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      rw [value]
      by_cases he : a = b
      · rw [ite_eq_left he,ih bs hlen];simp only [List.cons.injEq,he,true_and]
      · rw [ite_eq_right he,BitVec.sub_eq_iff_eq_add,BitVec.zero_add]
        simp only [Literal.byte_injective,List.cons.injEq,he,false_and]
end E5R.Thermostat.MemcmpSpec
