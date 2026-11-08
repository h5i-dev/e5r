import Projects.thermostat.TrimMath
import Projects.thermostat.HeaderSpec
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseTokenMath
open E5R E5R.Thermostat

theorem trim_length (xs : List (BitVec 8)) : (TrimMath.trim xs).length≤xs.length := by
  have a := TrimMath.left_length xs
  have b := TrimMath.left_length (TrimMath.left xs).reverse
  simpa only [TrimMath.trim,TrimMath.left,List.length_reverse] using Nat.le_trans b (by simpa only [List.length_reverse] using a)

theorem other_length (xs : List (BitVec 8)) (other : xs.length≠5) : HeaderSpec.same xs (WireSpec.ascii "close")=false := by
  unfold HeaderSpec.same
  apply decide_eq_false
  intro equal
  have sizes := congrArg List.length equal
  have size : xs.length=5 := by simpa only [List.length_map,show (WireSpec.ascii "close").length=5 by decide +kernel] using sizes
  exact other size

theorem notFive (n : Nat) (bound : n<2^32) : taken .ne (BitVec.ofNat 32 n) 5#32=decide (n≠5) := by
  change decide (BitVec.ofNat 32 n≠5#32)=_
  have equivalent : BitVec.ofNat 32 n=5#32 ↔ n=5 := by
    constructor
    · intro h
      have numeric := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] using numeric
    · intro h
      subst n
      rfl
  simp only [ne_eq,equivalent]
end E5R.Thermostat.MainCloseTokenMath
