import Projects.thermostat.HeadScanMath
namespace E5R.Thermostat.HeadMethodMath
open E5R E5R.Thermostat

theorem nonzero (j : Nat) (hj : 0<j) (hn : j≤2048) : taken .eq (BitVec.ofNat 32 j) (0 : Word)=false := by
  have words : BitVec.ofNat 32 j≠(0 : Word) := by
    intro he
    have eq := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at eq
    change j=0 at eq
    omega
  simpa [taken] using words

theorem different (i n : Nat) (hi : i<n) (hn : n≤2048) :
    taken .eq (BitVec.ofNat 32 n) (BitVec.ofNat 32 i)=false := by
  have words : BitVec.ofNat 32 n≠BitVec.ofNat 32 i := by
    intro he
    have eq := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n<2^32),Nat.mod_eq_of_lt (by omega : i<2^32)] at eq
    omega
  simpa [taken] using words

theorem next_test (i j : Nat) (hi : i<j) (hj : j≤2048) :
    taken .eq (BitVec.ofNat 32 j) (BitVec.ofNat 32 i+1#32)=decide (i+1=j) := by
  rw [HeadScanMath.next_word]
  by_cases eq : i+1=j
  · rw [eq];simp [taken]
  · have lt : i+1<j := by omega
    simpa only [eq,decide_false] using different (i+1) j lt hj
end E5R.Thermostat.HeadMethodMath
