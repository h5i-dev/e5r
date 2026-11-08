import Theories.Logic
namespace E5R.Thermostat.HeadScanMath
open E5R

theorem next_word (j : Nat) : BitVec.ofNat 32 j+1#32=BitVec.ofNat 32 (j+1) := by
  rw [BitVec.ofNat_add]

theorem next_again (j n : Nat) (hj : j<n) (hn : n≤1024) :
    taken .ne (BitVec.ofNat 32 n) (BitVec.ofNat 32 j+1#32)=decide (j+1<n) := by
  rw [next_word]
  by_cases he : j+1<n
  · have words : BitVec.ofNat 32 n≠BitVec.ofNat 32 (j+1) := by
      intro hw
      have eq := congrArg BitVec.toNat hw
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n<2^32),
        Nat.mod_eq_of_lt (by omega : j+1<2^32)] at eq
      omega
    simp [taken,words,he]
  · have eq : n=j+1 := by omega
    rw [eq]
    simp [taken]
theorem next_full (j n : Nat) (hj : j<n) (hn : n≤1024) :
    taken .geu (BitVec.ofNat 32 j+1#32) (BitVec.ofNat 32 n)=decide (n≤j+1) := by
  rw [next_word]
  have jbound : j+1<2^32 := by omega
  have nbound : n<2^32 := by omega
  by_cases full : n≤j+1
  · have hnot : ¬j+1<n := by omega
    simp [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt jbound,Nat.mod_eq_of_lt nbound,full,hnot]
  · have hlt : j+1<n := by omega
    simp [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt jbound,Nat.mod_eq_of_lt nbound,full,hlt]
end E5R.Thermostat.HeadScanMath
