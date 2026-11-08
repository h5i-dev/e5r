import Projects.thermostat.HeadMethodMath
namespace E5R.Thermostat.HeadTargetMath
open E5R E5R.Thermostat

theorem remaining (m j : Nat) (hm : m<j) (hj : j≤2048) :
    (~~~BitVec.ofNat 32 m)+BitVec.ofNat 32 j=BitVec.ofNat 32 (j-m-1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,BitVec.toNat_not]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : m<2^32),
    Nat.mod_eq_of_lt (by omega : j<2^32),Nat.mod_eq_of_lt (by omega : j-m-1<2^32)]
  have sum : 2^32-1-m+j=2^32+(j-m-1) := by omega
  rw [sum,Nat.add_mod]
  simp only [Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega : j-m-1<2^32)]

theorem geu (i j : Nat) (hi : i≤2048) (hj : j≤2048) :
    taken .geu (BitVec.ofNat 32 i) (BitVec.ofNat 32 j)=decide (j≤i) := by
  simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i<2^32),Nat.mod_eq_of_lt (by omega : j<2^32)]
  by_cases h : j≤i
  · have hn : ¬i<j := by omega
    simp only [h,hn,decide_true,decide_false,Bool.not_false]
  · have hn : i<j := by omega
    simp only [h,hn,decide_true,decide_false,Bool.not_true]
theorem current (m i : Nat) (hm : m<i) :
    BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)+1#32=BitVec.ofNat 32 i := by
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
  congr 1
  omega

theorem before (buf : Word) (m i : Nat) (hm : m<i) :
    buf+BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)=buf+BitVec.ofNat 32 (i-1) := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  omega

theorem offset_next (m i : Nat) (hm : m<i) :
    BitVec.ofNat 32 (i-m-1)+1#32=BitVec.ofNat 32 (i+1-m-1) := by
  rw [←BitVec.ofNat_add]
  congr 1
  omega

theorem remaining_next (i j : Nat) (hi : i<j) :
    BitVec.ofNat 32 (j-i)+0xffffffff#32=BitVec.ofNat 32 (j-(i+1)) := by
  have sum : j-i=(j-(i+1))+1 := by omega
  rw [sum,BitVec.ofNat_add,BitVec.add_assoc,
    show 1#32+0xffffffff#32=0#32 by decide +kernel,BitVec.add_zero]

theorem again (i j : Nat) (hi : i<j) (hj : j≤2048) :
    taken .ne (BitVec.ofNat 32 (j-(i+1))) (0 : Word)=decide (i+1<j) := by
  by_cases more : i+1<j
  · have nz := HeadMethodMath.nonzero (j-(i+1)) (by omega) (by omega)
    have words : BitVec.ofNat 32 (j-(i+1))≠(0 : Word) := by
      intro eq
      rw [eq] at nz
      contradiction
    have words' : BitVec.ofNat 32 (j-(i+1))≠0#32 := by
      simpa only [show (0 : Word)=0#32 by decide +kernel] using words
    simp [taken,words',more]
  · have zero : j-(i+1)=0 := by omega
    simp [zero,taken,more]
end E5R.Thermostat.HeadTargetMath
