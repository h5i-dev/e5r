import Projects.thermostat.WordZero
set_option linter.unusedSimpArgs false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WordZero
open E5R E5R.Thermostat

theorem and_three (x : Word) : x &&& 3#32 = BitVec.ofNat 32 (x.toNat%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& 3 = (x.toNat%4)%4294967296
  rw [show (3 : Nat) = 2^2-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem neg_and_three (p : Word) (ha : p.toNat%4 = 0) : (0#32-p) &&& 3#32 = 0#32 := by
  rw [and_three]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,BitVec.toNat_sub]
  change ((0+4294967296-p.toNat)%4294967296%4)%4294967296 = 0
  have := p.isLt
  omega

theorem and_low_clear (x : Word) (ha : x.toNat%4 = 0) : x &&& 0xfffffffc#32 = x := by
  have hz : x &&& 3#32 = 0#32 := by rw [and_three,ha]
  have hh := congrArg (fun a : Word => x &&& a) (BitVec.or_not_self (3#32))
  simp only [BitVec.and_or_distrib_left,hz,BitVec.zero_or,BitVec.and_allOnes] at hh
  have he : ~~~(3#32) = 0xfffffffc#32 := by decide +kernel
  rw [he] at hh
  exact hh
end E5R.Thermostat.WordZero
