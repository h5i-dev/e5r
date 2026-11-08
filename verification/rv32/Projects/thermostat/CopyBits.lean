import Projects.thermostat.Memory
namespace E5R.Thermostat.CopyBits
open E5R E5R.Thermostat

theorem low2 (p : Word) : (p &&& 3#32).toNat = p.toNat%4 := by
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change p.toNat &&& 3 = p.toNat%4
  rw [show (3:Nat)=2^2-1 by decide,Nat.and_two_pow_sub_one_eq_mod]

theorem aligned (p : Word) (ha : p.toNat%4=0) : p &&& 3#32=0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [low2,ha];rfl

theorem neg_aligned (p : Word) (ha : p.toNat%4=0) : (0#32-p) &&& 3#32=0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [low2]
  simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
  have hp := p.isLt
  change ((0+4294967296-p.toNat)%4294967296)%4 = 0
  omega
end E5R.Thermostat.CopyBits
