import Projects.thermostat.CopyBits
namespace E5R.Thermostat.CopyBits
open E5R E5R.Thermostat

/-- Low-bit scratch addressing used by actual memcpy ORs the source alignment
    into a word-aligned stack address. Derive the equivalent checked RAM offset. -/
theorem or_low (p : Word) (k : Nat) (ha : p.toNat%4=0) (hk : k<4) (hw : p.toNat+k<2^32) :
    p ||| BitVec.ofNat 32 k = p+BitVec.ofNat 32 k := by
  have he : p.toNat=4*(p.toNat/4) := by omega
  have ho : p.toNat ||| k=p.toNat+k := by
    rw [he]
    exact (Nat.two_pow_add_eq_or_of_lt (i := 2) (b := k) (by omega) (p.toNat/4)).symm
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or,BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k<2^32 by omega),ho,Nat.mod_eq_of_lt hw]
end E5R.Thermostat.CopyBits
