import Projects.thermostat.HeadScanMath
namespace E5R.Thermostat.HeadVersionMath
open E5R E5R.Thermostat

theorem offset (m te length : Nat) (hm : m<te) :
    BitVec.ofNat 32 (te-m-1)+(BitVec.ofNat 32 m-BitVec.ofNat 32 length)=
    BitVec.ofNat 32 (te-1)-BitVec.ofNat 32 length := by
  rw [BitVec.sub_eq_add_neg,←BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 32 (te-m-1)) (BitVec.ofNat 32 m),←BitVec.ofNat_add,←BitVec.sub_eq_add_neg]
  have eq : m+(te-m-1)=te-1 := by omega
  rw [eq]

theorem offset_nat (i length : Nat) (hi : i<length) (hlen : length≤2048) :
    (BitVec.ofNat 32 i-BitVec.ofNat 32 length).toNat=2^32-length+i := by
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i<2^32),Nat.mod_eq_of_lt (by omega : length<2^32)]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem guard (te length k : Nat) (ht : te+9≤length) (hlen : length≤2048) (hk : 3≤k ∧ k≤6) :
    taken .eq (BitVec.ofNat 32 (te-1)-BitVec.ofNat 32 length) (BitVec.ofNat 32 (2^32-k))=false := by
  have ne : BitVec.ofNat 32 (te-1)-BitVec.ofNat 32 length≠BitVec.ofNat 32 (2^32-k) := by
    intro eq
    have nat := congrArg BitVec.toNat eq
    rw [offset_nat (te-1) length (by omega) hlen,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at nat
    omega
  simpa [taken] using ne
end E5R.Thermostat.HeadVersionMath
