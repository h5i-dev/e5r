import Projects.thermostat.Proof
import Projects.thermostat.Quiet
namespace E5R.Thermostat.MainMethodLengthMath
open E5R

theorem unsigned (n : Nat) (bound : n≤2048) : (BitVec.ofNat 32 n).toNat=n := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
theorem signed (n : Nat) (bound : n≤2048) : (BitVec.ofNat 32 n).toInt=Int.ofNat n := by
  rw [BitVec.toInt_eq_toNat_cond,unsigned n bound,ite_eq_left (show 2*n<2^32 by omega)]
  rfl

theorem ltTest (a b : Nat) (ha : a≤2048) (hb : b≤2048) :
    taken .lt (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a<b) := by
  change decide ((BitVec.ofNat 32 a).toInt<(BitVec.ofNat 32 b).toInt)=_
  rw [signed a ha,signed b hb]
  simp

theorem eqTest (a b : Nat) (ha : a≤2048) (hb : b≤2048) :
    taken .eq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a=b) := by
  have same : BitVec.ofNat 32 a=BitVec.ofNat 32 b ↔ a=b := by
    constructor
    · intro eq;have h := congrArg BitVec.toNat eq;simpa only [unsigned a ha,unsigned b hb] using h
    · intro eq;rw [eq]
  simp only [taken,Bool.beq_eq_decide_eq,same]

theorem neTest (a b : Nat) (ha : a≤2048) (hb : b≤2048) :
    taken .ne (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a≠b) := by
  change (!taken .eq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b))=_
  rw [eqTest a b ha hb,←decide_not]
end E5R.Thermostat.MainMethodLengthMath
