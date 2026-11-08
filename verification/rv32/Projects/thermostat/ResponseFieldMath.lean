import Projects.thermostat.ResponseHeadSpec
import Projects.thermostat.ObservedByte
import Projects.thermostat.HttpPutMath
namespace E5R.Thermostat.ResponseFieldMath
open E5R E5R.Thermostat

def word (v : BitVec 8) : Word := v.setWidth 32

theorem nat (v : BitVec 8) : (word v).toNat=v.toNat := by
  simp only [word,BitVec.toNat_setWidth]
  have hv := v.isLt
  omega

theorem eq_iff (v : BitVec 8) (n : Nat) (hn : n<256) : word v=BitVec.ofNat 32 n ↔ v.toNat=n := by
  constructor
  · intro he
    have hh := congrArg BitVec.toNat he
    rw [nat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<2^32 by omega)] at hh
    exact hh
  · intro he
    apply BitVec.eq_of_toNat_eq
    rw [nat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<2^32 by omega),he]

theorem equal (v : BitVec 8) (n : Nat) (hn : n<256) : taken .eq (word v) (BitVec.ofNat 32 n)=decide (v.toNat=n) := by
  change decide (word v=BitVec.ofNat 32 n)=_
  simp only [eq_iff v n hn]

theorem not_equal (v : BitVec 8) (n : Nat) (hn : n<256) : taken .ne (word v) (BitVec.ofNat 32 n)=decide (v.toNat≠n) := by
  change (!taken .eq (word v) (BitVec.ofNat 32 n))=_
  rw [equal v n hn]
  simp only [decide_not]

theorem less (v : BitVec 8) (n : Nat) (hn : n<256) : taken .ltu (word v) (BitVec.ofNat 32 n)=decide (v.toNat<n) := by
  change decide ((word v).toNat<(BitVec.ofNat 32 n).toNat)=_
  rw [nat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<2^32 by omega)]

theorem normal {v : BitVec 8} (hf : ResponseHeadSpec.fieldByte v) (hn : v.toNat≠9) : 32≤v.toNat ∧ v.toNat≠127 := by
  rcases hf with h|h
  · exact False.elim (hn h)
  · exact h
theorem counter (n : Nat) (hp : 0<n) (hn : n≤16) :
    taken .eq (BitVec.ofNat 32 (n-1)) (0 : Word)=decide (n=1) := by
  by_cases he : n=1
  · subst n;decide +kernel
  · rw [HttpPutMath.zero_guard (n-1) (by omega) (by omega),decide_eq_false he]
end E5R.Thermostat.ResponseFieldMath
