import Projects.thermostat.KernelCode

set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Arithmetic
open E5R

/-- The compiler's slli/srli pair truncates to the low sixteen bits. -/
theorem trunc16 (v : Word) : ((v <<< 16) >>> 16).toNat = v.toNat % 65536 := by
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  change (v.toNat * 65536 % 4294967296) / 65536 = v.toNat % 65536
  omega

def biased (dc : BitVec 16) : Word := ((dc.signExtend 32 + 0xfffffed3#32) <<< 16) >>> 16

/-- Independently stated 50..300 range, including every negative i16 value.
    This is the unsigned biased comparison emitted at the SetSetpoint arm. -/
theorem setpoint_range (dc : BitVec 16) :
    65285 ≤ (biased dc).toNat ↔ 50 ≤ dc.toInt ∧ dc.toInt ≤ 300 := by
  have hd := dc.isLt
  have hsign : dc.msb = true ↔ 32768 ≤ dc.toNat := by
    rw [BitVec.msb_eq_decide]
    change (decide (32768 ≤ dc.toNat) = true ↔ 32768 ≤ dc.toNat)
    simp only [decide_eq_true_eq]
  unfold biased
  rw [trunc16,BitVec.toNat_add,BitVec.toNat_signExtend,BitVec.toNat_setWidth]
  simp only [BitVec.toInt_eq_msb_cond]
  cases hm : dc.msb with
  | true =>
    have hs := hsign.mp hm
    simp [hm]
    omega
  | false =>
    have hs : dc.toNat < 32768 := by
      have hn : ¬dc.msb = true := by rw [hm]; decide
      have hn' : ¬32768 ≤ dc.toNat := fun hs => hn (hsign.mpr hs)
      omega
    simp [hm]
    omega

end E5R.Thermostat.Arithmetic
