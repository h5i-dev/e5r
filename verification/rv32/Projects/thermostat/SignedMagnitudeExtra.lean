import Projects.thermostat.SignedMagnitude
import Projects.thermostat.ReplyJsonBounds
import Projects.thermostat.Arithmetic
namespace E5R.Thermostat.SignedMagnitude
open E5R E5R.Thermostat

theorem recover (v : BitVec 16) : ((input v) <<< 16).sshiftRight 16 = input v := by
  have hv := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight]
  simp only [BitVec.msb_eq_decide,shifted_nat,Nat.shiftRight_eq_div_pow]
  by_cases h : v.toNat < 32768
  · rw [decide_eq_false (show ¬2^(32-1) ≤ v.toNat*65536 by omega)]
    simp only [Bool.false_eq_true,ite_false,input_nat,ite_eq_left h];omega
  · rw [decide_eq_true (show 2^(32-1) ≤ v.toNat*65536 by omega)]
    simp only [ite_true,input_nat,ite_eq_right h];omega

theorem normalized (v : BitVec 16) :
    ((BitVec.ofNat 32 v.toInt.natAbs) <<< 16) >>> 16 = BitVec.ofNat 32 v.toInt.natAbs := by
  have hn := ReplyJsonBounds.magnitude v
  apply BitVec.eq_of_toNat_eq
  rw [Arithmetic.trunc16]
  simp only [BitVec.toNat_ofNat]
  omega
end E5R.Thermostat.SignedMagnitude

namespace E5R.Thermostat.SignedMagnitude
open E5R E5R.Thermostat

theorem zero_iff (v : BitVec 16) : input v = 0#32 ↔ v.toInt.natAbs = 0 := by
  have hv := v.isLt
  have hi := input_nat v
  have hm := magnitude v
  constructor
  · intro h
    have hz := congrArg BitVec.toNat h
    by_cases hn : v.toNat < 32768
    · rw [ite_eq_left hn] at hi hm
      change (input v).toNat = 0 at hz
      omega
    · rw [ite_eq_right hn] at hi hm
      change (input v).toNat = 0 at hz
      omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    by_cases hn : v.toNat < 32768
    · rw [ite_eq_left hn] at hi hm
      change (input v).toNat = 0
      omega
    · rw [ite_eq_right hn] at hi hm
      omega

theorem one_digit_leading (v : BitVec 16) (hn : v.toInt.natAbs < 10) :
    alu .and (alu .sltu (alu .sll (BitVec.ofNat 32 v.toInt.natAbs) 16#32) 1#32)
      (alu .sltu 0#32 (input v)) = 0#32 := by
  by_cases hz : v.toInt.natAbs = 0
  · have hi := (zero_iff v).mpr hz
    simp only [hz,hi,alu]
    decide +kernel
  · have ha : ¬((BitVec.ofNat 32 v.toInt.natAbs) <<< 16).ult 1#32 = true := by
      change ¬decide (((BitVec.ofNat 32 v.toInt.natAbs) <<< 16).toNat < (1#32).toNat) = true
      simp only [decide_eq_true_eq,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
      omega
    change (if ((BitVec.ofNat 32 v.toInt.natAbs) <<< 16).ult 1#32 then 1 else 0) &&& _ = _
    rw [ite_eq_right ha]
    exact BitVec.zero_and
end E5R.Thermostat.SignedMagnitude

namespace E5R.Thermostat.SignedMagnitude
open E5R E5R.Thermostat

def negative (v : BitVec 16) : Word := if v.toNat < 32768 then 0#32 else 1#32
def positive (v : BitVec 16) : Word := if v.toNat < 32768 then 1#32 else 0#32

theorem sign_bit (v : BitVec 16) : (input v) >>> 31 = negative v := by
  have hv := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,input_nat]
  simp only [Nat.shiftRight_eq_div_pow]
  by_cases h : v.toNat < 32768
  · rw [ite_eq_left h]
    simp only [negative,ite_eq_left h,BitVec.toNat_ofNat];omega
  · rw [ite_eq_right h]
    simp only [negative,ite_eq_right h,BitVec.toNat_ofNat];omega

theorem sign_flip (v : BitVec 16) : (negative v) ^^^ 1#32 = positive v := by
  unfold negative positive
  by_cases h : v.toNat < 32768
  · simp only [ite_eq_left h];decide +kernel
  · simp only [ite_eq_right h];decide +kernel
end E5R.Thermostat.SignedMagnitude

namespace E5R.Thermostat.SignedMagnitude
open E5R E5R.Thermostat

theorem nonzero_test (v : BitVec 16) (hn : v.toInt.natAbs ≠ 0) : alu .sltu 0#32 (input v) = 1#32 := by
  have hne : input v ≠ 0#32 := fun he => hn ((zero_iff v).mp he)
  have hz : (input v).toNat ≠ 0 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    exact h
  have ht : (0#32).ult (input v) = true := by
    change decide (0 < (input v).toNat) = true
    exact decide_eq_true (by omega)
  change (if (0#32).ult (input v) then 1 else 0) = _
  rw [ht];rfl
end E5R.Thermostat.SignedMagnitude
