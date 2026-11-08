import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SignedMagnitude
open E5R E5R.Thermostat

def input (v : BitVec 16) : Word := v.signExtend 32
def sign (v : BitVec 16) : Word := if v.toNat < 32768 then 0#32 else 0xffffffff#32

theorem magnitude (v : BitVec 16) : v.toInt.natAbs = if v.toNat < 32768 then v.toNat else 65536-v.toNat := by
  have hv := v.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : v.toNat < 32768
  · rw [ite_eq_left (show 2*v.toNat < 2^16 by omega),ite_eq_left h]
    rfl
  · rw [ite_eq_right (show ¬2*v.toNat < 2^16 by omega),ite_eq_right h]
    have ha := Int.ofNat_natAbs_of_nonpos (show (v.toNat : Int)-(2^16 : Nat) ≤ 0 by omega)
    omega

theorem input_nat (v : BitVec 16) : (input v).toNat = if v.toNat < 32768 then v.toNat else v.toNat+4294901760 := by
  have hv := v.isLt
  simp only [input,BitVec.toNat_signExtend,BitVec.toNat_setWidth,BitVec.msb_eq_decide]
  by_cases h : v.toNat < 32768
  · rw [decide_eq_false (show ¬2^(16-1) ≤ v.toNat by omega)]
    simp only [Bool.false_eq_true,ite_false,ite_eq_left h];omega
  · rw [decide_eq_true (show 2^(16-1) ≤ v.toNat by omega)]
    simp only [ite_true,ite_eq_right h];omega

theorem shifted_nat (v : BitVec 16) : ((input v) <<< 16).toNat = v.toNat*65536 := by
  have hv := v.isLt
  rw [BitVec.toNat_shiftLeft,input_nat,Nat.shiftLeft_eq]
  by_cases h : v.toNat < 32768
  · rw [ite_eq_left h];change (v.toNat*65536)%4294967296 = v.toNat*65536;omega
  · rw [ite_eq_right h];change ((v.toNat+4294901760)*65536)%4294967296 = v.toNat*65536;omega

theorem sign_mask (v : BitVec 16) : ((input v) <<< 16).sshiftRight 31 = sign v := by
  have hv := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight]
  simp only [BitVec.msb_eq_decide,shifted_nat,Nat.shiftRight_eq_div_pow]
  by_cases h : v.toNat < 32768
  · rw [decide_eq_false (show ¬2^(32-1) ≤ v.toNat*65536 by omega)]
    simp only [Bool.false_eq_true,ite_false,sign,ite_eq_left h,BitVec.toNat_ofNat];omega
  · rw [decide_eq_true (show 2^(32-1) ≤ v.toNat*65536 by omega)]
    simp only [ite_true,sign,ite_eq_right h,BitVec.toNat_ofNat];omega

theorem absolute (v : BitVec 16) : ((input v) ^^^ sign v)-sign v = BitVec.ofNat 32 v.toInt.natAbs := by
  have hv := v.isLt
  by_cases h : v.toNat < 32768
  · simp only [sign,ite_eq_left h,BitVec.xor_zero,BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [input_nat,ite_eq_left h,magnitude,ite_eq_left h,BitVec.toNat_ofNat]
    omega
  · simp only [sign,ite_eq_right h]
    change ((input v) ^^^ BitVec.allOnes 32)-BitVec.allOnes 32 = _
    rw [BitVec.xor_allOnes,BitVec.sub_eq_add_neg,show -BitVec.allOnes 32 = 1#32 by decide +kernel,←BitVec.neg_eq_not_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg,input_nat,ite_eq_right h,magnitude,ite_eq_right h,BitVec.toNat_ofNat]
    omega
end E5R.Thermostat.SignedMagnitude
