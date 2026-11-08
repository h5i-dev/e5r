import Projects.thermostat.DecimalDigits
import Projects.thermostat.DigitWordMath
namespace E5R.Thermostat.DigitSmallMath
open E5R E5R.Thermostat

theorem pairOffset (n : Nat) (hn : n < 100) : (BitVec.ofNat 32 n <<< 17) >>> 16 = BitVec.ofNat 32 (2*n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  change ((n%4294967296*131072)%4294967296)/65536 = (2*n)%4294967296
  omega

theorem previous (n : Nat) (hn : 1 ≤ n) (_hb : n ≤ 5) :
    BitVec.ofNat 32 n+0xffffffff#32 = BitVec.ofNat 32 (n-1) := by
  rw [show 0xffffffff#32 = -(1#32) by decide +kernel,←BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le n 1 (by omega) hn

theorem digit_nat (n : Nat) (hn : n < 10) : (DecimalDigits.digit n).toNat = 48+n := by
  simp only [DecimalDigits.digit,BitVec.toNat_ofNat]
  omega
end E5R.Thermostat.DigitSmallMath

namespace E5R.Thermostat.DigitSmallMath
open E5R E5R.Thermostat

theorem reciprocal100 (n : Nat) (hn : n < 10000) :
    ((BitVec.ofNat 32 (n/4))*5243#32) >>> 17 = BitVec.ofNat 32 (n/100) := by
  have h := DigitWordMath.quotient100 n hn
  change (((BitVec.ofNat 32 n <<< 16) >>> 18)*5243#32) >>> 17 = _ at h
  rw [DigitWordMath.shifted4 n (by omega)] at h
  exact h

theorem remainder100 (n : Nat) (hn : n < 10000) :
    (BitVec.ofNat 32 n)-(BitVec.ofNat 32 (n/100)*100#32) = BitVec.ofNat 32 (n%100) := by
  have hd := Nat.mod_add_div n 100
  rw [←BitVec.ofNat_mul,BitVec.ofNat_sub_ofNat_of_le n (n/100*100) (by omega) (by omega)]
  congr 1
  omega
end E5R.Thermostat.DigitSmallMath

namespace E5R.Thermostat.DigitSmallMath
open E5R E5R.Thermostat

theorem leading_nonzero (n : Nat) (hn : 0 < n) (hb : n < 10) :
    alu .sltu (alu .sll (BitVec.ofNat 32 n) 16#32) 1#32 = 0#32 := by
  have ht : ¬((BitVec.ofNat 32 n) <<< 16).ult 1#32 = true := by
    change ¬decide (((BitVec.ofNat 32 n) <<< 16).toNat < (1#32).toNat) = true
    simp only [decide_eq_true_eq,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
    omega
  change (if ((BitVec.ofNat 32 n) <<< 16).ult 1#32 then 1 else 0) = _
  rw [ite_eq_right ht];rfl
end E5R.Thermostat.DigitSmallMath

namespace E5R.Thermostat.DigitSmallMath
open E5R E5R.Thermostat

theorem reciprocal10000 (n : Nat) (hn : n ≤ 32768) :
    ((BitVec.ofNat 32 (n/16))*839#32) >>> 19 = BitVec.ofNat 32 (n/10000) := by
  have h := DigitWordMath.quotient10000 n hn
  change (((BitVec.ofNat 32 n <<< 16) >>> 20)*839#32) >>> 19 = _ at h
  rw [DigitWordMath.shifted16 n (by omega)] at h
  exact h

theorem remainder10000 (n : Nat) (hn : n ≤ 32768) :
    (BitVec.ofNat 32 n)-(BitVec.ofNat 32 (n/10000)*10000#32) = BitVec.ofNat 32 (n%10000) := by
  have hd := Nat.mod_add_div n 10000
  rw [←BitVec.ofNat_mul,BitVec.ofNat_sub_ofNat_of_le n (n/10000*10000) (by omega) (by omega)]
  congr 1
  omega

theorem pairIndexRaw (n : Nat) (hn : n < 10000) :
    (((BitVec.ofNat 32 (n/4))*5243#32) >>> 16) &&& 2046#32 = BitVec.ofNat 32 (2*(n/100)) := by
  have h := DigitWordMath.pair_index n hn
  change ((((BitVec.ofNat 32 n <<< 16) >>> 18)*5243#32) >>> 16) &&& 2046#32 = _ at h
  rw [DigitWordMath.shifted4 n (by omega)] at h
  exact h
end E5R.Thermostat.DigitSmallMath
