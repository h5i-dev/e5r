import Projects.thermostat.DecimalSpec
import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
namespace E5R.Thermostat.DecimalMath
open E5R

theorem length_guard (n : Nat) (hn : n < 2^32) :
    taken .geu (BitVec.ofNat 32 n+0xfffffffa#32) 0xfffffffb#32 =
      decide (1 ≤ n ∧ n ≤ 5) := by
  simp only [taken]
  rw [BitVec.ult,BitVec.toNat_add,BitVec.toNat_ofNat]
  change (!decide ((n%4294967296+4294967290)%4294967296 < 4294967291)) = decide (1 ≤ n ∧ n ≤ 5)
  have hh : (n%4294967296+4294967290)%4294967296 < 4294967291 ↔ ¬(1 ≤ n ∧ n ≤ 5) := by omega
  simp only [hh,decide_not,Bool.not_not]

theorem digit_guard (b : BitVec 8) :
    taken .geu (BitVec.ofNat 32 b.toNat+0xffffffd0#32) 10#32 = !(DecimalSpec.digit b) := by
  have hb := b.isLt
  simp only [taken]
  rw [BitVec.ult,BitVec.toNat_add,BitVec.toNat_ofNat]
  change (!decide ((b.toNat%4294967296+4294967248)%4294967296 < 10)) = (!decide (48 ≤ b.toNat ∧ b.toNat ≤ 57))
  have hh : (b.toNat%4294967296+4294967248)%4294967296 < 10 ↔ (48 ≤ b.toNat ∧ b.toNat ≤ 57) := by omega
  simp only [hh]

theorem digit_sub (b : BitVec 8) (h : DecimalSpec.digit b = true) :
    BitVec.ofNat 32 b.toNat+0xffffffd0#32 = BitVec.ofNat 32 (b.toNat-48) := by
  have hb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by simpa [DecimalSpec.digit] using h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  change (b.toNat%4294967296+4294967248)%4294967296 = (b.toNat-48)%4294967296
  omega

theorem sign_zero (b : BitVec 8) :
    alu .sltu (BitVec.ofNat 32 b.toNat+0xffffffd3#32) 1#32 =
      (if b = 45#8 then 1#32 else 0#32) := by
  have hb := b.isLt
  have he : b = 45#8 ↔ b.toNat = 45 := by
    constructor
    · intro h;rw [h];rfl
    · intro h;apply BitVec.eq_of_toNat_eq;exact h
  change (if (BitVec.ofNat 32 b.toNat+0xffffffd3#32).ult 1#32 then 1#32 else 0#32) = _
  have hh : (BitVec.ofNat 32 b.toNat+0xffffffd3#32).ult 1#32 = decide (b = 45#8) := by
    rw [BitVec.ult,BitVec.toNat_add,BitVec.toNat_ofNat]
    change decide ((b.toNat%4294967296+4294967251)%4294967296 < 1) = _
    have hiff : (b.toNat%4294967296+4294967251)%4294967296 < 1 ↔ b = 45#8 := by rw [he];omega
    simp only [hiff]
  rw [hh];simp

theorem shift_one (a : Nat) : BitVec.ofNat 32 a <<< 1 = BitVec.ofNat 32 (2*a) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow,show BitVec.twoPow 32 1 = 2#32 by decide +kernel]
  rw [←BitVec.ofNat_mul,show a*2 = 2*a by omega]

theorem shift_three (a : Nat) : BitVec.ofNat 32 a <<< 3 = BitVec.ofNat 32 (8*a) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow,show BitVec.twoPow 32 3 = 8#32 by decide +kernel]
  rw [←BitVec.ofNat_mul,show a*8 = 8*a by omega]

theorem low_byte (n : Nat) (hn : n < 256) : BitVec.ofNat 32 n &&& 255#32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  change (n%4294967296 &&& 255) = n%4294967296
  rw [show (255 : Nat) = 2^8-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem accumulate (a : Nat) (b : BitVec 8) (hd : DecimalSpec.digit b = true) :
    ((BitVec.ofNat 32 a <<< 3)+(BitVec.ofNat 32 a <<< 1))+
      ((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32) =
        BitVec.ofNat 32 (10*a+(b.toNat-48)) := by
  have hb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by simpa [DecimalSpec.digit] using hd
  rw [shift_one,shift_three,digit_sub b hd,low_byte _ (by omega),←BitVec.ofNat_add,←BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 32) (by omega)


def signed (negative : Bool) (n : Nat) : Word := if negative then 0#32-BitVec.ofNat 32 n else BitVec.ofNat 32 n

theorem range_guard (negative : Bool) (n : Nat) (hn : n ≤ 99999) :
    alu .sltu ((32768#32+signed negative n) >>> 16) 1#32 =
      (if n ≤ (if negative then 32768 else 32767) then 1#32 else 0#32) := by
  have hh : ((32768#32+signed negative n) >>> 16).ult 1#32 =
      decide (n ≤ (if negative then 32768 else 32767)) := by
    rw [BitVec.ult,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    have hi : (32768#32+signed negative n).toNat / 2^16 < 1 ↔ n ≤ (if negative then 32768 else 32767) := by
      cases negative with
      | false =>
        simp only [signed,Bool.false_eq_true,ite_false]
        rw [BitVec.toNat_add,BitVec.toNat_ofNat]
        change (32768+n%4294967296)%4294967296/65536 < 1 ↔ n ≤ 32767
        omega
      | true =>
        simp only [signed,ite_true]
        rw [BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat]
        change (32768+(4294967296-n%4294967296+0)%4294967296)%4294967296/65536 < 1 ↔ n ≤ 32768
        omega
    change decide ((32768#32+signed negative n).toNat / 2^16 < 1) = _
    simp only [hi]
  change (if ((32768#32+signed negative n) >>> 16).ult 1#32 then 1#32 else 0#32) = _
  rw [hh]
  simp only [decide_eq_true_eq]

theorem signed_low (negative : Bool) (n : Nat) :
    (signed negative n).setWidth 16 = BitVec.ofInt 16 (if negative then -(Int.ofNat n) else Int.ofNat n) := by
  cases negative <;> simp [signed,BitVec.ofInt_neg,BitVec.setWidth_neg_of_le (by decide : 16 ≤ 32)]

end E5R.Thermostat.DecimalMath
