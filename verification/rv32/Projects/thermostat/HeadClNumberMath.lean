import Projects.thermostat.DecimalMath
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadClNumberMath
open E5R E5R.Thermostat

def next (a : Nat) (b : BitVec 8) : Nat := 10*a+(b.toNat-48)

theorem digit_test : ∀ b : BitVec 8,
    taken .ltu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffc6#32) 255#32) 246#32= !(DecimalSpec.digit b) := by decide +kernel

theorem next_bound (a : Nat) (b : BitVec 8) (ha : a≤1024) (digit : DecimalSpec.digit b=true) : next a b≤10249 := by
  have hd : 48≤b.toNat ∧ b.toNat≤57 := by simpa only [DecimalSpec.digit,decide_eq_true_eq] using digit
  unfold next;omega

theorem mulhu_zero (a : Nat) (ha : a≤1024) : muldiv .mulhu (BitVec.ofNat 32 a) 10#32=0#32 := by
  change BitVec.ofNat 32 ((BitVec.ofNat 32 a).toNat*10/4294967296)=0#32
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega)]

theorem product (a : Nat) :
    alu .add (alu .sll (BitVec.ofNat 32 a) 1#32) (alu .sll (BitVec.ofNat 32 a) 3#32)=BitVec.ofNat 32 (10*a) := by
  change (BitVec.ofNat 32 a<<<1)+(BitVec.ofNat 32 a<<<3)=_
  rw [DecimalMath.shift_one,DecimalMath.shift_three,←BitVec.ofNat_add]
  congr 1;omega

theorem low (a : Nat) (b : BitVec 8) (digit : DecimalSpec.digit b=true) :
    alu .add (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32) 255#32) (BitVec.ofNat 32 (10*a))=
      BitVec.ofNat 32 (next a b) := by
  have hd : 48≤b.toNat ∧ b.toNat≤57 := by simpa only [DecimalSpec.digit,decide_eq_true_eq] using digit
  change ((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32)+BitVec.ofNat 32 (10*a)=_
  rw [BitVec.add_comm,DecimalMath.digit_sub b digit,DecimalMath.low_byte _ (by omega),←BitVec.ofNat_add]
  rfl

theorem carry_zero (a : Nat) (b : BitVec 8) (ha : a≤1024) (digit : DecimalSpec.digit b=true) :
    alu .sltu (BitVec.ofNat 32 (next a b)) (BitVec.ofNat 32 (10*a))=0#32 := by
  have hn := next_bound a b ha digit
  change (if (BitVec.ofNat 32 (next a b)).ult (BitVec.ofNat 32 (10*a)) then 1#32 else 0#32)=_
  have test : (BitVec.ofNat 32 (next a b)).ult (BitVec.ofNat 32 (10*a))=false := by
    rw [BitVec.ult,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : next a b<2^32),Nat.mod_eq_of_lt (by omega : 10*a<2^32)]
    simp only [show ¬next a b<10*a by unfold next;omega,decide_false]
  rw [test];rfl

theorem overflow_test (n : Nat) (hn : n≤10249) :
    taken .ne (alu .or (alu .sltu 1024#32 (BitVec.ofNat 32 n)) (alu .sltu (0 : Word) 0#32)) (0 : Word)=decide (1024<n) := by
  have test : (1024#32).ult (BitVec.ofNat 32 n)=decide (1024<n) := by
    change decide (1024<(BitVec.ofNat 32 n).toNat)=decide (1024<n)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  change decide ((if (1024#32).ult (BitVec.ofNat 32 n) then 1#32 else 0#32) ||| 0#32 ≠ 0#32)=_
  rw [test]
  by_cases more : 1024<n <;> simp only [more,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false] <;> decide +kernel
end E5R.Thermostat.HeadClNumberMath
