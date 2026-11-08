import Projects.thermostat.DecimalMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ParamMath
open E5R E5R.Thermostat

theorem digit_word (b : BitVec 8) :
    ((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32) = BitVec.ofNat 32 ((b.toNat+208)%256) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_add,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  change ((b.toNat%4294967296+4294967248)%4294967296 &&& 255) = ((b.toNat+208)%256)%4294967296
  rw [show (255 : Nat) = 2^8-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem digit_guard (b : BitVec 8) :
    taken .geu ((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32) 10#32 = !DecimalSpec.digit b := by
  have hb := b.isLt
  rw [digit_word]
  simp only [taken]
  rw [BitVec.ult,BitVec.toNat_ofNat]
  change (!decide (((b.toNat+208)%256)%4294967296 < 10)) = (!DecimalSpec.digit b)
  have hi : ((b.toNat+208)%256)%4294967296 < 10 ↔ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by omega
  simp only [hi,DecimalSpec.digit]

theorem digit_value (b : BitVec 8) (hd : DecimalSpec.digit b = true) :
    ((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32) = BitVec.ofNat 32 (b.toNat-48) := by
  have hb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by simpa only [DecimalSpec.digit,decide_eq_true_eq] using hd
  rw [digit_word,show (b.toNat+208)%256 = b.toNat-48 by omega]

theorem length_guard (n : Nat) (hn : n < 2^32) :
    taken .ltu 0xfffffff5#32 (BitVec.ofNat 32 n+0xfffffff5#32) = decide (1 ≤ n ∧ n ≤ 10) := by
  simp only [taken]
  rw [BitVec.ult,BitVec.toNat_add,BitVec.toNat_ofNat]
  change decide (4294967285 < (n%4294967296+4294967285)%4294967296) = _
  have hi : 4294967285 < (n%4294967296+4294967285)%4294967296 ↔ 1 ≤ n ∧ n ≤ 10 := by omega
  simp only [hi]

theorem mulhu_ten (a : Nat) (ha : a < 2^32) :
    muldiv .mulhu (BitVec.ofNat 32 a) 10#32 = BitVec.ofNat 32 (10*a/4294967296) := by
  simp only [muldiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha]
  change BitVec.ofNat 32 (a*10/4294967296) = _
  rw [show a*10 = 10*a by omega]

/-- The actual unsigned add carry and MULHU produce the upper half of the
    widened decimal accumulator. This is ordinary checked word arithmetic. -/
theorem high_carry (a d : Nat) (ha : a < 2^32) (hd : d ≤ 9) :
    alu .sltu (BitVec.ofNat 32 (10*a+d)) (BitVec.ofNat 32 (10*a)) +
      muldiv .mulhu (BitVec.ofNat 32 a) 10#32 = BitVec.ofNat 32 ((10*a+d)/4294967296) := by
  rw [mulhu_ten a ha]
  have hlt : (BitVec.ofNat 32 (10*a+d)).ult (BitVec.ofNat 32 (10*a)) =
      decide ((10*a+d)%4294967296 < (10*a)%4294967296) := rfl
  unfold alu
  rw [hlt]
  by_cases hc : (10*a+d)%4294967296 < (10*a)%4294967296
  · have hdiv : (10*a+d)/4294967296 = 10*a/4294967296+1 := by omega
    simp only [decide_eq_true hc,ite_true]
    rw [hdiv,BitVec.ofNat_add,BitVec.add_comm]
    rfl
  · have hdiv : (10*a+d)/4294967296 = 10*a/4294967296 := by omega
    simp only [decide_eq_false hc,Bool.false_eq_true,ite_false]
    rw [hdiv]
    change (0 : Word)+BitVec.ofNat 32 (10*a/4294967296) = _
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add]

@[irreducible] def carry (a d : Nat) : Word :=
  alu .sltu (BitVec.ofNat 32 (10*a+d)) (BitVec.ofNat 32 (10*a))

theorem carry_add (a d : Nat) (ha : a < 2^32) (hd : d ≤ 9) :
    carry a d+BitVec.ofNat 32 (10*a/4294967296) = BitVec.ofNat 32 ((10*a+d)/4294967296) := by
  unfold carry
  simpa only [mulhu_ten a ha] using high_carry a d ha hd

theorem ten_shifts (a : Nat) : (BitVec.ofNat 32 a <<< 1)+(BitVec.ofNat 32 a <<< 3) = BitVec.ofNat 32 (10*a) := by
  rw [DecimalMath.shift_one,DecimalMath.shift_three,←BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 32) (by omega)

theorem decrement (n : Nat) (hn : 0 < n) : BitVec.ofNat 32 n+0xffffffff#32 = BitVec.ofNat 32 (n-1) := by
  have he : n = (n-1)+1 := by omega
  calc
    _ = (BitVec.ofNat 32 (n-1)+1#32)+0xffffffff#32 := by
      exact congrArg (fun x : Word => x+0xffffffff#32) (by rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 32) he)
    _ = _ := by rw [BitVec.add_assoc,show 1#32+0xffffffff#32 = 0#32 by decide +kernel,BitVec.add_zero]

theorem counter_branch (n : Nat) (hn : 0 < n) (hb : n < 2^32) :
    taken .ne (BitVec.ofNat 32 (n-1)) (0 : Word) = decide (n ≠ 1) := by
  change decide (BitVec.ofNat 32 (n-1) ≠ (0 : Word)) = _
  have he : BitVec.ofNat 32 (n-1) = (0 : Word) ↔ n = 1 := by
    constructor
    · intro h
      have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n-1 < 2^32 by omega)] at hh
      change n-1 = 0 at hh;omega
    · intro h;subst n;rfl
  simp only [ne_eq,he]


theorem ult (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    taken .ltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = decide (a < b) := by
  simp only [taken]
  rw [BitVec.ult,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

theorem difference (a b : Nat) (hb : b ≤ a) :
    BitVec.ofNat 32 a-BitVec.ofNat 32 b = BitVec.ofNat 32 (a-b) := by
  have he : a = (a-b)+b := by omega
  calc
    _ = (BitVec.ofNat 32 (a-b)+BitVec.ofNat 32 b)-BitVec.ofNat 32 b := by
      exact congrArg (fun x : Word => x-BitVec.ofNat 32 b) (by rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 32) he)
    _ = _ := BitVec.add_sub_cancel _ _

end E5R.Thermostat.ParamMath
