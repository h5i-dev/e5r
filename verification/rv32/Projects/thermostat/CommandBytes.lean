import Projects.thermostat.PackedBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CommandBytes
open E5R E5R.Thermostat

def modeField (m : Spec.Mode) : Word := BitVec.ofNat 32 (Encoding.modeByte m).toNat <<< 8

theorem mode (payload : Word) (m : Spec.Mode) :
    WireSpec.CommandWord ((3#32 ||| modeField m) ||| (payload <<< 16)) (.mode m) := by
  intro i b hb
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  cases m <;> rcases hc with h|h|h|h
  all_goals simp only [Encoding.commandByte,Encoding.commandTag,h] at hb
  all_goals try contradiction
  all_goals have he := Option.some.inj hb;subst b
  all_goals simp only [h,PackedBytes.byte_or,PackedBytes.shifted0,PackedBytes.shifted1]
  all_goals simp [modeField,Encoding.modeByte,byteOf]

theorem shifted8_0 (v : Word) (hv : v.toNat < 256) : byteOf (v <<< 8) 0 = 0#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (v.toNat*256%4294967296/1)%256 = 0
  omega

theorem shifted8_1 (v : Word) (hv : v.toNat < 256) : byteOf (v <<< 8) 1 = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,BitVec.toNat_setWidth]
  change (v.toNat*256%4294967296/256)%256 = v.toNat%256
  omega

theorem shifted8_2 (v : Word) (hv : v.toNat < 256) : byteOf (v <<< 8) 2 = 0#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (v.toNat*256%4294967296/65536)%256 = 0
  omega

theorem relay (idx : Word) (hi : idx.toNat < 256) (on : Bool) :
    WireSpec.CommandWord ((2#32 ||| (idx <<< 8)) ||| ((if on then 1#32 else 0#32) <<< 16))
      (.relay (idx.setWidth 8) on) := by
  intro i b hb
  have hi' := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  cases on <;> rcases hc with h|h|h|h
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,Encoding.commandByte,Encoding.commandTag,h] at hb ⊢
  all_goals try contradiction
  all_goals have he := Option.some.inj hb;subst b
  all_goals simp only [PackedBytes.byte_or,PackedBytes.shifted0,PackedBytes.shifted1,PackedBytes.shifted2,
    shifted8_0 idx hi,shifted8_1 idx hi,shifted8_2 idx hi]
  all_goals simp [byteOf,Encoding.boolByte]
end E5R.Thermostat.CommandBytes
