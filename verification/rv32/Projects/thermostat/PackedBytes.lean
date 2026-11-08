import Projects.thermostat.WireSpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PackedBytes
open E5R E5R.Thermostat

theorem byte_shift (v : Word) (i : Nat) : byteOf v i = (v >>> (8*i)).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) = 2^8 by decide,←Nat.pow_mul]

theorem byte_or (v w : Word) (i : Nat) : byteOf (v ||| w) i = byteOf v i ||| byteOf w i := by
  rw [byte_shift,byte_shift,byte_shift,BitVec.ushiftRight_or_distrib,BitVec.setWidth_or]

theorem shifted0 (v : Word) : byteOf (v <<< 16) 0 = 0#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change ((v.toNat*65536)%4294967296/1)%256 = 0
  omega

theorem shifted1 (v : Word) : byteOf (v <<< 16) 1 = 0#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change ((v.toNat*65536)%4294967296/256)%256 = 0
  omega

theorem shifted2 (v : Word) : byteOf (v <<< 16) 2 = byteOf v 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change ((v.toNat*65536)%4294967296/65536)%256 = (v.toNat/1)%256
  omega

theorem shifted3 (v : Word) : byteOf (v <<< 16) 3 = byteOf v 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change ((v.toNat*65536)%4294967296/16777216)%256 = (v.toNat/256)%256
  omega

theorem low0 (v : Word) : byteOf v 0 = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [byteOf,BitVec.toNat_setWidth]

theorem short0 (v : Word) : byteOf v 0 = Encoding.shortByte (v.setWidth 16) false := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,Encoding.shortByte,BitVec.toNat_ofNat,BitVec.toNat_setWidth,ite_false]
  change (v.toNat/1)%256 = (v.toNat%65536/1)%256
  omega

theorem short1 (v : Word) : byteOf v 1 = Encoding.shortByte (v.setWidth 16) true := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,Encoding.shortByte,BitVec.toNat_ofNat,BitVec.toNat_setWidth,ite_true]
  change (v.toNat/256)%256 = (v.toNat%65536/256)%256
  omega

/-- The decoder's packed numeric union is related to the existing kernel ABI.
    No assertion is made about inactive union bytes. -/
theorem numeric (report : Bool) (v : Word) :
    WireSpec.CommandWord ((if report then 1#32 else 0#32) ||| (v <<< 16))
      (if report then .reportTemp (v.setWidth 16) else .setpoint (v.setWidth 16)) := by
  intro i b hb
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  cases report <;> rcases hc with h|h|h|h
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,Encoding.commandByte,h,Encoding.commandTag] at hb
  all_goals try contradiction
  all_goals have he := Option.some.inj hb;subst b
  all_goals simp only [h,byte_or,shifted0,shifted1,shifted2,shifted3]
  all_goals try simp [byteOf]
  all_goals first | simpa [byteOf] using short0 v | simpa [byteOf] using short1 v
end E5R.Thermostat.PackedBytes
