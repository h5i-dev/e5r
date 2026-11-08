import Projects.thermostat.Encoding
import Projects.thermostat.Memory
import Projects.thermostat.HeaterFrame

namespace E5R.Thermostat.Fields
open E5R E5R.Thermostat

def modeWord : Spec.Mode → Word
 | .off => 0 | .heat => 1 | .auto => 2

theorem mode_valid (m : Spec.Mode) : modeWord m = 0#32 ∨ modeWord m = 1#32 ∨ modeWord m = 2#32 := by
  cases m <;> simp [modeWord]

theorem short_load (ram : Word → BitVec 8) (p : Word) (v : BitVec 16)
    (h0 : ram p = Encoding.shortByte v false) (h1 : ram (p+1#32) = Encoding.shortByte v true) :
    extend .h true (ramRead ram p .h) = v.signExtend 32 := by
  apply congrArg (BitVec.signExtend 32)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  change ((ram p).toNat + 256*(ram (p+1#32)).toNat) % 4294967296 % 65536 = v.toNat
  rw [h0,h1]
  change ((v.toNat / 1) % 256 + 256*((v.toNat / 256) % 256)) % 4294967296 % 65536 = v.toNat
  have := v.isLt
  omega

theorem setpoint (ram : Word → BitVec 8) (p : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram p s) :
    extend .h true (ramRead ram (p+4#32) .h) = s.setpoint.signExtend 32 := by
  have h0 := hs ⟨4,by decide⟩
  have h1 := hs ⟨5,by decide⟩
  apply short_load
  · exact h0
  · simpa [BitVec.add_assoc,Encoding.snapshotByte] using h1

theorem temp (ram : Word → BitVec 8) (p : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram p s) :
    extend .h true (ramRead ram (p+6#32) .h) = s.temp.signExtend 32 := by
  have h0 := hs ⟨6,by decide⟩
  have h1 := hs ⟨7,by decide⟩
  apply short_load
  · exact h0
  · simpa [BitVec.add_assoc,Encoding.snapshotByte] using h1

theorem mode (ram : Word → BitVec 8) (p : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram p s) :
    extend .b false (ramRead ram (p+9#32) .b) = modeWord s.mode := by
  have h := hs ⟨9,by decide⟩
  change ram (p+9#32) = Encoding.modeByte s.mode at h
  rw [Memory.load_byte,h]
  cases s.mode <;> rfl

theorem unsigned_half_byte0 (ram : Word → BitVec 8) (p : Word) :
    byteOf (extend .h false (ramRead ram p .h)) 0 = ram p := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram p).isLt
  have h1 := (ram (p+1)).isLt
  simp only [byteOf,extend,ramRead,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (((ram p).toNat + 256*(ram (p+1)).toNat) % 4294967296 &&& 65535) / 1 % 256 = (ram p).toNat
  rw [show (65535 : Nat) = 2^16-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem unsigned_half_byte1 (ram : Word → BitVec 8) (p : Word) :
    byteOf (extend .h false (ramRead ram p .h)) 1 = ram (p+1) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram p).isLt
  have h1 := (ram (p+1)).isLt
  simp only [byteOf,extend,ramRead,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (((ram p).toNat + 256*(ram (p+1)).toNat) % 4294967296 &&& 65535) / 256 % 256 = (ram (p+1)).toNat
  rw [show (65535 : Nat) = 2^16-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem heater (m : Spec.Mode) (t sp : BitVec 16) :
    spec (modeWord m) (t.signExtend 32) (sp.signExtend 32) = if Spec.heater m t sp then 1 else 0 := by
  rw [spec_i16 _ (mode_valid m)]
  cases m <;> simp [modeWord,Spec.heater]

theorem signed_byte0 (v : BitVec 16) : byteOf (v.signExtend 32) 0 = Encoding.shortByte v false := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,Encoding.shortByte,BitVec.toNat_ofNat]
  rw [BitVec.toNat_signExtend,BitVec.toNat_setWidth]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  have := v.isLt
  split <;> omega

theorem signed_byte1 (v : BitVec 16) : byteOf (v.signExtend 32) 1 = Encoding.shortByte v true := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,Encoding.shortByte,BitVec.toNat_ofNat]
  rw [BitVec.toNat_signExtend,BitVec.toNat_setWidth]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  have := v.isLt
  split <;> omega

theorem mode_byte (m : Spec.Mode) : byteOf (modeWord m) 0 = Encoding.modeByte m := by
  cases m <;> decide +kernel

theorem bool_byte (b : Bool) : byteOf (if b then (1 : Word) else 0) 0 = Encoding.boolByte b := by
  cases b <;> decide +kernel

theorem half_store_load (ram : Word → BitVec 8) (p : Word) (v : BitVec 16) :
    extend .h true (ramRead (ramWrite ram p (v.signExtend 32) .h) p .h) = v.signExtend 32 := by
  apply short_load
  · have hn : p ≠ p+1#32 := by simp [BitVec.self_eq_add_right]
    simpa [ramWrite,ramPut,hn] using signed_byte0 v
  · simp [ramWrite,ramPut,signed_byte1]

end E5R.Thermostat.Fields
