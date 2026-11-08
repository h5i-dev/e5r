import Projects.thermostat.PackedBytes
import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireCallerBytes
open E5R E5R.Thermostat

theorem low_mask (w : Word) : w &&& 255#32 = BitVec.ofNat 32 (byteOf w 0).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change w.toNat &&& 255 = (w.toNat/1%256)%4294967296
  rw [show (255 : Nat) = 2^8-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shifted_byte (w : Word) (n k : Nat) : byteOf (w >>> (8*n)) k = byteOf w (n+k) := by
  rw [PackedBytes.byte_shift,PackedBytes.byte_shift]
  apply congrArg (fun v : Word => v.setWidth 8)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,←Nat.shiftRight_add]
  congr 1
  omega

def memory (ram : Word → BitVec 8) (p w : Word) : Word → BitVec 8 :=
  ramWrite (ramWrite (ramWrite ram (p+10#32) w .b) (p+11#32) (w >>> 8) .b) (p+12#32) (w >>> 16) .h

theorem bytes (ram : Word → BitVec 8) (p w : Word) (i : Fin 4) :
    memory ram p w ((p+10#32)+BitVec.ofNat 32 i.val) = byteOf w i.val := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hc with h|h|h|h
  all_goals simp only [memory,ramWrite,ramPut,BitVec.add_assoc,h]
  all_goals simp only [BitVec.add_right_inj]
  all_goals simp only [show 10#32+0#32 = 10#32 by decide,show 10#32+1#32 = 11#32 by decide,
    show 10#32+2#32 = 12#32 by decide,show 10#32+3#32 = 13#32 by decide,
    show 12#32+1#32 = 13#32 by decide]
  all_goals try simp only [BitVec.add_right_inj]
  all_goals simp
  all_goals first | rfl | exact shifted_byte w 1 0 | exact shifted_byte w 2 0 | exact shifted_byte w 2 1

theorem command (ram : Word → BitVec 8) (p w : Word) (cmd : Spec.Command) (h : WireSpec.CommandWord w cmd) :
    Encoding.CommandAt (memory ram p w) (p+10#32) cmd := by
  intro i b hb;rw [bytes];exact h i b hb

theorem frame (ram : Word → BitVec 8) (p w x : Word)
    (hx : ∀ i : Fin 4, x ≠ (p+10#32)+BitVec.ofNat 32 i.val) : memory ram p w x = ram x := by
  have h3 : (p+12#32)+1#32 = (p+10#32)+3#32 := by
    rw [BitVec.add_assoc,BitVec.add_assoc];rfl
  have h2 : p+12#32 = (p+10#32)+2#32 := by rw [BitVec.add_assoc];rfl
  have h1 : p+11#32 = (p+10#32)+1#32 := by rw [BitVec.add_assoc];rfl
  simp only [memory,ramWrite]
  rw [ramPut_ne _ (by change x ≠ (p+12#32)+1#32;rw [h3];exact hx ⟨3,by decide⟩),ramPut_ne _ (by rw [h2];exact hx ⟨2,by decide⟩),
    ramPut_ne _ (by rw [h1];exact hx ⟨1,by decide⟩)]
  exact ramPut_ne _ (by simpa only [BitVec.add_zero] using hx ⟨0,by decide⟩)
end E5R.Thermostat.WireCallerBytes
