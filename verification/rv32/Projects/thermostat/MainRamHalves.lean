import Projects.thermostat.MainRamCopyByte
import Projects.thermostat.ResponseWordBytes
namespace E5R.Thermostat.MainRamHalves
open E5R E5R.Thermostat

/-- Actual little-endian low half of a RAM word known to fit16 bits. -/
theorem low (ram : Word → BitVec 8) (p v : Word) (word : ramRead ram p .w=v) (small : v.toNat<65536) :
    extend .h false (ramRead ram p .h)=v := by
  apply ResponseWordBytes.half ram p v small
  intro i
  have byte := MainRamCopyByte.read_byte ram p ⟨i.val,by have := i.isLt;omega⟩
  rw [word] at byte
  exact byte.symm

theorem high_byte (v : Word) (small : v.toNat<65536) (i : Fin 2) : byteOf v (2+i.val)=0#8 := by
  apply BitVec.eq_of_toNat_eq
  have index : i.val=0 ∨ i.val=1 := by have := i.isLt;omega
  rcases index with h|h <;> simp only [h,byteOf,BitVec.toNat_ofNat,Nat.reduceAdd,Nat.reducePow] <;> omega

/-- The upper RAM half is zero under either load extension, without alignment
    or source-code layout assumptions. Alignment is checked by each ELF load. -/
theorem high (ram : Word → BitVec 8) (p v : Word) (word : ramRead ram p .w=v) (small : v.toNat<65536) (signed : Bool) :
    extend .h signed (ramRead ram (p+2#32) .h)=0#32 := by
  have bytes (i : Fin 2) : ram ((p+2#32)+BitVec.ofNat 32 i.val)=0#8 := by
    have byte := MainRamCopyByte.read_byte ram p ⟨2+i.val,by have := i.isLt;omega⟩
    rw [word,high_byte v small i] at byte
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using byte.symm
  have b0 : ram (p+2#32)=0#8 := by simpa only [BitVec.add_zero] using bytes ⟨0,by decide⟩
  have b1 : ram ((p+2#32)+1)=0#8 := bytes ⟨1,by decide⟩
  rw [ramRead,b0,b1]
  cases signed <;> decide +kernel

theorem zero_low (ram : Word → BitVec 8) (p : Word) (word : ramRead ram p .w=0#32) (signed : Bool) :
    extend .h signed (ramRead ram p .h)=0#32 := by
  have b0 : ram p=0#8 := by
    have byte := MainRamCopyByte.read_byte ram p ⟨0,by decide⟩
    rw [word] at byte
    simpa only [BitVec.add_zero,show byteOf 0#32 0=0#8 by decide +kernel] using byte.symm
  have b1 : ram (p+1)=0#8 := by
    have byte := MainRamCopyByte.read_byte ram p ⟨1,by decide⟩
    rw [word] at byte
    simpa only [show (1 : Word)=1#32 by decide +kernel,show byteOf 0#32 1=0#8 by decide +kernel] using byte.symm
  rw [ramRead,b0,b1]
  cases signed <;> decide +kernel
end E5R.Thermostat.MainRamHalves
