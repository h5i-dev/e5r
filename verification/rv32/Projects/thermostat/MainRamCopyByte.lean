import Projects.thermostat.HeadRamCopyMemory
namespace E5R.Thermostat.MainRamCopyByte
open E5R E5R.Thermostat

/-- Every byte of an actual little-endian RAM word load, including the final
    byte. This is a proved RAM arithmetic fact, not a memcpy summary. -/
theorem read_byte (ram : Word → BitVec 8) (p : Word) (i : Fin 4) :
    byteOf (ramRead ram p .w) i.val=ram (p+BitVec.ofNat 32 i.val) := by
  have b0 := (ram p).isLt
  have b1 := (ram (p+1#32)).isLt
  have b2 := (ram (p+2#32)).isLt
  have b3 := (ram (p+3#32)).isLt
  have casesIndex : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by have := i.isLt;omega
  rcases casesIndex with h|h|h|h <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp only [h,byteOf,ramRead,BitVec.toNat_ofNat,BitVec.add_zero,Nat.reducePow,show (1 : Word)=1#32 by decide +kernel,show (2 : Word)=2#32 by decide +kernel,show (3 : Word)=3#32 by decide +kernel] <;> omega

/-- Byte-for-byte correspondence for the actual word-store sequence proved
    by the RAM copy loop. The source snapshot is the original RAM. -/
theorem copied (ram : Word → BitVec 8) (src dst : Word) (n : Nat) (i : Fin (4*n))
    (nowrap : dst.toNat+4*n<2^32) :
    AlignedCopyLoop.writes ram dst (HeadRamCopyMemory.snapshot ram src n) (dst+BitVec.ofNat 32 i.val)=
      ram (src+BitVec.ofNat 32 i.val) := by
  have index := i.isLt
  have whole : i.val/4<n := by omega
  have part : i.val%4<4 := Nat.mod_lt _ (by decide)
  have word := HeadRamCopyMemory.copied ram src dst n ⟨i.val/4,whole⟩ nowrap
  have byte := congrArg (fun w => byteOf w (i.val%4)) word
  rw [read_byte _ _ ⟨i.val%4,part⟩,read_byte _ _ ⟨i.val%4,part⟩] at byte
  have address (p : Word) : (p+BitVec.ofNat 32 (4*(i.val/4)))+BitVec.ofNat 32 (i.val%4)=p+BitVec.ofNat 32 i.val := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4*(i.val/4)+i.val%4=i.val by omega]
  simpa only [address] using byte
end E5R.Thermostat.MainRamCopyByte
