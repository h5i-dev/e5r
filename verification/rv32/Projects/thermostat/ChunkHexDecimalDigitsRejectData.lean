import Projects.thermostat.ChunkHexDecimalDigitsReject
import Projects.thermostat.ChunkLayout
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkHexDecimalDigitsRejectData
open E5R E5R.Thermostat

theorem word0 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ramRead (ChunkHexDecimalDigitsReject.memory c ram src dst input limit) (dst+0#32) .w=extend .w true (ramRead ram (src+0#32) .w) := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.read_away _ dst _ 0 32 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 0 12 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 0 8 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 0 4 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word4 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ramRead (ChunkHexDecimalDigitsReject.memory c ram src dst input limit) (dst+4#32) .w=extend .w true (ramRead ram (src+4#32) .w) := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.read_away _ dst _ 4 32 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 4 12 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 4 8 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word8 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ramRead (ChunkHexDecimalDigitsReject.memory c ram src dst input limit) (dst+8#32) .w=extend .w true (ramRead ram (src+8#32) .w) := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.read_away _ dst _ 8 32 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 8 12 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word12 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ramRead (ChunkHexDecimalDigitsReject.memory c ram src dst input limit) (dst+12#32) .w=extend .w true (ramRead ram (src+12#32) .w) := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.read_away _ dst _ 12 32 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word16 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ramRead (ChunkHexDecimalDigitsReject.memory c ram src dst input limit) (dst+16#32) .w=extend .w true (ramRead ram (src+16#32) .w) := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.read_away _ dst _ 16 32 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 12 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 8 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 4 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 0 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 28 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 24 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 16 20 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word20 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ramRead (ChunkHexDecimalDigitsReject.memory c ram src dst input limit) (dst+20#32) .w=extend .w true (ramRead ram (src+20#32) .w) := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.read_away _ dst _ 20 32 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 20 12 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 20 8 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 20 4 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 20 0 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 20 28 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.read_away _ dst _ 20 24 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem byte24 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ChunkHexDecimalDigitsReject.memory c ram src dst input limit (dst+24#32)=byteOf (extend .w true (ramRead ram (src+24#32) .w)) 0 := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [ChunkLayout.byte_away _ dst _ 24 32 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.byte_away _ dst _ 24 12 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.byte_away _ dst _ 24 8 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.byte_away _ dst _ 24 4 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.byte_away _ dst _ 24 0 .w (by decide) (by decide) (by decide)]
  rw [ChunkLayout.byte_away _ dst _ 24 28 .w (by decide) (by decide) (by decide)]
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem byte32 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ChunkHexDecimalDigitsReject.memory c ram src dst input limit (dst+32#32)=byteOf (alu .add (0x01900000#32) 0x00000003#32) 0 := by
  unfold ChunkHexDecimalDigitsReject.memory
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem byte33 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ChunkHexDecimalDigitsReject.memory c ram src dst input limit (dst+33#32)=byteOf (alu .add (0x01900000#32) 0x00000003#32) 1 := by
  unfold ChunkHexDecimalDigitsReject.memory
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem byte34 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ChunkHexDecimalDigitsReject.memory c ram src dst input limit (dst+34#32)=byteOf (alu .add (0x01900000#32) 0x00000003#32) 2 := by
  unfold ChunkHexDecimalDigitsReject.memory
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem byte35 (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :
    ChunkHexDecimalDigitsReject.memory c ram src dst input limit (dst+35#32)=byteOf (alu .add (0x01900000#32) 0x00000003#32) 3 := by
  unfold ChunkHexDecimalDigitsReject.memory
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem frame (c : Core) (ram : Word → BitVec 8) (src dst input limit x : Word)
    (hx : ∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) :
    ChunkHexDecimalDigitsReject.memory c ram src dst input limit x=ram x := by
  unfold ChunkHexDecimalDigitsReject.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨32+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨12+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨8+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨4+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨0+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨28+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨24+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨20+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨16+i.val,by have hi : i.val<4 := i.isLt;omega⟩)]
end E5R.Thermostat.ChunkHexDecimalDigitsRejectData
