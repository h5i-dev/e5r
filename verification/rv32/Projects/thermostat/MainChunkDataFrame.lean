import Projects.thermostat.MainChunkDataMemory
import Projects.thermostat.ChunkStateFrame
import Projects.thermostat.AppState
import Projects.thermostat.MainChunkLayout
namespace E5R.Thermostat.MainChunkDataFrame
open E5R E5R.Thermostat HttpRequestSpec

theorem state_region (ram : Word → BitVec 8) (sp w r value : Word) (hw : w.toNat<2048) :
    ViewFrame.Region ram (MainChunkDataAppend.memory ram sp w r value) (sp+3680#32) 25 := by
  intro i
  apply MainChunkDataMemory.frame
  · have h := FrameOffsets.ne sp 3680 132 i.val w.toNat (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h
  · intro j
    exact FrameOffsets.ne sp 3680 3660 i.val j.val (by have := i.isLt;omega)
      (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem state {ram sp w r value s} (hw : w.toNat<2048) (hs : ChunkLayout.At ram (sp+3680#32) s) :
    ChunkLayout.At (MainChunkDataAppend.memory ram sp w r value) (sp+3680#32) s :=
  ChunkStateFrame.preserve hs (state_region ram sp w r value hw)

theorem read_cursor (ram : Word → BitVec 8) (sp w r value : Word) (hw : w.toNat<2048) :
    ramRead (MainChunkDataAppend.memory ram sp w r value) (sp+3656#32) .w=ramRead ram (sp+3656#32) .w := by
  apply ramRead_w_congr
  intro k hk
  apply MainChunkDataMemory.frame
  · have h := FrameOffsets.ne sp 3656 132 k w.toNat (by omega) (by omega) (by omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h
  · intro j
    exact FrameOffsets.ne sp 3656 3660 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem app (ram : Word → BitVec 8) (w r value : Word) (s : Spec.Snapshot)
    (hw : w.toNat<2048) (hs : AppState.At ram s) :
    AppState.At (MainChunkDataAppend.memory ram 0x80ffeb90#32 w r value) s := by
  apply AppState.preserve ram _ s hs
  intro i
  have base : 0x80ffebbc#32=0x80ffeb90#32+44#32 := by decide +kernel
  rw [base]
  apply MainChunkDataMemory.frame
  · have h := FrameOffsets.ne 0x80ffeb90#32 44 132 i.val w.toNat
      (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h
  · intro j
    exact FrameOffsets.ne 0x80ffeb90#32 44 3660 i.val j.val (by have := i.isLt;omega)
      (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem word (ram : Word → BitVec 8) (sp w r value : Word) (hw : w.toNat<2048)
    (off : Nat) (lo : 2180≤off) (hi : off+4≤3656) :
    ramRead (MainChunkDataAppend.memory ram sp w r value) (sp+BitVec.ofNat 32 off) .w=
      ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  apply ramRead_w_congr
  intro k hk
  apply MainChunkDataMemory.frame
  · have h := FrameOffsets.ne sp off 132 k w.toNat (by omega) (by omega) (by omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h
  · intro j
    exact FrameOffsets.ne sp off 3660 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem layout {ram sp w r value} (hw : w.toNat<2048) (h : MainChunkLayout.At ram sp) :
    MainChunkLayout.At (MainChunkDataAppend.memory ram sp w r value) sp :=
  MainChunkLayout.preserve h (fun off lo hi => word ram sp w r value hw off lo hi)

end E5R.Thermostat.MainChunkDataFrame
