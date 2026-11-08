import Projects.thermostat.MainChunkDataAppend
import Projects.thermostat.Marshal
namespace E5R.Thermostat.MainChunkDataMemory
open E5R E5R.Thermostat

theorem address (sp w : Word) : (sp+132#32)+w=sp+BitVec.ofNat 32 (132+w.toNat) := by
  rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]

theorem cursor (ram : Word → BitVec 8) (sp w r value : Word) :
    ramRead (MainChunkDataAppend.memory ram sp w r value) (sp+3660#32) .w=w+1#32 := by
  unfold MainChunkDataAppend.memory
  exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (sp w r value x : Word)
    (hb : x≠(sp+132#32)+w)
    (hc : ∀ i : Fin 4, x≠(sp+3660#32)+BitVec.ofNat 32 i.val) :
    MainChunkDataAppend.memory ram sp w r value x=ram x := by
  unfold MainChunkDataAppend.memory
  rw [StoreBytes.frame _ _ _ _ .w hc]
  exact ramPut_ne _ hb

theorem stored (ram : Word → BitVec 8) (sp w r value : Word) (hw : w.toNat<2048) :
    MainChunkDataAppend.memory ram sp w r value ((sp+132#32)+w)=byteOf value 0 := by
  unfold MainChunkDataAppend.memory
  rw [address]
  rw [FrameOffsets.byte _ sp _ (132+w.toNat) 3660 .w (by omega) (by decide) (by left;omega)]
  exact ramPut_eq _ _ _

theorem stored_byte (ram : Word → BitVec 8) (sp w r : Word) (b : BitVec 8) (hw : w.toNat<2048) :
    MainChunkDataAppend.memory ram sp w r (BitVec.ofNat 32 b.toNat) ((sp+132#32)+w)=b := by
  rw [stored _ _ _ _ _ hw]
  have hb := Marshal.byte_load (fun _ => b) 0#32
  simpa only [Memory.load_byte] using hb

theorem rx_other (ram : Word → BitVec 8) (sp w r value : Word) (k : Nat)
    (hw : w.toNat<2048) (hk : k<2048) (hne : k≠w.toNat) :
    MainChunkDataAppend.memory ram sp w r value ((sp+132#32)+BitVec.ofNat 32 k)=
      ram ((sp+132#32)+BitVec.ofNat 32 k) := by
  apply frame
  · have hn := FrameOffsets.ne sp 132 132 k w.toNat (by omega) (by omega) (by omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using hn
  · intro j
    exact FrameOffsets.ne sp 132 3660 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)

end E5R.Thermostat.MainChunkDataMemory
