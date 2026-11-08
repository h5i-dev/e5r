import Projects.thermostat.EncodeReplyStart
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.EncodeReplyStart
open E5R E5R.Thermostat

theorem words (ram : Word → BitVec 8) (sp dst cap : Word) (c : Core) :
    ramRead (memory ram sp dst cap c) (sp+92#32) .w = c.get 1 ∧
    ramRead (memory ram sp dst cap c) (sp+8#32) .w = dst ∧
    ramRead (memory ram sp dst cap c) (sp+12#32) .w = cap ∧
    ramRead (memory ram sp dst cap c) (sp+16#32) .w = 0#32 := by
  refine ⟨?_ ,?_ ,?_ ,?_ ⟩
  · unfold memory saved
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 92 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 92 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 92 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory saved
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 8 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 8 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory saved
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 12 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory saved
    exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (sp dst cap : Word) (c : Core) (x : Word)
    (hx : ∀ i : Fin 96, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp dst cap c x = ram x := by
  unfold memory saved
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨16+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨12+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨8+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨92+i,by omega⟩)]
end E5R.Thermostat.EncodeReplyStart
