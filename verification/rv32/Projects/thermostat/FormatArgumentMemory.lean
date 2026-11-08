import Projects.thermostat.FormatArgumentCall
import Projects.thermostat.ZeroHalf
namespace E5R.Thermostat.FormatArgumentCall
open E5R E5R.Thermostat

theorem words (ram : Word → BitVec 8) (sp obj : Word) :
    ramRead (memory ram sp obj) sp .w = obj ∧
    ramRead (memory ram sp obj) (sp+4#32) .w = 0x80005c04#32 ∧
    ramRead (memory ram sp obj) (sp+8#32) .w = 0x60000020#32 ∧
    ramRead (memory ram sp obj) (sp+12#32) .w = 0#32 := by
  refine ⟨?_,?_,?_,?_⟩
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (by simpa only [BitVec.add_zero] using Memory.word_disjoint sp 0 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (by simpa only [BitVec.add_zero] using Memory.word_disjoint sp 0 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (by simpa only [BitVec.add_zero] using Memory.word_disjoint sp 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 4 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 4 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 8 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · exact ramRead_ramWrite_w _ _ _

theorem width (ram : Word → BitVec 8) (sp obj : Word) : ramRead (memory ram sp obj) (sp+12#32) .h = 0#32 :=
  Memory.word_zero_half (words ram sp obj).2.2.2

theorem frame (ram : Word → BitVec 8) (sp obj x : Word)
    (hx : ∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp obj x = ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨12+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨8+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨4+i,by omega⟩)]
  exact ramWrite_w_other _ _ _ _ (fun i hi => hx ⟨i,by omega⟩)
end E5R.Thermostat.FormatArgumentCall
