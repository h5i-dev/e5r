import Projects.thermostat.UartWriteInputs
import Projects.thermostat.UartWriteRemaining
import Projects.thermostat.UartWriteActive
import Projects.thermostat.UartWriteTail
import Projects.thermostat.UartWriteReturn
import Projects.thermostat.StoreWords
set_option maxRecDepth 3000
namespace E5R.Thermostat.UartWriteMemory
open E5R E5R.Thermostat

theorem inputs_frame (ram : Word → BitVec 8) (obj io src len x : Word)
    (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : UartWriteInputs.memory ram obj io src len x=ram x := by
  unfold UartWriteInputs.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i;have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨12+i.val,by omega⟩)]

theorem remaining_frame (ram : Word → BitVec 8) (obj ptr len x : Word)
    (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : UartWriteRemaining.memory ram obj ptr len x=ram x := by
  unfold UartWriteRemaining.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i;have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨20+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i;have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨16+i.val,by omega⟩)]

theorem active_frame (ram : Word → BitVec 8) (obj io src len x : Word)
    (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : UartWriteActive.memory ram obj io src len x=ram x := by
  unfold UartWriteActive.memory
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨36+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i;have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨32+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i;have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨28+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i;have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨24+i.val,by omega⟩)]

theorem tail_frame (ram : Word → BitVec 8) (obj src len x : Word)
    (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : UartWriteTail.memory ram obj src len x=ram x := by
  unfold UartWriteTail.memory
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨36+i.val,by omega⟩)]

theorem returned_frame (ram : Word → BitVec 8) (obj x : Word)
    (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : UartWriteReturn.memory ram obj x=ram x := by
  unfold UartWriteReturn.memory
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨40+i.val,by omega⟩)]

theorem inputs_io (ram : Word → BitVec 8) (obj io src len : Word) :
    ramRead (UartWriteInputs.memory ram obj io src len) (obj+12#32) .w=io := by
  unfold UartWriteInputs.memory
  exact ramRead_ramWrite_w _ _ _

theorem remaining_io (ram : Word → BitVec 8) (obj ptr len : Word) :
    ramRead (UartWriteRemaining.memory ram obj ptr len) (obj+12#32) .w=ramRead ram (obj+12#32) .w := by
  unfold UartWriteRemaining.memory
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 12 4 20 4 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 12 4 16 4 (by decide) (by decide) (Or.inl (by decide)))]

theorem remaining_src (ram : Word → BitVec 8) (obj ptr len : Word) :
    ramRead (UartWriteRemaining.memory ram obj ptr len) (obj+16#32) .w=ptr := by
  unfold UartWriteRemaining.memory
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 16 4 20 4 (by decide) (by decide) (Or.inl (by decide)))]
  exact ramRead_ramWrite_w _ _ _

theorem remaining_len (ram : Word → BitVec 8) (obj ptr len : Word) :
    ramRead (UartWriteRemaining.memory ram obj ptr len) (obj+20#32) .w=len := by
  unfold UartWriteRemaining.memory
  exact ramRead_ramWrite_w _ _ _

theorem active_src (ram : Word → BitVec 8) (obj io src len : Word) :
    ramRead (UartWriteActive.memory ram obj io src len) (obj+16#32) .w=ramRead ram (obj+16#32) .w := by
  unfold UartWriteActive.memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 16 4 36 1 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 16 4 32 4 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 16 4 28 4 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 16 4 24 4 (by decide) (by decide) (Or.inl (by decide)))]

theorem active_len (ram : Word → BitVec 8) (obj io src len : Word) :
    ramRead (UartWriteActive.memory ram obj io src len) (obj+20#32) .w=ramRead ram (obj+20#32) .w := by
  unfold UartWriteActive.memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 20 4 36 1 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 20 4 32 4 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 20 4 28 4 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 20 4 24 4 (by decide) (by decide) (Or.inl (by decide)))]

end E5R.Thermostat.UartWriteMemory
