import Projects.thermostat.SharedResponseMemory
import Projects.thermostat.SharedResponseFlags
namespace E5R.Thermostat.SharedResponseFrame
open E5R E5R.Thermostat

theorem stores (ram : Word → BitVec 8) (sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used x : Word)
    (hf : ∀ i : Fin 753, x≠fp+BitVec.ofNat 32 i.val) (hs : ∀ i : Fin 24, x≠sp+BitVec.ofNat 32 i.val) :
    SharedResponseStore.memory ram sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used x=ram x := by
  unfold SharedResponseStore.memory
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨146+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨145+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨143+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hs ⟨20+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨142+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .h (by
    intro i
    have hi : i.val<2 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨140+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨136+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨132+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨128+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨124+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨112+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨108+i.val,by omega⟩)]

theorem flags (ram : Word → BitVec 8) (fp x : Word)
    (hf : ∀ i : Fin 753, x≠fp+BitVec.ofNat 32 i.val) : SharedResponseFlags.memory ram fp x=ram x := by
  unfold SharedResponseFlags.memory SharedResponseFlags.first
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨532+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨576+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨620+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨664+i.val,by omega⟩)]
end E5R.Thermostat.SharedResponseFrame
