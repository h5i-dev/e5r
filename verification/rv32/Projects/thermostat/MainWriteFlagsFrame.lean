import Projects.thermostat.MainWriteFlags
import Projects.thermostat.StoreBytes
import Projects.thermostat.WordZero
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.MainWriteFlags
open E5R E5R.Thermostat

theorem low (ram : Word → BitVec 8) (fp : Word) : ViewFrame.Region ram (memory ram fp) fp 532 := by
  intro i
  unfold memory
  change ramPut ram (fp+532#32) 1#8 (fp+BitVec.ofNat 32 i.val)=_
  apply ramPut_ne
  exact WordZero.offset_ne fp i.val 532 (by have := i.isLt;omega) (by decide) (by have := i.isLt;omega)

theorem frame (ram : Word → BitVec 8) (fp x : Word) (hf : ∀ i : Fin 753, x≠fp+BitVec.ofNat 32 i.val) : memory ram fp x=ram x := by
  exact StoreBytes.frame _ _ _ _ .b (by
    intro i
    have hi : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hf ⟨532+i.val,by omega⟩)
end E5R.Thermostat.MainWriteFlags
