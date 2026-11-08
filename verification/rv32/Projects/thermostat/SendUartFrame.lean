import Projects.thermostat.UartWriteAll
namespace E5R.Thermostat.SendUartFrame
open E5R E5R.Thermostat

theorem prefixRegion {before after : Word → BitVec 8} {obj : Word} (h : ∀ x, (∀ i : Fin 41, x≠(obj+48#32)+BitVec.ofNat 32 i.val) → after x=before x) :
    ViewFrame.Region before after obj 48 := by
  intro i
  apply h _
  have hh := StoreWords.offsets obj 0 48 48 41 (by decide) (by decide) (by decide) i
  simpa only [BitVec.add_zero] using hh

theorem outside {before after : Word → BitVec 8} {obj : Word} (h : ∀ x, (∀ i : Fin 41, x≠(obj+48#32)+BitVec.ofNat 32 i.val) → after x=before x)
    (x : Word) (hx : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) : after x=before x := by
  apply h x
  intro i
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact hx ⟨48+i.val,by have := i.isLt;omega⟩
end E5R.Thermostat.SendUartFrame
