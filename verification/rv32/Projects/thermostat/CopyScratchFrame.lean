import Projects.thermostat.CopyTwoExecute
import Projects.thermostat.CopyThreeExecute
namespace E5R.Thermostat.CopyScratchFrame
open E5R E5R.Thermostat

theorem initial_half (ram : Word → BitVec 8) (sp x : Word)
    (hx : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) : CopyInitData.halfRam ram sp x=ram x := by
  unfold CopyInitData.halfRam CopyUnalignedScratch.memory
  rw [StoreBytes.frame _ _ _ _ .h (by
    intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨14+i.val,by have := i.isLt;change i.val<2 at this;omega⟩)]
  apply StoreBytes.frame _ _ _ _ .w
  intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨12+i.val,by have := i.isLt;change i.val<4 at this;omega⟩

theorem initial_byte (ram : Word → BitVec 8) (sp x : Word)
    (hx : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) : CopyInitData.byteRam ram sp x=ram x := by
  unfold CopyInitData.byteRam CopyUnalignedScratch.memory
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨15+i.val,by have := i.isLt;change i.val<1 at this;omega⟩)]
  apply StoreBytes.frame _ _ _ _ .w
  intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨12+i.val,by have := i.isLt;change i.val<4 at this;omega⟩

theorem two (ram : Word → BitVec 8) (sp x : Word)
    (hx : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) : CopyTwoFinal.scratch ram sp x=ram x := by
  have h6 := hx ⟨6,by decide⟩
  have h8 := hx ⟨8,by decide⟩
  simp only [CopyTwoFinal.scratch,ramWrite,ramPut,if_neg h6,if_neg h8]

theorem three (ram : Word → BitVec 8) (sp x : Word)
    (hx : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) : CopyThreeFinal.scratch ram sp x=ram x := by
  have h6 := hx ⟨6,by decide⟩
  have h8 := hx ⟨8,by decide⟩
  simp only [CopyThreeFinal.scratch,ramWrite,ramPut,if_neg h6,if_neg h8]
end E5R.Thermostat.CopyScratchFrame
