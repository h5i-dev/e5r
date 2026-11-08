import Projects.thermostat.SendLoad
import Projects.thermostat.StoreRead
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SendLoadData
open E5R E5R.Thermostat

theorem slot16 (ram : Word → BitVec 8) (obj tx io ctptr : Word) :
    ramRead (SendLoad.memory ram obj tx io ctptr) (obj+16#32) .w=io := by
  unfold SendLoad.memory
  rw [StoreRead.other _ (obj+16#32) (obj+4#32) (832#32) .w .w (StoreWords.offsets obj 16 4 4 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+16#32) (obj+0#32) (tx+192#32) .w .w (StoreWords.offsets obj 16 4 0 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot0 (ram : Word → BitVec 8) (obj tx io ctptr : Word) :
    ramRead (SendLoad.memory ram obj tx io ctptr) (obj+0#32) .w=tx+192#32 := by
  unfold SendLoad.memory
  rw [StoreRead.other _ (obj+0#32) (obj+4#32) (832#32) .w .w (StoreWords.offsets obj 0 4 4 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot4 (ram : Word → BitVec 8) (obj tx io ctptr : Word) :
    ramRead (SendLoad.memory ram obj tx io ctptr) (obj+4#32) .w=832#32 := by
  unfold SendLoad.memory
  exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (obj tx io ctptr : Word) (x : Word)
    (hx : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) : SendLoad.memory ram obj tx io ctptr x=ram x := by
  unfold SendLoad.memory
  rw [StoreBytes.frame _ (obj+4#32) (832#32) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨4+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+0#32) (tx+192#32) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨0+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+16#32) (io) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨16+i.val,by omega⟩)]
end E5R.Thermostat.SendLoadData
