import Projects.thermostat.SendFinish
import Projects.thermostat.WordRegions
namespace E5R.Thermostat.SendFinishData
open E5R E5R.Thermostat

theorem result_value (ram : Word → BitVec 8) (obj res io flag : Word) (hsep : WordRegions.Disjoint obj 89 res 8) :
    ramRead (SendFinish.memory ram obj res io flag) (res+0#32) .w=0xffffffff#32 := by
  unfold SendFinish.memory
  rw [StoreRead.other _ (res+0#32) (obj+45#32) (1#32) .w .b (by
    intro i j
    have hi : i.val<4 := i.isLt
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add]
    exact Ne.symm (hsep ⟨45+j.val,by have := j.isLt;omega⟩ ⟨0+i.val,by have := i.isLt;omega⟩))]
  rw [StoreRead.other _ (res+0#32) (res+4#32) (flag) .w .w (by
    intro i j
    have hi : i.val<4 := i.isLt
    have hj : j.val<4 := j.isLt
    exact StoreWords.offsets res 0 4 4 4 (by decide) (by decide) (by decide) i j)]
  exact ramRead_ramWrite_w _ _ _

theorem close_value (ram : Word → BitVec 8) (obj res io flag : Word) (hsep : WordRegions.Disjoint obj 89 res 8) :
    ramRead (SendFinish.memory ram obj res io flag) (res+4#32) .w=flag := by
  unfold SendFinish.memory
  rw [StoreRead.other _ (res+4#32) (obj+45#32) (1#32) .w .b (by
    intro i j
    have hi : i.val<4 := i.isLt
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add]
    exact Ne.symm (hsep ⟨45+j.val,by have := j.isLt;omega⟩ ⟨4+i.val,by have := i.isLt;omega⟩))]
  exact ramRead_ramWrite_w _ _ _

theorem done_value (ram : Word → BitVec 8) (obj res io flag : Word) (hsep : WordRegions.Disjoint obj 89 res 8) :
    SendFinish.memory ram obj res io flag (obj+45#32)=byteOf (1#32) 0 := by
  unfold SendFinish.memory
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _

theorem flush_value (ram : Word → BitVec 8) (obj res io flag : Word) (hsep : WordRegions.Disjoint obj 89 res 8) :
    SendFinish.memory ram obj res io flag (obj+52#32)=byteOf (1#32) 0 := by
  unfold SendFinish.memory
  rw [StoreBytes.frame _ (obj+45#32) (1#32) (obj+52#32) .b (by
    intro j
    have hj : j.val<1 := j.isLt
    have hh := StoreWords.offsets obj 52 1 45 1 (by decide) (by decide) (by decide) ⟨0,by decide⟩ j
    simpa only [BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (res+4#32) (flag) (obj+52#32) .w (by
    intro j
    have hj : j.val<4 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hsep ⟨52,by have := (by decide : 0<1);omega⟩ ⟨4+j.val,by have := j.isLt;omega⟩)]
  rw [StoreBytes.frame _ (res+0#32) (0xffffffff#32) (obj+52#32) .w (by
    intro j
    have hj : j.val<4 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hsep ⟨52,by have := (by decide : 0<1);omega⟩ ⟨0+j.val,by have := j.isLt;omega⟩)]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _

theorem frame (ram : Word → BitVec 8) (obj res io flag : Word) (x : Word)
    (ho : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) (hr : ∀ i : Fin 8, x≠res+BitVec.ofNat 32 i.val) :
    SendFinish.memory ram obj res io flag x=ram x := by
  unfold SendFinish.memory
  rw [StoreBytes.frame _ (obj+45#32) (1#32) x .b (by intro i;have hi : i.val<1 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨45+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (res+4#32) (flag) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hr ⟨4+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (res+0#32) (0xffffffff#32) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hr ⟨0+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+52#32) (1#32) x .b (by intro i;have hi : i.val<1 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨52+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+52#32) (0#32) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨52+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+48#32) (io) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨48+i.val,by omega⟩)]
end E5R.Thermostat.SendFinishData
