import Projects.thermostat.SendSave
import Projects.thermostat.StoreRead
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SendSaveData
open E5R E5R.Thermostat

theorem slot140 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+140#32) .w=c.get 1 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+140#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 140 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 140 4 112 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+116#32) (c.get 21) .w .w (StoreWords.offsets frame 140 4 116 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+120#32) (c.get 20) .w .w (StoreWords.offsets frame 140 4 120 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+124#32) (c.get 19) .w .w (StoreWords.offsets frame 140 4 124 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+128#32) (c.get 18) .w .w (StoreWords.offsets frame 140 4 128 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+132#32) (c.get 9) .w .w (StoreWords.offsets frame 140 4 132 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+140#32) (frame+136#32) (c.get 8) .w .w (StoreWords.offsets frame 140 4 136 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot136 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+136#32) .w=c.get 8 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+136#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 136 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+136#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 136 4 112 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+136#32) (frame+116#32) (c.get 21) .w .w (StoreWords.offsets frame 136 4 116 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+136#32) (frame+120#32) (c.get 20) .w .w (StoreWords.offsets frame 136 4 120 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+136#32) (frame+124#32) (c.get 19) .w .w (StoreWords.offsets frame 136 4 124 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+136#32) (frame+128#32) (c.get 18) .w .w (StoreWords.offsets frame 136 4 128 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+136#32) (frame+132#32) (c.get 9) .w .w (StoreWords.offsets frame 136 4 132 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot132 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+132#32) .w=c.get 9 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+132#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 132 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+132#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 132 4 112 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+132#32) (frame+116#32) (c.get 21) .w .w (StoreWords.offsets frame 132 4 116 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+132#32) (frame+120#32) (c.get 20) .w .w (StoreWords.offsets frame 132 4 120 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+132#32) (frame+124#32) (c.get 19) .w .w (StoreWords.offsets frame 132 4 124 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+132#32) (frame+128#32) (c.get 18) .w .w (StoreWords.offsets frame 132 4 128 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot128 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+128#32) .w=c.get 18 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+128#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 128 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+128#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 128 4 112 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+128#32) (frame+116#32) (c.get 21) .w .w (StoreWords.offsets frame 128 4 116 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+128#32) (frame+120#32) (c.get 20) .w .w (StoreWords.offsets frame 128 4 120 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+128#32) (frame+124#32) (c.get 19) .w .w (StoreWords.offsets frame 128 4 124 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot124 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+124#32) .w=c.get 19 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+124#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 124 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+124#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 124 4 112 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+124#32) (frame+116#32) (c.get 21) .w .w (StoreWords.offsets frame 124 4 116 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+124#32) (frame+120#32) (c.get 20) .w .w (StoreWords.offsets frame 124 4 120 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot120 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+120#32) .w=c.get 20 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+120#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 120 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+120#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 120 4 112 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+120#32) (frame+116#32) (c.get 21) .w .w (StoreWords.offsets frame 120 4 116 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot116 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+116#32) .w=c.get 21 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+116#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 116 4 108 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (frame+116#32) (frame+112#32) (c.get 22) .w .w (StoreWords.offsets frame 116 4 112 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot112 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+112#32) .w=c.get 22 := by
  unfold SendSave.memory
  rw [StoreRead.other _ (frame+112#32) (frame+108#32) (c.get 23) .w .w (StoreWords.offsets frame 112 4 108 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot108 (ram : Word → BitVec 8) (frame : Word) (c : Core) :
    ramRead (SendSave.memory ram frame c) (frame+108#32) .w=c.get 23 := by
  unfold SendSave.memory
  exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (frame : Word) (c : Core) (x : Word)
    (hx : ∀ i : Fin 144, x≠frame+BitVec.ofNat 32 i.val) : SendSave.memory ram frame c x=ram x := by
  unfold SendSave.memory
  rw [StoreBytes.frame _ (frame+108#32) (c.get 23) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨108+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+112#32) (c.get 22) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨112+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+116#32) (c.get 21) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨116+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+120#32) (c.get 20) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨120+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+124#32) (c.get 19) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨124+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+128#32) (c.get 18) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨128+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+132#32) (c.get 9) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨132+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+136#32) (c.get 8) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨136+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+140#32) (c.get 1) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨140+i.val,by omega⟩)]
end E5R.Thermostat.SendSaveData
