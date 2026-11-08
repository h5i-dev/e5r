import Projects.thermostat.HeadClStoreRaw
import Projects.thermostat.HeadFieldsView
import Projects.thermostat.FrameOffsets
namespace E5R.Thermostat.HeadClStoreMemory
open E5R E5R.Thermostat HttpRequestSpec

theorem region (ram : Word → BitVec 8) (sp low : Word) (off len : Nat)
    (bound : off+len≤4294967296) (words : off+len≤312 ∨ 320≤off) (flag : off+len≤325 ∨ 326≤off) :
    ViewFrame.Region ram (HeadClStoreRaw.memory ram sp low) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadClStoreRaw.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => FrameOffsets.ne sp off 325 i.val j.val
    (by omega) (by have hj : j.val<1 := j.isLt;omega) (by have hj : j.val<1 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 316 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 312 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem flag_word_frame (ram : Word → BitVec 8) (sp : Word) (off : Nat)
    (bound : off+4≤4294967296) (outside : off+4≤325 ∨ 326≤off) :
    ramRead (ramWrite ram (sp+325#32) 1#32 .b) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  apply ramRead_w_congr
  intro i hi
  exact StoreBytes.frame _ _ _ _ .b (fun j => FrameOffsets.ne sp off 325 i j.val
    (by omega) (by have hj : j.val<1 := j.isLt;omega) (by have hj : j.val<1 := j.isLt;omega))

theorem low_word (ram : Word → BitVec 8) (sp low : Word) :
    ramRead (HeadClStoreRaw.memory ram sp low) (sp+312#32) .w=low := by
  unfold HeadClStoreRaw.memory
  rw [flag_word_frame _ sp 312 (by decide) (by decide),Memory.read_word_write_other _ _ _ _
    (fun i j => FrameOffsets.ne sp 312 316 i.val j.val (by have hi := i.isLt;omega) (by have hj := j.isLt;omega) (by have hi := i.isLt;have hj := j.isLt;omega))]
  exact ramRead_ramWrite_w _ _ _

theorem high_word (ram : Word → BitVec 8) (sp low : Word) :
    ramRead (HeadClStoreRaw.memory ram sp low) (sp+316#32) .w=0#32 := by
  unfold HeadClStoreRaw.memory
  rw [flag_word_frame _ sp 316 (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem hasCl (ram : Word → BitVec 8) (sp low : Word) :
    HeadClStoreRaw.memory ram sp low (sp+325#32)=HeadFieldsView.flag true := by
  simp [HeadClStoreRaw.memory,HeadFieldsView.flag,ramWrite,ramPut,byteOf]
end E5R.Thermostat.HeadClStoreMemory
