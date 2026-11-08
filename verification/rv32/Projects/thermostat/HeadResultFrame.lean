import Projects.thermostat.HeadResultView
import Projects.thermostat.HeadSaved
namespace E5R.Thermostat.HeadResultFrame
open E5R E5R.Thermostat

theorem reject_region (ram : Word → BitVec 8) (sp tag status : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤4904 ∨ 4916≤off) :
    ViewFrame.Region ram (HeadResultStore.memory ram (sp+4904#32) tag status) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadResultStore.memory
  simp only [BitVec.add_zero,
    show (sp+4904#32)+4#32=sp+4908#32 by rw [BitVec.add_assoc];rfl,
    show (sp+4904#32)+8#32=sp+4912#32 by rw [BitVec.add_assoc];rfl]
  rw [StoreBytes.frame _ _ _ _ .h (fun j => FrameOffsets.ne sp off 4912 i.val j.val
    (by omega) (by have hj : j.val<2 := j.isLt;omega) (by have hj : j.val<2 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4908 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4904 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem incomplete_region (ram : Word → BitVec 8) (sp : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤4904 ∨ 4916≤off) :
    ViewFrame.Region ram (HeadIncomplete.memory ram (sp+4904#32)) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadIncomplete.memory
  simp only [BitVec.add_zero,
    show (sp+4904#32)+4#32=sp+4908#32 by rw [BitVec.add_assoc];rfl]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4908 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4904 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem reject_saved {ram sp tag status saved} (h : HeadSaved.At ram sp saved) :
    HeadSaved.At (HeadResultStore.memory ram (sp+4904#32) tag status) sp saved := by
  apply HeadSaved.preserve h
  simpa only [BitVec.add_zero] using reject_region ram sp tag status 0 384 (by decide) (by decide)

theorem incomplete_saved {ram sp saved} (h : HeadSaved.At ram sp saved) :
    HeadSaved.At (HeadIncomplete.memory ram (sp+4904#32)) sp saved := by
  apply HeadSaved.preserve h
  simpa only [BitVec.add_zero] using incomplete_region ram sp 0 384 (by decide) (by decide)
end E5R.Thermostat.HeadResultFrame
