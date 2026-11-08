import Projects.thermostat.HeadFieldsView
import Projects.thermostat.HeadSavedTail
import Projects.thermostat.HeadFieldsSetup
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.HeadFieldsSetupMemory
open E5R E5R.Thermostat

theorem region (ram : Word → BitVec 8) (sp buf body length : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤8 ∨ 20≤off) :
    ViewFrame.Region ram (HeadFieldsSetup.memory ram sp buf body length) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadFieldsSetup.memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 12 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 16 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 8 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem word_frame (ram : Word → BitVec 8) (sp buf body length : Word) (off : Nat)
    (hb : off+4≤4294967296) (hs : off+4≤8 ∨ 20≤off) :
    ramRead (HeadFieldsSetup.memory ram sp buf body length) (sp+BitVec.ofNat 32 off) .w=
      ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (region ram sp buf body length off 4 hb hs) 0 (by decide)

theorem body_word (ram : Word → BitVec 8) (sp buf body length : Word) :
    ramRead (HeadFieldsSetup.memory ram sp buf body length) (sp+8#32) .w=body := by
  unfold HeadFieldsSetup.memory
  rw [FrameOffsets.word _ sp (length+0xffffffff#32) 8 12 .w (by decide) (by decide) (by decide),
    FrameOffsets.word _ sp (buf+1#32) 8 16 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem buffer_next_word (ram : Word → BitVec 8) (sp buf body length : Word) :
    ramRead (HeadFieldsSetup.memory ram sp buf body length) (sp+16#32) .w=buf+1#32 := by
  unfold HeadFieldsSetup.memory
  rw [FrameOffsets.word _ sp (length+0xffffffff#32) 16 12 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem length_before_word (ram : Word → BitVec 8) (sp buf body length : Word) :
    ramRead (HeadFieldsSetup.memory ram sp buf body length) (sp+12#32) .w=length+0xffffffff#32 := by
  unfold HeadFieldsSetup.memory
  exact ramRead_ramWrite_w _ _ _
theorem saved {ram sp values} (buf body length : Word) (h : HeadSaved.At ram sp values) :
    HeadSaved.At (HeadFieldsSetup.memory ram sp buf body length) sp values :=
  HeadSavedTail.preserve h (region ram sp buf body length 332 52 (by decide) (by decide))

theorem fields {ram sp f} (buf body length : Word) (h : HeadFieldsView.At ram sp f) :
    HeadFieldsView.At (HeadFieldsSetup.memory ram sp buf body length) sp f :=
  HeadFieldsView.preserve h (region ram sp buf body length 56 271 (by decide) (by decide))
end E5R.Thermostat.HeadFieldsSetupMemory
