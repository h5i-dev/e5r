import Projects.thermostat.HeadStackSave
import Projects.thermostat.AppState
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.HeadStackMemory
open E5R E5R.Thermostat

theorem region (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤332 ∨ 384≤off) :
    ViewFrame.Region ram (HeadStackSave.memory ram sp saved) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadStackSave.memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 332 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 336 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 340 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 344 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 348 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 352 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 356 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 360 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 364 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 368 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 372 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 376 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 380 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]

theorem word (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) (off : Nat)
    (hb : off+4≤4294967296) (hs : off+4≤332 ∨ 384≤off) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+BitVec.ofNat 32 off) .w=
      ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (region ram sp saved off 4 hb hs) 0 (by decide)

theorem saved1 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+380#32) .w=saved 1 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 380 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 380 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 380 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 380 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 380 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 380 352 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 21) 380 356 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 20) 380 360 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 19) 380 364 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 18) 380 368 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 9) 380 372 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 8) 380 376 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved8 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+376#32) .w=saved 8 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 376 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 376 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 376 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 376 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 376 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 376 352 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 21) 376 356 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 20) 376 360 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 19) 376 364 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 18) 376 368 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 9) 376 372 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved9 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+372#32) .w=saved 9 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 372 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 372 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 372 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 372 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 372 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 372 352 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 21) 372 356 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 20) 372 360 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 19) 372 364 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 18) 372 368 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved18 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+368#32) .w=saved 18 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 368 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 368 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 368 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 368 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 368 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 368 352 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 21) 368 356 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 20) 368 360 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 19) 368 364 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved19 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+364#32) .w=saved 19 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 364 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 364 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 364 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 364 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 364 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 364 352 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 21) 364 356 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 20) 364 360 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved20 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+360#32) .w=saved 20 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 360 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 360 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 360 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 360 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 360 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 360 352 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 21) 360 356 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved21 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+356#32) .w=saved 21 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 356 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 356 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 356 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 356 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 356 348 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 22) 356 352 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved22 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+352#32) .w=saved 22 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 352 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 352 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 352 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 352 344 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 23) 352 348 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved23 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+348#32) .w=saved 23 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 348 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 348 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 348 340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 24) 348 344 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved24 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+344#32) .w=saved 24 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 344 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 344 336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 25) 344 340 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved25 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+340#32) .w=saved 25 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 340 332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (saved 26) 340 336 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved26 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+336#32) .w=saved 26 := by
  unfold HeadStackSave.memory
  rw [FrameOffsets.word _ sp (saved 27) 336 332 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem saved27 (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    ramRead (HeadStackSave.memory ram sp saved) (sp+332#32) .w=saved 27 := by
  unfold HeadStackSave.memory
  exact ramRead_ramWrite_w _ _ _

/-- The parser stack is below the real App borrow word and snapshot. -/
theorem app (ram : Word → BitVec 8) (saved : Reg → Word) (s : Spec.Snapshot) (h : AppState.At ram s) :
    AppState.At (HeadStackSave.memory ram 0x80ffea10#32 saved) s := by
  apply AppState.preserve ram _ s h
  have region := region ram 0x80ffea10#32 saved 428 25 (by decide) (by decide)
  have base : 0x80ffea10#32+428#32=0x80ffebbc#32 := by decide +kernel
  simpa only [ViewFrame.Region,base] using region
end E5R.Thermostat.HeadStackMemory
