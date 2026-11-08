import Projects.thermostat.HeadVersionSave
import Projects.thermostat.HeadSaved
namespace E5R.Thermostat.HeadVersionMemory
open E5R E5R.Thermostat

theorem region (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤20 ∨ 56≤off) :
    ViewFrame.Region ram (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadVersionSave.memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 20 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 48 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 52 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 44 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 36 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 40 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 32 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 24 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 28 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem word_frame (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) (off : Nat)
    (hb : off+4≤4294967296) (hs : off+4≤20 ∨ 56≤off) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (region ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd off 4 hb hs) 0 (by decide)

theorem targetEnd_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+28#32) .w=targetEnd := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 28 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 28 48 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (dst) 28 52 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (buf) 28 44 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (maxHead) 28 36 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (n) 28 40 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (mask) 28 32 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 28 24 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem targetStart_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+24#32) .w=targetStart := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 24 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 24 48 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (dst) 24 52 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (buf) 24 44 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (maxHead) 24 36 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (n) 24 40 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (mask) 24 32 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem mask_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+32#32) .w=mask := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 32 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 32 48 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (dst) 32 52 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (buf) 32 44 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (maxHead) 32 36 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (n) 32 40 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem n_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+40#32) .w=n := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 40 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 40 48 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (dst) 40 52 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (buf) 40 44 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (maxHead) 40 36 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem maxHead_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+36#32) .w=maxHead := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 36 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 36 48 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (dst) 36 52 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (buf) 36 44 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem buf_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+44#32) .w=buf := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 44 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 44 48 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (dst) 44 52 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem dst_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+52#32) .w=dst := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 52 20 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 52 48 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem length_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+48#32) .w=length := by
  unfold HeadVersionSave.memory
  rw [FrameOffsets.word _ sp (methodEnd) 48 20 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem methodEnd_word (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :
    ramRead (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) (sp+20#32) .w=methodEnd := by
  unfold HeadVersionSave.memory
  exact ramRead_ramWrite_w _ _ _

theorem saved (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) (values : Reg → Word) (h : HeadSaved.At ram sp values) :
    HeadSaved.At (HeadVersionSave.memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd) sp values := by
  exact ⟨(word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 380 (by decide) (by decide)).trans h.x1,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 376 (by decide) (by decide)).trans h.x8,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 372 (by decide) (by decide)).trans h.x9,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 368 (by decide) (by decide)).trans h.x18,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 364 (by decide) (by decide)).trans h.x19,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 360 (by decide) (by decide)).trans h.x20,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 356 (by decide) (by decide)).trans h.x21,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 352 (by decide) (by decide)).trans h.x22,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 348 (by decide) (by decide)).trans h.x23,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 344 (by decide) (by decide)).trans h.x24,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 340 (by decide) (by decide)).trans h.x25,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 336 (by decide) (by decide)).trans h.x26,
    (word_frame ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd 332 (by decide) (by decide)).trans h.x27⟩

theorem app (ram : Word → BitVec 8) (targetEnd targetStart mask n maxHead buf dst length methodEnd : Word)
    (state : Spec.Snapshot) (h : AppState.At ram state) :
    AppState.At (HeadVersionSave.memory ram 0x80ffea10#32 targetEnd targetStart mask n maxHead buf dst length methodEnd) state := by
  apply AppState.preserve ram _ state h
  have frame := region ram 0x80ffea10#32 targetEnd targetStart mask n maxHead buf dst length methodEnd 428 25 (by decide) (by decide)
  have base : 0x80ffea10#32+428#32=0x80ffebbc#32 := by decide +kernel
  simpa only [ViewFrame.Region,base] using frame
end E5R.Thermostat.HeadVersionMemory
