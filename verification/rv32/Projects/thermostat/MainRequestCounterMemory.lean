import Projects.thermostat.MainRequestCounter
import Projects.thermostat.MainServeLayout
import Projects.thermostat.MainHeaderLayout
import Projects.thermostat.FrameOffsets
namespace E5R.Thermostat.MainRequestCounterMemory
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (sp count used : Word) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3292 ∨ 3300≤off) :
    ViewFrame.Region ram (MainRequestCounter.memory ram sp count used) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold MainRequestCounter.memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3296 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;rcases apart with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 3292 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;rcases apart with h|h <;> omega))]

theorem word (ram : Word → BitVec 8) (sp count used : Word) (off : Nat) (bound : off+4≤448)
    (apart : off+4≤88 ∨ 96≤off) :
    ramRead (MainRequestCounter.memory ram sp count used) ((sp+3204#32)+BitVec.ofNat 32 off) .w=
      ramRead ram ((sp+3204#32)+BitVec.ofNat 32 off) .w := by
  have region := frame ram sp count used (3204+off) 4 (by omega) (by rcases apart with h|h <;> omega)
  have kept := ViewFrame.word region 0 (by decide)
  simpa only [BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add] using kept

theorem count (ram : Word → BitVec 8) (sp served used : Word) :
    ramRead (MainRequestCounter.memory ram sp served used) (sp+3292#32) .w=served+1#32 := by
  unfold MainRequestCounter.memory
  rw [FrameOffsets.word _ sp used 3292 3296 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem used (ram : Word → BitVec 8) (sp served endWord : Word) :
    ramRead (MainRequestCounter.memory ram sp served endWord) (sp+3296#32) .w=endWord := ramRead_ramWrite_w _ _ _

theorem serve (ram : Word → BitVec 8) (served : Nat) (endWord : Word) (h : MainServeLayout.At ram served) :
    MainServeLayout.At (MainRequestCounter.memory ram 0x80ffeb90#32 (BitVec.ofNat 32 served) endWord) (served+1) := by
  have slot (off : Nat) (bound : off+4≤448) (apart : off+4≤88 ∨ 96≤off) :
      ramRead (MainRequestCounter.memory ram 0x80ffeb90#32 (BitVec.ofNat 32 served) endWord) (MainServeLayout.fp+BitVec.ofNat 32 off) .w=
        ramRead ram (MainServeLayout.fp+BitVec.ofNat 32 off) .w := by
    simpa only [show 0x80ffeb90#32+3204#32=MainServeLayout.fp by decide +kernel] using word ram 0x80ffeb90#32 (BitVec.ofNat 32 served) endWord off bound apart
  refine ⟨(slot 0 (by decide) (Or.inl (by decide))).trans h.headMax,(slot 4 (by decide) (Or.inl (by decide))).trans h.bodyMax,
    (slot 8 (by decide) (Or.inl (by decide))).trans h.requests,(slot 44 (by decide) (Or.inl (by decide))).trans h.config,
    (slot 48 (by decide) (Or.inl (by decide))).trans h.router,(slot 52 (by decide) (Or.inl (by decide))).trans h.app,
    (slot 56 (by decide) (Or.inl (by decide))).trans h.rx,(slot 60 (by decide) (Or.inl (by decide))).trans h.capacity,
    (slot 64 (by decide) (Or.inl (by decide))).trans h.tx,(slot 68 (by decide) (Or.inl (by decide))).trans h.txCapacity,
    (slot 72 (by decide) (Or.inl (by decide))).trans h.uart,?_⟩
  simpa only [show MainServeLayout.fp+88#32=0x80ffeb90#32+3292#32 by decide +kernel,←BitVec.ofNat_add] using count ram 0x80ffeb90#32 (BitVec.ofNat 32 served) endWord

theorem header (ram : Word → BitVec 8) (count used : Word) (filled : Nat) (h : MainHeaderLayout.At ram filled) :
    MainHeaderLayout.At (MainRequestCounter.memory ram 0x80ffeb90#32 count used) filled := by
  have slot (off : Nat) (bound : off+4≤448) (apart : off+4≤88 ∨ 96≤off) :
      ramRead (MainRequestCounter.memory ram 0x80ffeb90#32 count used) (MainServeLayout.fp+BitVec.ofNat 32 off) .w=
        ramRead ram (MainServeLayout.fp+BitVec.ofNat 32 off) .w := by
    simpa only [show 0x80ffeb90#32+3204#32=MainServeLayout.fp by decide +kernel] using word ram 0x80ffeb90#32 count used off bound apart
  exact ⟨⟨(slot 108 (by decide) (Or.inr (by decide))).trans h.head.rx,(slot 432 (by decide) (Or.inr (by decide))).trans h.head.config,
      (slot 76 (by decide) (Or.inl (by decide))).trans h.head.headLimit,(slot 80 (by decide) (Or.inl (by decide))).trans h.head.bodyLimit⟩,
    h.bound,(slot 112 (by decide) (Or.inr (by decide))).trans h.capacity,(slot 436 (by decide) (Or.inr (by decide))).trans h.filledPtr,
    (slot 84 (by decide) (Or.inl (by decide))).trans h.filled,(slot 440 (by decide) (Or.inr (by decide))).trans h.uartPtr⟩
end E5R.Thermostat.MainRequestCounterMemory
