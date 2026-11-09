import Projects.thermostat.LoopKeepRebuild
import Projects.thermostat.MainHeaderLayout
import Projects.thermostat.MainServeLayout
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
namespace E5R.Thermostat.LoopKeepLayout
open E5R E5R.Thermostat
abbrev fp := 0x80fff814#32

/-- The old filled/used equality drives the actual rebuild; other live serve
    slots and head/body limits are preserved by its exact twelve stores. -/
theorem word (ram : Word → BitVec 8) (used : Word) (off : Nat)
    (safe : off+4≤84 ∨ (88≤off ∧ off+4≤100)) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+BitVec.ofNat 32 off) .w=
      ramRead ram (fp+BitVec.ofNat 32 off) .w := by
  unfold LoopKeepRebuild.memory
  rw [FrameOffsets.word _ fp _ off 112 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 108 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 104 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 100 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 84 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 432 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 428 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 424 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 420 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 448 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 440 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ off 436 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  try rfl

theorem rx (ram : Word → BitVec 8) (used : Word) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+108#32) .w=0x80ffec14#32 := by
  unfold LoopKeepRebuild.memory
  rw [FrameOffsets.word _ fp _ 108 112 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  exact ramRead_ramWrite_w _ _ _

theorem config (ram : Word → BitVec 8) (used : Word) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+432#32) .w=0x80fff860#32 := by
  unfold LoopKeepRebuild.memory
  rw [FrameOffsets.word _ fp _ 432 112 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 432 108 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 432 104 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 432 100 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 432 84 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  exact ramRead_ramWrite_w _ _ _

theorem capacity (ram : Word → BitVec 8) (used : Word) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+112#32) .w=2048#32 := by
  unfold LoopKeepRebuild.memory
  exact ramRead_ramWrite_w _ _ _

theorem filledPtr (ram : Word → BitVec 8) (used : Word) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+436#32) .w=0x80fff868#32 := by
  unfold LoopKeepRebuild.memory
  rw [FrameOffsets.word _ fp _ 436 112 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 108 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 104 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 100 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 84 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 432 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 428 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 424 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 420 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 448 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 436 440 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  exact ramRead_ramWrite_w _ _ _

theorem filled (ram : Word → BitVec 8) (used : Word) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+84#32) .w=0#32 := by
  unfold LoopKeepRebuild.memory
  rw [FrameOffsets.word _ fp _ 84 112 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 84 108 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 84 104 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 84 100 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  exact ramRead_ramWrite_w _ _ _

theorem uartPtr (ram : Word → BitVec 8) (used : Word) :
    ramRead (LoopKeepRebuild.memory ram used) (fp+440#32) .w=0x80ffffc7#32 := by
  unfold LoopKeepRebuild.memory
  rw [FrameOffsets.word _ fp _ 440 112 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 108 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 104 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 100 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 84 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 432 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 428 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 424 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 420 .w (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  rw [FrameOffsets.word _ fp _ 440 448 .b (by omega) (by decide) (by simp only [Width.bytes]; omega)]
  exact ramRead_ramWrite_w _ _ _

theorem header (ram : Word → BitVec 8) (used : Word)
    (headLimit : ramRead ram (fp+76#32) .w=1024#32)
    (bodyLimit : ramRead ram (fp+80#32) .w=1024#32) :
    MainHeaderLayout.At (LoopKeepRebuild.memory ram used) 0 := by
  refine ⟨⟨rx ram used,config ram used,?_,?_⟩,by decide,capacity ram used,?_,filled ram used,uartPtr ram used⟩
  · exact (word ram used 76 (Or.inl (by decide))).trans headLimit
  · exact (word ram used 80 (Or.inl (by decide))).trans bodyLimit
  · simpa only [show fp+84#32=0x80fff868#32 by decide +kernel] using filledPtr ram used

theorem serve {ram : Word → BitVec 8} {served : Nat} (used : Word) (h : MainServeLayout.At ram served) :
    MainServeLayout.At (LoopKeepRebuild.memory ram used) served := by
  apply MainServeLayout.preserve (h := h)
  intro off member
  obtain ⟨bound,apart⟩ := MainServeLayout.bounds off member
  exact word ram used off (by omega)
end E5R.Thermostat.LoopKeepLayout
