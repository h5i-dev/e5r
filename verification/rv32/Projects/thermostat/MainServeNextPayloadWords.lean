import Projects.thermostat.MainServeNextMemory
set_option autoImplicit false
namespace E5R.Thermostat.MainServeNextPayloadWords
open E5R E5R.Thermostat

def At (ram : Word → BitVec 8) (sp : Word) : Prop :=
  ramRead ram (sp+4512#32) .w=0#32 ∧ extend .h true (ramRead ram (sp+4516#32) .h)=0#32

/-- Actual common Next staging writes these six semantic high-payload bytes.
    They are distinct from the arbitrary seven padding bytes. -/
theorem stored (ram : Word → BitVec 8) (sp : Word) : At (MainServeNextMemory.memory ram sp) sp := by
  have word : ramRead (MainServeNextMemory.zeroStage ram sp) (sp+4512#32) .w=0#32 := by
    unfold MainServeNextMemory.zeroStage MainServeNextZeroStage.memory
    rw [FrameOffsets.word _ sp 0#32 4512 4516 .h (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  have half : extend .h true (ramRead (MainServeNextMemory.zeroStage ram sp) (sp+4516#32) .h)=0#32 := MainHalfMemory.zero_store _ _ true
  have copy := MainRamCopy264.frame (MainServeNextMemory.zeroStage ram sp) sp 992 1062 4512 6 (by decide) (by decide) (Or.inr (by decide))
  have pack := MainServeNextStoreFrames.packTwo (MainServeNextMemory.secondCopy ram sp) sp
    (ramRead (MainServeNextMemory.secondCopy ram sp) (sp+3960#32) .w)
    (extend .h true (ramRead (MainServeNextMemory.secondCopy ram sp) (sp+3964#32) .h))
    (extend .b false (ramRead (MainServeNextMemory.secondCopy ram sp) (sp+3966#32) .b)) 4512 6 (by decide) (Or.inr (by decide))
  have region : ViewFrame.Region (MainServeNextMemory.zeroStage ram sp) (MainServeNextMemory.memory ram sp) (sp+4512#32) 6 := HeadRegionFrame.trans copy pack
  refine ⟨?_,?_⟩
  · have preserved := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at preserved
    exact preserved.trans word
  · have preserved := MainHalfMemory.frame region 4 (by decide)
    simp only [BitVec.add_assoc,show 4512#32+4#32=4516#32 by decide +kernel] at preserved
    rw [preserved]
    exact half
end E5R.Thermostat.MainServeNextPayloadWords
