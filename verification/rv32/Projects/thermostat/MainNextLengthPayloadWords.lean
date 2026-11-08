import Projects.thermostat.MainNextLengthMemory
import Projects.thermostat.MainHalfMemory
namespace E5R.Thermostat.MainNextLengthPayloadWords
open E5R E5R.Thermostat HttpRequestSpec

structure At (ram : Word → BitVec 8) (sp : Word) : Prop where
  word : ramRead ram (sp+5168#32) .w=0#32
  half : extend .h true (ramRead ram (sp+5172#32) .h)=0#32

/-- The actual high framing payload is zero for accepted Content-Length.
    This concerns semantic payload words; unrelated padding stays arbitrary. -/
theorem contract (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :
    At (MainNextLengthMemory.memory ram sp head amount) sp := by
  have storedWord : ramRead (MainNextLengthPrefix.stored ram sp head) (sp+5168#32) .w=0#32 := by
    unfold MainNextLengthPrefix.stored MainNextLengthStores.memory
    rw [FrameOffsets.word _ sp 0#32 5168 5172 .h (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  have storedHalf : extend .h true (ramRead (MainNextLengthPrefix.stored ram sp head) (sp+5172#32) .h)=0#32 := MainHalfMemory.zero_store _ _ true
  have copy := MainNextCopy264.frame (MainNextLengthPrefix.stored ram sp head) sp 3352 5168 6 (by decide) (Or.inr (by decide))
  have tail := MainNextLengthTailMemory.region (MainNextLengthPrefix.memory ram sp head) sp (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 (head.len+amount)) (BitVec.ofNat 32 head.minor) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 0) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 1) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 2) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 3) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 4) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 5) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 6) 5168 6 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  have region : ViewFrame.Region (MainNextLengthPrefix.stored ram sp head) (MainNextLengthMemory.memory ram sp head amount) (sp+5168#32) 6 := HeadRegionFrame.trans copy tail
  refine ⟨?_,?_⟩
  · have word := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at word
    exact word.trans storedWord
  · have half := MainHalfMemory.frame region 4 (by decide)
    simp only [BitVec.add_assoc,show 5168#32+4#32=5172#32 by decide +kernel] at half
    rw [half]
    exact storedHalf
end E5R.Thermostat.MainNextLengthPayloadWords
