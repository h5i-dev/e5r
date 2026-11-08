import Projects.thermostat.MainServeNextStoreFrames
import Projects.thermostat.MainServeNextCopyOne
import Projects.thermostat.MainServeNextCopyTwo
import Projects.thermostat.MainNextArrayFrame
import Projects.thermostat.MainNextArrayRelocate
import Projects.thermostat.MainHalfMemory
namespace E5R.Thermostat.MainServeNextMemory
open E5R E5R.Thermostat HttpRequestSpec

def front (ram : Word → BitVec 8) (sp : Word) := MainServeNextFront.memory ram sp
def firstCopy (ram : Word → BitVec 8) (sp : Word) := MainServeNextCopyOne.memory (front ram sp) sp

def firstPack (ram : Word → BitVec 8) (sp : Word) := MainServeNextPackOne.memory (firstCopy ram sp) sp
  (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h))
  (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b))

def zeroStage (ram : Word → BitVec 8) (sp : Word) := MainServeNextZeroStage.memory (firstPack ram sp) sp

def secondCopy (ram : Word → BitVec 8) (sp : Word) := MainServeNextCopyTwo.memory (zeroStage ram sp) sp

def memory (ram : Word → BitVec 8) (sp : Word) := MainServeNextPackTwo.memory (secondCopy ram sp) sp
  (ramRead (secondCopy ram sp) (sp+3960#32) .w) (extend .h true (ramRead (secondCopy ram sp) (sp+3964#32) .h))
  (extend .b false (ramRead (secondCopy ram sp) (sp+3966#32) .b))

theorem frame (ram : Word → BitVec 8) (sp : Word) (off size : Nat) (bound : off+size≤3652) :
    ViewFrame.Region ram (memory ram sp) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainServeNextStoreFrames.front ram sp off size (by omega) (Or.inl bound) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainRamCopy264.frame (front ram sp) sp 1226 992 off size (by omega) (by decide) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainServeNextStoreFrames.packOne (firstCopy ram sp) sp (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h)) (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b)) off size (by omega) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainServeNextStoreFrames.zeroStage (firstPack ram sp) sp off size (by omega) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainRamCopy264.frame (zeroStage ram sp) sp 992 1062 off size (by omega) (by decide) (Or.inl (by omega)))
  exact MainServeNextStoreFrames.packTwo (secondCopy ram sp) sp (ramRead (secondCopy ram sp) (sp+3960#32) .w) (extend .h true (ramRead (secondCopy ram sp) (sp+3964#32) .h)) (extend .b false (ramRead (secondCopy ram sp) (sp+3966#32) .b)) off size (by omega) (Or.inl (by omega))

theorem zero_input (ram : Word → BitVec 8) (sp : Word) :
    ramRead (firstPack ram sp) (sp+4232#32) .w=0#32 ∧ extend .h true (ramRead (firstPack ram sp) (sp+4236#32) .h)=0#32 := by
  have word : ramRead (front ram sp) (sp+4232#32) .w=0#32 := by
    unfold front MainServeNextFront.memory
    rw [FrameOffsets.word _ sp 0#32 4232 4236 .h (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  have half : extend .h true (ramRead (front ram sp) (sp+4236#32) .h)=0#32 := MainHalfMemory.zero_store _ _ true
  have copy := MainRamCopy264.frame (front ram sp) sp 1226 992 4232 6 (by decide) (by decide) (Or.inr (by decide))
  have packed := MainServeNextStoreFrames.packOne (firstCopy ram sp) sp
    (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h))
    (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b)) 4232 6 (by decide) (Or.inr (by decide))
  have region : ViewFrame.Region (front ram sp) (firstPack ram sp) (sp+4232#32) 6 := HeadRegionFrame.trans copy packed
  refine ⟨?_,?_⟩
  · have preserved := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at preserved
    exact preserved.trans word
  · have preserved := MainHalfMemory.frame region 4 (by decide)
    simp only [BitVec.add_assoc,show 4232#32+4#32=4236#32 by decide +kernel] at preserved
    rw [preserved]
    exact half

theorem array (ram : Word → BitVec 8) (sp : Word) (head : Head) (stack : Memory.Block B sp 5232)
    (view : MainNextArrayView.At ram (sp+4904#32) head) : MainNextArrayView.At (memory ram sp) (sp+4248#32) head := by
  have frontView := MainNextArrayFrame.preserve view (MainServeNextStoreFrames.front ram sp 4904 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide)))
  have first := MainNextArrayRelocate.contract frontView (MainRamCopy264.bytes (front ram sp) sp 1226 992 (by decide) stack)
  have packed := MainNextArrayFrame.preserve first (MainServeNextStoreFrames.packOne (firstCopy ram sp) sp (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h)) (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b)) 3968 264 (by decide) (Or.inr (by decide)))
  have zero := MainNextArrayFrame.preserve packed (MainServeNextStoreFrames.zeroStage (firstPack ram sp) sp 3968 264 (by decide) (Or.inl (by decide)))
  have second := MainNextArrayRelocate.contract zero (MainRamCopy264.bytes (zeroStage ram sp) sp 992 1062 (by decide) stack)
  exact MainNextArrayFrame.preserve second (MainServeNextStoreFrames.packTwo (secondCopy ram sp) sp (ramRead (secondCopy ram sp) (sp+3960#32) .w) (extend .h true (ramRead (secondCopy ram sp) (sp+3964#32) .h)) (extend .b false (ramRead (secondCopy ram sp) (sp+3966#32) .b)) 4248 264 (by decide) (Or.inr (by decide)))
end E5R.Thermostat.MainServeNextMemory
