import Projects.thermostat.NextFramingCore
import Projects.thermostat.MainServeNextMemory
namespace E5R.Thermostat.NextFramingMemory
open E5R E5R.Thermostat HttpRequestSpec RejectNextCore
abbrev B := UartPlatform.board

theorem frame (ram : Word → BitVec 8) (sp : Word) (off size : Nat) (bound : off+size≤3652) :
    ViewFrame.Region ram (memory ram sp) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (RejectNextFrames.front ram sp (ramRead ram (sp+5168#32) .w) (extend .h true (ramRead ram (sp+5172#32) .h)) off size (by omega) (Or.inl bound) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainRamCopy264.frame (front ram sp) sp 1226 992 off size (by omega) (by decide) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainServeNextStoreFrames.packOne (firstCopy ram sp) sp (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h)) (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b)) off size (by omega) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (RejectNextFrames.zeroStage (firstPack ram sp) sp (ramRead (firstPack ram sp) (sp+4232#32) .w) (extend .h true (ramRead (firstPack ram sp) (sp+4236#32) .h)) off size (by omega) (Or.inl (by omega)))
  apply HeadRegionFrame.trans (MainRamCopy264.frame (zeroStage ram sp) sp 992 1062 off size (by omega) (by decide) (Or.inl (by omega)))
  exact MainServeNextStoreFrames.packTwo (secondCopy ram sp) sp (ramRead (secondCopy ram sp) (sp+3960#32) .w) (extend .h true (ramRead (secondCopy ram sp) (sp+3964#32) .h)) (extend .b false (ramRead (secondCopy ram sp) (sp+3966#32) .b)) off size (by omega) (Or.inl (by omega))

theorem array (ram : Word → BitVec 8) (sp : Word) (head : Head) (stack : Memory.Block B sp 5232)
    (view : MainNextArrayView.At ram (sp+4904#32) head) : MainNextArrayView.At (memory ram sp) (sp+4248#32) head := by
  have frontView := MainNextArrayFrame.preserve view (RejectNextFrames.front ram sp (ramRead ram (sp+5168#32) .w) (extend .h true (ramRead ram (sp+5172#32) .h)) 4904 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide)))
  have first := MainNextArrayRelocate.contract frontView (MainRamCopy264.bytes (front ram sp) sp 1226 992 (by decide) stack)
  have packed := MainNextArrayFrame.preserve first (MainServeNextStoreFrames.packOne (firstCopy ram sp) sp (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h)) (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b)) 3968 264 (by decide) (Or.inr (by decide)))
  have zero := MainNextArrayFrame.preserve packed (RejectNextFrames.zeroStage (firstPack ram sp) sp (ramRead (firstPack ram sp) (sp+4232#32) .w) (extend .h true (ramRead (firstPack ram sp) (sp+4236#32) .h)) 3968 264 (by decide) (Or.inl (by decide)))
  have second := MainNextArrayRelocate.contract zero (MainRamCopy264.bytes (zeroStage ram sp) sp 992 1062 (by decide) stack)
  exact MainNextArrayFrame.preserve second (MainServeNextStoreFrames.packTwo (secondCopy ram sp) sp (ramRead (secondCopy ram sp) (sp+3960#32) .w) (extend .h true (ramRead (secondCopy ram sp) (sp+3964#32) .h)) (extend .b false (ramRead (secondCopy ram sp) (sp+3966#32) .b)) 4248 264 (by decide) (Or.inr (by decide)))
end E5R.Thermostat.NextFramingMemory
