import Projects.thermostat.HeadHeaderAdd
import Projects.thermostat.HeadRegionFrame
namespace E5R.Thermostat.HeadFieldsStepFrame
open E5R E5R.Thermostat

def At (before after : Word → BitVec 8) (sp : Word) : Prop :=
  ∀ off len : Nat, off+len≤5312 → (8≤off ∧ off+len≤56 ∨ 327≤off) →
    ViewFrame.Region before after (sp+BitVec.ofNat 32 off) len

theorem trans {before mid after sp} (first : At before mid sp) (second : At mid after sp) : At before after sp :=
  fun off len bound outside => HeadRegionFrame.trans (first off len bound outside) (second off len bound outside)

theorem of_line {before after sp} (lineFrame : ViewFrame.Region before after (sp+8#32) 5304) : At before after sp := by
  intro off len bound outside
  exact HeadRegionFrame.offset lineFrame off len (by omega) (by omega)

theorem after_add {before mid after sp} (lineFrame : ViewFrame.Region before mid (sp+8#32) 5304)
    (addFrame : HeadHeaderAddFrame.At mid after sp) : At before after sp := by
  intro off len bound outside
  exact HeadRegionFrame.trans (HeadRegionFrame.offset lineFrame off len (by omega) (by omega))
    (addFrame off len (by omega) (by omega))
end E5R.Thermostat.HeadFieldsStepFrame
