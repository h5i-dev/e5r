-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatInput
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatStrQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatInput
theorem establishes_quiet {B c ram sp fmt obj src dst flags cap pos xs}
    (h : Pre B c ram sp fmt obj src dst flags cap pos xs) (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ a, Quiet.Steps B img 37 ⟨c,ram⟩ ⟨a,FormatStrSave.memory ram sp c⟩ ∧ FormatStr.Ready c a obj ∧
      CursorInput.Pre B a (FormatStrSave.memory ram sp c) (sp+32#32) obj src dst cap pos xs := by
  obtain ⟨a,ta,ha⟩ := E5R.Thermostat.FormatStr.contract_quiet B c ram sp fmt obj flags h.pc h.spReg h.formatterReg h.stack h.aligned
    h.object h.objectAligned h.writer h.vtable h.flagsWord h.defaultFlags h.formatterStack hrom
  have ho : ViewFrame.Region ram (FormatStrSave.memory ram sp c) obj 12 :=
    fun i => FormatStrSave.frame ram sp c _ (h.objectStack i)
  have hs : ViewFrame.Region ram (FormatStrSave.memory ram sp c) src xs.length :=
    fun i => FormatStrSave.frame ram sp c _ (h.sourceStack i)
  have hl := CursorLayoutFrame.frame h.layout ho hs
  refine ⟨a,ta,ha,ha.pc,?_,ha.writer,ha.source.trans h.sourceReg,ha.length.trans h.lengthReg,
    hl.stack,hl.stackAligned,hl.object,hl.objectAligned,hl.capacity,hl.position,hl.pointerWord,hl.capacityWord,hl.positionWord,
    hl.source,hl.short,hl.output,hl.nowrap,hl.objectStack,hl.sourceStack,hl.outputStack,hl.sourceOutput,hl.objectOutput⟩
  rw [ha.sp,h.spReg,BitVec.add_assoc];rfl

end E5R.Thermostat.FormatInput
