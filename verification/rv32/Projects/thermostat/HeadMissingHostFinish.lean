import Projects.thermostat.HeadDonePrepare
import Projects.thermostat.HeadFieldsFailStore
import Projects.thermostat.HeadReturn
import Projects.thermostat.HeadResultFrame
namespace E5R.Thermostat.HeadMissingHostFinish
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word)
    (missing : HeadDonePrepare.Missing c sp) (output : ramRead ram (sp+52#32) .w=sp+4904#32)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp saved) :
    ∃ d, Quiet.Steps B img 20 ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram (sp+4904#32) 4#32 400#32⟩ ∧
      d.pc=saved 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d saved ∧
      HeadResultView.At (HeadResultStore.memory ram (sp+4904#32) 4#32 400#32) (sp+4904#32) (.reject 400) ∧ d.sameCsr c := by
  have small : Memory.Block B sp 56 := by simpa only [BitVec.add_zero] using Memory.sub_block stack (off := 0) (by decide) (by decide)
  have abi : Memory.Block B sp 384 := by simpa only [BitVec.add_zero] using Memory.sub_block stack (off := 0) (by decide) (by decide)
  obtain ⟨a,ta,apc,_,ar,ac⟩ := HeadFieldsFailStore.contract B c ram sp (sp+4904#32) 4#32 400#32 missing.2.2.2 missing.2.1 missing.2.2.1 output
    small aligned (Memory.sub_block stack (by decide) (by decide)) (Memory.word_aligned sp 1226 aligned) missing.1
  obtain ⟨d,td,dpc,dsp,regs,_,dc⟩ := HeadReturn.contract B a _ sp saved apc ((ar 2 (by decide)).trans missing.2.2.2)
    abi aligned (HeadResultFrame.reject_saved stored)
  exact ⟨d,ta.trans td,dpc,dsp,regs,HeadResultView.reject ram (sp+4904#32) 400 (by decide),dc.trans ac⟩
end E5R.Thermostat.HeadMissingHostFinish
