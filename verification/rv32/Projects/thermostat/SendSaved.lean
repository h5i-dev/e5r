import Projects.thermostat.SendSaveData
import Projects.thermostat.ReadFrame
namespace E5R.Thermostat.SendSaved
open E5R E5R.Thermostat
structure At (ram : Word → BitVec 8) (frame : Word) (c : Core) : Prop where
  x1 : ramRead ram (frame+140#32) .w=c.get 1
  x8 : ramRead ram (frame+136#32) .w=c.get 8
  x9 : ramRead ram (frame+132#32) .w=c.get 9
  x18 : ramRead ram (frame+128#32) .w=c.get 18
  x19 : ramRead ram (frame+124#32) .w=c.get 19
  x20 : ramRead ram (frame+120#32) .w=c.get 20
  x21 : ramRead ram (frame+116#32) .w=c.get 21
  x22 : ramRead ram (frame+112#32) .w=c.get 22
  x23 : ramRead ram (frame+108#32) .w=c.get 23

theorem save (ram : Word → BitVec 8) (frame : Word) (c : Core) : At (SendSave.memory ram frame c) frame c :=
  ⟨SendSaveData.slot140 ram frame c,SendSaveData.slot136 ram frame c,SendSaveData.slot132 ram frame c,SendSaveData.slot128 ram frame c,SendSaveData.slot124 ram frame c,SendSaveData.slot120 ram frame c,SendSaveData.slot116 ram frame c,SendSaveData.slot112 ram frame c,SendSaveData.slot108 ram frame c⟩

theorem region {before after frame c} (h : At before frame c) (hf : ViewFrame.Region before after (frame+108#32) 36) : At after frame c := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := ViewFrame.word hf 32 (by decide)
    rw [BitVec.add_assoc,show 108#32+32#32=140#32 by decide +kernel] at hh
    exact hh.trans h.x1
  · have hh := ViewFrame.word hf 28 (by decide)
    rw [BitVec.add_assoc,show 108#32+28#32=136#32 by decide +kernel] at hh
    exact hh.trans h.x8
  · have hh := ViewFrame.word hf 24 (by decide)
    rw [BitVec.add_assoc,show 108#32+24#32=132#32 by decide +kernel] at hh
    exact hh.trans h.x9
  · have hh := ViewFrame.word hf 20 (by decide)
    rw [BitVec.add_assoc,show 108#32+20#32=128#32 by decide +kernel] at hh
    exact hh.trans h.x18
  · have hh := ViewFrame.word hf 16 (by decide)
    rw [BitVec.add_assoc,show 108#32+16#32=124#32 by decide +kernel] at hh
    exact hh.trans h.x19
  · have hh := ViewFrame.word hf 12 (by decide)
    rw [BitVec.add_assoc,show 108#32+12#32=120#32 by decide +kernel] at hh
    exact hh.trans h.x20
  · have hh := ViewFrame.word hf 8 (by decide)
    rw [BitVec.add_assoc,show 108#32+8#32=116#32 by decide +kernel] at hh
    exact hh.trans h.x21
  · have hh := ViewFrame.word hf 4 (by decide)
    rw [BitVec.add_assoc,show 108#32+4#32=112#32 by decide +kernel] at hh
    exact hh.trans h.x22
  · have hh := ViewFrame.word hf 0 (by decide)
    rw [BitVec.add_assoc,show 108#32+0#32=108#32 by decide +kernel] at hh
    exact hh.trans h.x23
end E5R.Thermostat.SendSaved
