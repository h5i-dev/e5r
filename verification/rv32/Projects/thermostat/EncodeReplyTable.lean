import Projects.thermostat.EncodeReplyConstructMemory
import Projects.thermostat.EncodeValues
import Projects.thermostat.FormatTable
namespace E5R.Thermostat.EncodeReplyTable
open E5R E5R.Thermostat

theorem table (B : Board) (ram : Word → BitVec 8) (sp reply modePtr modeLen : Word) (s : Spec.Snapshot)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4=0) :
    FormatTable.At B (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (sp+28#32) (EncodeValues.values reply (sp+20#32) s) := by
  have hw := EncodeReplyConstruct.words ram sp reply modePtr modeLen
  refine ⟨Memory.sub_block hm (off := 28) (m := 64) (by decide) (by decide),Memory.word_aligned sp 7 ha,?_,?_⟩
  · intro i
    have hi := i.isLt
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 := by omega
    rcases hc with h0|h0|h0|h0|h0|h0|h0|h0
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*0))) .w = reply+4#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*0)) = 28#32 by decide +kernel]
      exact hw.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*1))) .w = reply+6#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*1)) = 36#32 by decide +kernel]
      exact hw.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*2))) .w = reply+8#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*2)) = 44#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*3))) .w = reply
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*3)) = 52#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*4))) .w = reply+1#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*4)) = 60#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*5))) .w = reply+2#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*5)) = 68#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*6))) .w = reply+3#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*6)) = 76#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.pointer]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*7))) .w = sp+20#32
      rw [BitVec.add_assoc,show (28#32+BitVec.ofNat 32 (8*7)) = 84#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro i
    have hi := i.isLt
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 := by omega
    rcases hc with h0|h0|h0|h0|h0|h0|h0|h0
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*0))+4#32) .w = 0x80004e5e#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*0)+4#32)) = 32#32 by decide +kernel]
      exact hw.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*1))+4#32) .w = 0x80004e5e#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*1)+4#32)) = 40#32 by decide +kernel]
      exact hw.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*2))+4#32) .w = 0x80005112#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*2)+4#32)) = 48#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*3))+4#32) .w = 0x80005112#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*3)+4#32)) = 56#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*4))+4#32) .w = 0x80005112#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*4)+4#32)) = 64#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*5))+4#32) .w = 0x80005112#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*5)+4#32)) = 72#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*6))+4#32) .w = 0x80005112#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*6)+4#32)) = 80#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · simp only [EncodeValues.values,h0,FormatValue.entry]
      change ramRead (EncodeReplyConstruct.memory ram sp reply modePtr modeLen) (((sp+28#32)+BitVec.ofNat 32 (8*7))+4#32) .w = 0x8000228c#32
      rw [BitVec.add_assoc,BitVec.add_assoc,show (28#32+(BitVec.ofNat 32 (8*7)+4#32)) = 88#32 by decide +kernel]
      exact hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
end E5R.Thermostat.EncodeReplyTable
