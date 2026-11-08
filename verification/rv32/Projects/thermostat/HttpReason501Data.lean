import Projects.thermostat.HttpReason501
import Projects.thermostat.ResponseHeadSpec
import Projects.thermostat.ByteWrite
import Projects.thermostat.CopyRegs
set_option maxRecDepth 5000
namespace E5R.Thermostat.HttpReason501Data
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem memory_eq (ram : Word → BitVec 8) (dst : Word) :
    HttpReason501.memory ram dst=ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 501)) := by
  change HttpReason501.memory ram dst=ByteWrite.write ram (dst+13#32) [78#8,111#8,116#8,32#8,73#8,109#8,112#8,108#8,101#8,109#8,101#8,110#8,116#8,101#8,100#8]
  simp only [HttpReason501.memory,ramWrite,ByteWrite.write,BitVec.add_assoc]
  rfl

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word)
    (hp : c.pc=0x80003584#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=13#32) (h13 : c.get 13=501#32) (hm : Memory.Block B dst 192) :
    ∃ d, Quiet.Steps B img 47 ⟨c,ram⟩ ⟨d,ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 501))⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (13+(WireSpec.ascii (ResponseHeadSpec.reason 501)).length) ∧
      Bytes.Span B (ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 501))) (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 501)) := by
  obtain ⟨d,td,pd,d14,d15,d10,d11,d13,d16,d12,dr,dc⟩ := HttpReason501.contract c ram dst h10 h11 h12 h13 hm hp
  rw [memory_eq] at td
  refine ⟨d,td,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,d11,?_⟩
  · intro r hr
    exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 13 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 16 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 12 hr (by decide) (by decide) (by decide) (by decide))
  · apply ByteWrite.span
    · exact Memory.sub_block hm (by decide +kernel) (by decide +kernel)
    · decide +kernel
end E5R.Thermostat.HttpReason501Data
