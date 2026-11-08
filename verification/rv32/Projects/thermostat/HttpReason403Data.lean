import Projects.thermostat.HttpReason403
import Projects.thermostat.ResponseHeadSpec
import Projects.thermostat.ByteWrite
import Projects.thermostat.CopyRegs
set_option maxRecDepth 5000
namespace E5R.Thermostat.HttpReason403Data
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem memory_eq (ram : Word → BitVec 8) (dst : Word) :
    HttpReason403.memory ram dst=ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 403)) := by
  change HttpReason403.memory ram dst=ByteWrite.write ram (dst+13#32) [70#8,111#8,114#8,98#8,105#8,100#8,100#8,101#8,110#8]
  simp only [HttpReason403.memory,ramWrite,ByteWrite.write,BitVec.add_assoc]
  rfl

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word)
    (hp : c.pc=0x80003584#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=13#32) (h13 : c.get 13=403#32) (hm : Memory.Block B dst 192) :
    ∃ d, Quiet.Steps B img 40 ⟨c,ram⟩ ⟨d,ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 403))⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (13+(WireSpec.ascii (ResponseHeadSpec.reason 403)).length) ∧
      Bytes.Span B (ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 403))) (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 403)) := by
  obtain ⟨d,td,pd,d14,d15,d10,d11,d13,d12,dr,dc⟩ := HttpReason403.contract c ram dst h10 h11 h12 h13 hm hp
  rw [memory_eq] at td
  refine ⟨d,td,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,d11,?_⟩
  · intro r hr
    exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 13 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 12 hr (by decide) (by decide) (by decide) (by decide))
  · apply ByteWrite.span
    · exact Memory.sub_block hm (by decide +kernel) (by decide +kernel)
    · decide +kernel
end E5R.Thermostat.HttpReason403Data
