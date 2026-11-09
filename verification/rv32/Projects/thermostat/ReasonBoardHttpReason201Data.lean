import Projects.thermostat.HttpReason201Data
import Projects.thermostat.ReasonBoardHttpReason201
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason201Data
open E5R E5R.Thermostat HttpReason201Data
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word)
    (hp : c.pc=0x80003584#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=13#32) (h13 : c.get 13=201#32) (hm : Memory.Block B dst 192) :
    ∃ d, Quiet.Steps B img 36 ⟨c,ram⟩ ⟨d,ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 201))⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (13+(WireSpec.ascii (ResponseHeadSpec.reason 201)).length) ∧
      Bytes.Span B (ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 201))) (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason 201)) := by
  obtain ⟨d,td,pd,d14,d15,d10,d11,d13,d12,dr,dc⟩ := ReasonBoardHttpReason201.contract c ram dst h10 h11 h12 h13 hm hp
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
end E5R.Thermostat.ReasonBoardHttpReason201Data
