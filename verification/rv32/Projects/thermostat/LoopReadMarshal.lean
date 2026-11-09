import Projects.thermostat.ReadMarshal
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
set_option autoImplicit false
namespace E5R.Thermostat.LoopReadMarshal
open E5R E5R.Thermostat
abbrev sp := 0x80ffeb90#32
/-- The broad old scratch frame covers SP+8..24, but the actual three word
    stores are at +8,+12,+20. The initialized receive capacity at +16 survives. -/
theorem capacity (ram : Word → BitVec 8) :
    ViewFrame.Region ram (ReadMarshal.memory ram) 0x80ffeba0#32 4 := by
  intro i
  have index := i.isLt
  have address : 0x80ffeba0#32+BitVec.ofNat 32 i.val=sp+BitVec.ofNat 32 (16+i.val) := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
  rw [address]
  unfold ReadMarshal.memory
  rw [show 2164260536#32=sp+BitVec.ofNat 32 4904 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4904 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260540#32=sp+BitVec.ofNat 32 4908 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4908 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260539#32=sp+BitVec.ofNat 32 4907 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4907 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260538#32=sp+BitVec.ofNat 32 4906 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4906 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260537#32=sp+BitVec.ofNat 32 4905 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4905 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260544#32=sp+BitVec.ofNat 32 4912 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4912 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260543#32=sp+BitVec.ofNat 32 4911 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4911 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260542#32=sp+BitVec.ofNat 32 4910 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4910 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260541#32=sp+BitVec.ofNat 32 4909 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4909 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164255644#32=sp+BitVec.ofNat 32 12 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 12 .w (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164255652#32=sp+BitVec.ofNat 32 20 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 20 .w (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164255640#32=sp+BitVec.ofNat 32 8 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 8 .w (by omega) (by decide) (by simp only [Width.bytes];omega)]
  rw [show 2164260545#32=sp+BitVec.ofNat 32 4913 by decide +kernel]
  rw [FrameOffsets.byte _ sp _ (16+i.val) 4913 .b (by omega) (by decide) (by simp only [Width.bytes];omega)]
end E5R.Thermostat.LoopReadMarshal
