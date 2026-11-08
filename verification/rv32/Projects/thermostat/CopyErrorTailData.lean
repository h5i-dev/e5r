import Projects.thermostat.UnalignedCopyData
namespace E5R.Thermostat.CopyErrorTailData
open E5R E5R.Thermostat

def pointer (wide : Bool) : Word := if wide then 0x80005bc6#32 else 0x80005bdf#32

theorem outside (wide : Bool) : UartPlatform.board.inRam (pointer wide) 1=false := by
  cases wide <;> (unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)

theorem span (wide : Bool) (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram (pointer wide) [125#8] := by
  apply ReadBytes.of_data
  · decide
  · cases wide <;> decide
  · intro i;have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
    cases wide <;> simp only [pointer,ite_true,ite_false,hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] <;> decide
  · intro i;have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
    simpa only [hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] using outside wide
  · intro i;have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
    cases wide <;> simp only [pointer,ite_true,ite_false,hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] <;> decide +kernel +revert
end E5R.Thermostat.CopyErrorTailData
