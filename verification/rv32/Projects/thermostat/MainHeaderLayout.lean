import Projects.thermostat.MainHeadLayout
namespace E5R.Thermostat.MainHeaderLayout
open E5R E5R.Thermostat

structure At (ram : Word → BitVec 8) (filled : Nat) : Prop where
  head : MainHeadLayout.At ram
  bound : filled≤2048
  capacity : ramRead ram (0x80fff814#32+112#32) .w=2048#32
  filledPtr : ramRead ram (0x80fff814#32+436#32) .w=0x80fff814#32+84#32
  filled : ramRead ram (0x80fff814#32+84#32) .w=BitVec.ofNat 32 filled
  uartPtr : ramRead ram (0x80fff814#32+440#32) .w=0x80ffffc7#32

theorem initialized (ram : Word → BitVec 8) (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) : At (FutureSetup.memory ram) 0 := by
  have layout := FutureSetup.layout ram capacity
  exact ⟨MainHeadLayout.initialized ram capacity,by decide,layout.capacity,layout.filledPtr,layout.filled,layout.uartPtr⟩

theorem preserve {before after : Word → BitVec 8} {filled : Nat} (h : At before filled)
    (frame : ViewFrame.Region before after 0x80fff814#32 449) : At after filled :=
  ⟨MainHeadLayout.preserve h.head frame,h.bound,
    (ViewFrame.word frame 112 (by decide)).trans h.capacity,
    (ViewFrame.word frame 436 (by decide)).trans h.filledPtr,
    (ViewFrame.word frame 84 (by decide)).trans h.filled,
    (ViewFrame.word frame 440 (by decide)).trans h.uartPtr⟩
end E5R.Thermostat.MainHeaderLayout
