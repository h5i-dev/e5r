import Projects.thermostat.MainHeaderLayout
namespace E5R.Thermostat.MainHeaderLayoutParts
open E5R E5R.Thermostat

/-- The copied Head occupies the gap between these two live layout regions. -/
theorem preserve {before after : Word → BitVec 8} {filled : Nat} (h : MainHeaderLayout.At before filled)
    (lo : ViewFrame.Region before after 0x80fff814#32 116)
    (hi : ViewFrame.Region before after (0x80fff814#32+432#32) 12) : MainHeaderLayout.At after filled := by
  have high (off : Nat) (bound : off+4≤12) := ViewFrame.word hi off bound
  have a432 : ramRead after (0x80fff814#32+432#32) .w=ramRead before (0x80fff814#32+432#32) .w := by simpa only [BitVec.add_zero] using high 0 (by decide)
  have a436 : ramRead after (0x80fff814#32+436#32) .w=ramRead before (0x80fff814#32+436#32) .w := by simpa only [BitVec.add_assoc,show 432#32+4#32=436#32 by decide +kernel] using high 4 (by decide)
  have a440 : ramRead after (0x80fff814#32+440#32) .w=ramRead before (0x80fff814#32+440#32) .w := by simpa only [BitVec.add_assoc,show 432#32+8#32=440#32 by decide +kernel] using high 8 (by decide)
  exact ⟨⟨(ViewFrame.word lo 108 (by decide)).trans h.head.rx,a432.trans h.head.config,
    (ViewFrame.word lo 76 (by decide)).trans h.head.headLimit,(ViewFrame.word lo 80 (by decide)).trans h.head.bodyLimit⟩,
    h.bound,(ViewFrame.word lo 112 (by decide)).trans h.capacity,a436.trans h.filledPtr,
    (ViewFrame.word lo 84 (by decide)).trans h.filled,a440.trans h.uartPtr⟩
end E5R.Thermostat.MainHeaderLayoutParts
