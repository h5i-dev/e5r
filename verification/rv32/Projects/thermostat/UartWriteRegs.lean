import Projects.thermostat.CopyRegs
namespace E5R.Thermostat.UartWriteRegs
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r

theorem trans {a b c} (h : Frame a b) (k : Frame b c) : Frame a c := fun r h11 h12 h13 h14 h15 h16 h17 =>
  (k r h11 h12 h13 h14 h15 h16 h17).trans (h r h11 h12 h13 h14 h15 h16 h17)

theorem returned {c d} (hpc : d.pc=c.get 1 &&& ~~~1) (hcsr : d.sameCsr c) (hf : Frame c d) : FormatCursor.Returned c d := by
  apply CopyRegs.returned hpc (hf 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hcsr
  intro r hr
  exact hf r (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 12 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 13 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 16 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 17 hr (by decide) (by decide) (by decide) (by decide))
end E5R.Thermostat.UartWriteRegs
