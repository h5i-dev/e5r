import Projects.thermostat.CopyRegs
namespace E5R.Thermostat.HttpDecRegs
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠2 → r≠5 → r≠6 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r

theorem trans {a b c} (h : Frame a b) (k : Frame b c) : Frame a c := fun r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17 =>
  (k r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17).trans (h r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17)

theorem returned {c d : Core} (hp : d.pc=c.get 1 &&& ~~~1) (hsp : d.get 2=c.get 2)
    (hc : d.sameCsr c) (hf : Frame c d) : FormatCursor.Returned c d := by
  apply CopyRegs.returned hp hsp hc
  intro r hr
  exact hf r (CopyRegs.ne_low r 2 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 5 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 6 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 12 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 13 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 16 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 17 hr (by decide) (by decide) (by decide) (by decide))
end E5R.Thermostat.HttpDecRegs
