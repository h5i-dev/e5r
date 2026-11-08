import Theories.Logic
namespace E5R.Thermostat.MainGprBank
open E5R

def Frame (c d : Core) : Prop := ∀ r : Reg, r∈[21,23,26] → d.get r=c.get r

structure At (c : Core) : Prop where
  minusOne : c.get 21=0xffffffff#32
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32

theorem refl (c : Core) : Frame c c := fun _ _ => rfl

theorem trans {a b c : Core} (ab : Frame a b) (bc : Frame b c) : Frame a c := fun r safe => (bc r safe).trans (ab r safe)

theorem preserve {c d : Core} (frame : Frame c d) (h : At c) : At d :=
  ⟨(frame 21 (by decide)).trans h.minusOne,(frame 23 (by decide)).trans h.future,(frame 26 (by decide)).trans h.three⟩
end E5R.Thermostat.MainGprBank
