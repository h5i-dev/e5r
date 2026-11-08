import Projects.thermostat.MainCloseValueChain
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseValueContext
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠15 → r≠22 → r≠23 → r≠24 → r≠25 → r≠26 → d.get r=c.get r

theorem Frame.trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r a b c d e f g i j => (k r a b c d e f g i j).trans (h r a b c d e f g i j)

/-- Literal registers established by the actual function setup, preserved
    throughout the value scanner and trim/token loop. -/
structure Literals (c : Core) : Prop extends MainCloseValueChain.Literals c where
  c8 : c.get 8=44#32
  c9 : c.get 9=23#32
  c18 : c.get 18=5#32
  c21 : c.get 21=0x80001b#32
  c29 : c.get 29=101#32

theorem Literals.preserve {c d : Core} (h : Literals c) (frame : Frame c d) : Literals d := by
  constructor
  · exact ⟨(frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c6,
      (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c19,
      (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c7,
      (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c20⟩
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c8
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c9
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c18
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c21
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.c29
end E5R.Thermostat.MainCloseValueContext
