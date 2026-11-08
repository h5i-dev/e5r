import Projects.thermostat.HeadStackMemory
namespace E5R.Thermostat.HeadSaved
open E5R E5R.Thermostat

structure At (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) : Prop where
  x1 : ramRead ram (sp+380#32) .w=saved 1
  x8 : ramRead ram (sp+376#32) .w=saved 8
  x9 : ramRead ram (sp+372#32) .w=saved 9
  x18 : ramRead ram (sp+368#32) .w=saved 18
  x19 : ramRead ram (sp+364#32) .w=saved 19
  x20 : ramRead ram (sp+360#32) .w=saved 20
  x21 : ramRead ram (sp+356#32) .w=saved 21
  x22 : ramRead ram (sp+352#32) .w=saved 22
  x23 : ramRead ram (sp+348#32) .w=saved 23
  x24 : ramRead ram (sp+344#32) .w=saved 24
  x25 : ramRead ram (sp+340#32) .w=saved 25
  x26 : ramRead ram (sp+336#32) .w=saved 26
  x27 : ramRead ram (sp+332#32) .w=saved 27

structure CoreAt (c : Core) (saved : Reg → Word) : Prop where
  x1 : c.get 1=saved 1
  x8 : c.get 8=saved 8
  x9 : c.get 9=saved 9
  x18 : c.get 18=saved 18
  x19 : c.get 19=saved 19
  x20 : c.get 20=saved 20
  x21 : c.get 21=saved 21
  x22 : c.get 22=saved 22
  x23 : c.get 23=saved 23
  x24 : c.get 24=saved 24
  x25 : c.get 25=saved 25
  x26 : c.get 26=saved 26
  x27 : c.get 27=saved 27

theorem stored (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :
    At (HeadStackSave.memory ram sp saved) sp saved := by
  exact ⟨HeadStackMemory.saved1 ram sp saved,
    HeadStackMemory.saved8 ram sp saved,
    HeadStackMemory.saved9 ram sp saved,
    HeadStackMemory.saved18 ram sp saved,
    HeadStackMemory.saved19 ram sp saved,
    HeadStackMemory.saved20 ram sp saved,
    HeadStackMemory.saved21 ram sp saved,
    HeadStackMemory.saved22 ram sp saved,
    HeadStackMemory.saved23 ram sp saved,
    HeadStackMemory.saved24 ram sp saved,
    HeadStackMemory.saved25 ram sp saved,
    HeadStackMemory.saved26 ram sp saved,
    HeadStackMemory.saved27 ram sp saved⟩

theorem preserve {before after sp saved} (h : At before sp saved)
    (frame : ViewFrame.Region before after sp 384) : At after sp saved := by
  exact ⟨(ViewFrame.word frame 380 (by decide)).trans h.x1,
    (ViewFrame.word frame 376 (by decide)).trans h.x8,
    (ViewFrame.word frame 372 (by decide)).trans h.x9,
    (ViewFrame.word frame 368 (by decide)).trans h.x18,
    (ViewFrame.word frame 364 (by decide)).trans h.x19,
    (ViewFrame.word frame 360 (by decide)).trans h.x20,
    (ViewFrame.word frame 356 (by decide)).trans h.x21,
    (ViewFrame.word frame 352 (by decide)).trans h.x22,
    (ViewFrame.word frame 348 (by decide)).trans h.x23,
    (ViewFrame.word frame 344 (by decide)).trans h.x24,
    (ViewFrame.word frame 340 (by decide)).trans h.x25,
    (ViewFrame.word frame 336 (by decide)).trans h.x26,
    (ViewFrame.word frame 332 (by decide)).trans h.x27⟩
end E5R.Thermostat.HeadSaved
