import Projects.thermostat.HeadSaved
namespace E5R.Thermostat.HeadSavedTail
open E5R E5R.Thermostat

/-- The actual thirteen parser ABI slots occupy only bytes 332..383.
    Scratch/header stores below them may change the rest of the stack frame. -/
theorem preserve {before after : Word → BitVec 8} {sp : Word} {values : Reg → Word}
    (h : HeadSaved.At before sp values) (frame : ViewFrame.Region before after (sp+332#32) 52) :
    HeadSaved.At after sp values := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have word : ramRead after (sp+380#32) .w=ramRead before (sp+380#32) .w := by
      simpa only [show (sp+332#32)+48#32=sp+380#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 48 (by decide)
    exact word.trans h.x1
  · have word : ramRead after (sp+376#32) .w=ramRead before (sp+376#32) .w := by
      simpa only [show (sp+332#32)+44#32=sp+376#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 44 (by decide)
    exact word.trans h.x8
  · have word : ramRead after (sp+372#32) .w=ramRead before (sp+372#32) .w := by
      simpa only [show (sp+332#32)+40#32=sp+372#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 40 (by decide)
    exact word.trans h.x9
  · have word : ramRead after (sp+368#32) .w=ramRead before (sp+368#32) .w := by
      simpa only [show (sp+332#32)+36#32=sp+368#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 36 (by decide)
    exact word.trans h.x18
  · have word : ramRead after (sp+364#32) .w=ramRead before (sp+364#32) .w := by
      simpa only [show (sp+332#32)+32#32=sp+364#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 32 (by decide)
    exact word.trans h.x19
  · have word : ramRead after (sp+360#32) .w=ramRead before (sp+360#32) .w := by
      simpa only [show (sp+332#32)+28#32=sp+360#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 28 (by decide)
    exact word.trans h.x20
  · have word : ramRead after (sp+356#32) .w=ramRead before (sp+356#32) .w := by
      simpa only [show (sp+332#32)+24#32=sp+356#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 24 (by decide)
    exact word.trans h.x21
  · have word : ramRead after (sp+352#32) .w=ramRead before (sp+352#32) .w := by
      simpa only [show (sp+332#32)+20#32=sp+352#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 20 (by decide)
    exact word.trans h.x22
  · have word : ramRead after (sp+348#32) .w=ramRead before (sp+348#32) .w := by
      simpa only [show (sp+332#32)+16#32=sp+348#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 16 (by decide)
    exact word.trans h.x23
  · have word : ramRead after (sp+344#32) .w=ramRead before (sp+344#32) .w := by
      simpa only [show (sp+332#32)+12#32=sp+344#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 12 (by decide)
    exact word.trans h.x24
  · have word : ramRead after (sp+340#32) .w=ramRead before (sp+340#32) .w := by
      simpa only [show (sp+332#32)+8#32=sp+340#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 8 (by decide)
    exact word.trans h.x25
  · have word : ramRead after (sp+336#32) .w=ramRead before (sp+336#32) .w := by
      simpa only [show (sp+332#32)+4#32=sp+336#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 4 (by decide)
    exact word.trans h.x26
  · have word : ramRead after (sp+332#32) .w=ramRead before (sp+332#32) .w := by
      simpa only [show (sp+332#32)+0#32=sp+332#32 by rw [BitVec.add_assoc];rfl] using ViewFrame.word frame 0 (by decide)
    exact word.trans h.x27
end E5R.Thermostat.HeadSavedTail
