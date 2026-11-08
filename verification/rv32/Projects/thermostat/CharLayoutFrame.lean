import Projects.thermostat.CharInput
namespace E5R.Thermostat.CharInput
open E5R E5R.Thermostat

theorem preserve {B ram ram' sp obj dst cap pos} (h : Data B ram sp obj dst cap pos)
    (ho : ViewFrame.Region ram ram' obj 12) : Data B ram' sp obj dst cap pos := by
  refine ⟨h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    h.output,h.nowrap,h.objectStack,h.outputStack,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simp only [BitVec.add_zero] at hh
  exact hh.trans h.pointerWord
end E5R.Thermostat.CharInput
