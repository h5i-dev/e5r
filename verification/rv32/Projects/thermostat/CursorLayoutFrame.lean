import Projects.thermostat.CursorInput
import Projects.thermostat.ReadFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CursorLayoutFrame
open E5R E5R.Thermostat

theorem frame {B before after sp obj src dst cap pos xs} (h : CursorInput.Layout B before sp obj src dst cap pos xs)
    (ho : ViewFrame.Region before after obj 12) (hs : ViewFrame.Region before after src xs.length) :
    CursorInput.Layout B after sp obj src dst cap pos xs := by
  refine ⟨h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    ReadFrame.span h.source hs,h.short,h.output,h.nowrap,h.objectStack,h.sourceStack,h.outputStack,h.sourceOutput,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simp only [BitVec.add_zero] at hh
  exact hh.trans h.pointerWord
end E5R.Thermostat.CursorLayoutFrame
