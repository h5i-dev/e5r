import Projects.thermostat.CursorInput
namespace E5R.Thermostat.CursorInput
open E5R E5R.Thermostat

theorem preserve {B ram ram' sp obj src dst cap pos xs} (h : Layout B ram sp obj src dst cap pos xs)
    (ho : ViewFrame.Region ram ram' obj 12) (hs : ViewFrame.Region ram ram' src xs.length) :
    Layout B ram' sp obj src dst cap pos xs := by
  refine ⟨h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    ReadFrame.span h.source hs,h.short,h.output,h.nowrap,h.objectStack,h.sourceStack,h.outputStack,h.sourceOutput,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simp only [BitVec.add_zero] at hh
  exact hh.trans h.pointerWord

theorem pre_of_layout {B c ram sp obj src dst cap pos xs} (h : Layout B ram sp obj src dst cap pos xs)
    (hp : c.pc = 0x800022a0#32) (hsp : c.get 2 = sp+32#32) (h10 : c.get 10 = obj)
    (h11 : c.get 11 = src) (h12 : c.get 12 = BitVec.ofNat 32 xs.length) :
    Pre B c ram sp obj src dst cap pos xs :=
  ⟨hp,hsp,h10,h11,h12,h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,h.position,
    h.pointerWord,h.capacityWord,h.positionWord,h.source,h.short,h.output,h.nowrap,
    h.objectStack,h.sourceStack,h.outputStack,h.sourceOutput,h.objectOutput⟩
end E5R.Thermostat.CursorInput
