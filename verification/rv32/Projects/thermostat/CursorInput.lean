import Projects.thermostat.CursorSave
import Projects.thermostat.ReadFrame
import Projects.thermostat.Subregion
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CursorInput
open E5R E5R.Thermostat

/-- Valid Cursor slice, source bytes and real caller allocations. -/
structure Layout (B : Board) (ram : Word → BitVec 8) (sp obj src dst : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  stack : Memory.Block B sp 32
  stackAligned : sp.toNat%4 = 0
  object : Memory.Block B obj 12
  objectAligned : obj.toNat%4 = 0
  capacity : cap < 2^32
  position : pos ≤ cap
  pointerWord : ramRead ram obj .w = dst
  capacityWord : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap
  positionWord : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos
  source : ReadBytes.Span B img ram src xs
  short : xs.length < 16
  output : Memory.Block B dst cap
  nowrap : dst.toNat+cap < 2^32
  objectStack : WordRegions.Disjoint obj 12 sp 32
  sourceStack : WordRegions.Disjoint src xs.length sp 32
  outputStack : WordRegions.Disjoint dst cap sp 32
  sourceOutput : WordRegions.Disjoint src xs.length dst cap
  objectOutput : WordRegions.Disjoint obj 12 dst cap

structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj src dst : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  pc : c.pc = 0x800022a0#32
  spReg : c.get 2 = sp+32#32
  objectReg : c.get 10 = obj
  sourceReg : c.get 11 = src
  lengthReg : c.get 12 = BitVec.ofNat 32 xs.length
  stack : Memory.Block B sp 32
  stackAligned : sp.toNat%4 = 0
  object : Memory.Block B obj 12
  objectAligned : obj.toNat%4 = 0
  capacity : cap < 2^32
  position : pos ≤ cap
  pointerWord : ramRead ram obj .w = dst
  capacityWord : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap
  positionWord : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos
  source : ReadBytes.Span B img ram src xs
  short : xs.length < 16
  output : Memory.Block B dst cap
  nowrap : dst.toNat+cap < 2^32
  objectStack : WordRegions.Disjoint obj 12 sp 32
  sourceStack : WordRegions.Disjoint src xs.length sp 32
  outputStack : WordRegions.Disjoint dst cap sp 32
  sourceOutput : WordRegions.Disjoint src xs.length dst cap
  objectOutput : WordRegions.Disjoint obj 12 dst cap

theorem saved_region {B c ram sp obj src dst cap pos xs} (_h : Pre B c ram sp obj src dst cap pos xs)
    (a : Word) (n : Nat) (hs : WordRegions.Disjoint a n sp 32) :
    ViewFrame.Region ram (CursorSave.memory ram sp c) a n := fun i => CursorSave.frame ram sp c _ (hs i)

theorem saved_source {B c ram sp obj src dst cap pos xs} (h : Pre B c ram sp obj src dst cap pos xs) :
    ReadBytes.Span B img (CursorSave.memory ram sp c) src xs := ReadFrame.span h.source (saved_region h src xs.length h.sourceStack)
theorem saved_layout {B c ram sp obj src dst cap pos xs} (h : Pre B c ram sp obj src dst cap pos xs) :
    Layout B (CursorSave.memory ram sp c) sp obj src dst cap pos xs := by
  have ho := saved_region h obj 12 h.objectStack
  refine ⟨h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    saved_source h,h.short,h.output,h.nowrap,h.objectStack,h.sourceStack,h.outputStack,h.sourceOutput,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.pointerWord)
end E5R.Thermostat.CursorInput
