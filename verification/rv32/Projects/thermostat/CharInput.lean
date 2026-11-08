import Projects.thermostat.CharSave
import Projects.thermostat.CharAscii
import Projects.thermostat.ViewFrame
import Projects.thermostat.WordRegions
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CharInput
open E5R E5R.Thermostat

/-- The char scratch byte belongs to this function's stack, so no false
    source/stack nonaliasing premise is imposed. Output and Cursor are disjoint. -/
structure Data (B : Board) (ram : Word → BitVec 8) (sp obj dst : Word) (cap pos : Nat) : Prop where
  stack : Memory.Block B sp 32
  stackAligned : sp.toNat%4 = 0
  object : Memory.Block B obj 12
  objectAligned : obj.toNat%4 = 0
  capacity : cap < 2^32
  position : pos ≤ cap
  pointerWord : ramRead ram obj .w = dst
  capacityWord : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap
  positionWord : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos
  output : Memory.Block B dst cap
  nowrap : dst.toNat+cap < 2^32
  objectStack : WordRegions.Disjoint obj 12 sp 32
  outputStack : WordRegions.Disjoint dst cap sp 32
  objectOutput : WordRegions.Disjoint obj 12 dst cap

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) (b : BitVec 8) :=
  CharAscii.memory (CharSave.memory ram sp c) sp b

theorem region (ram : Word → BitVec 8) (sp : Word) (c : Core) (b : BitVec 8) (obj : Word) (n : Nat)
    (hs : WordRegions.Disjoint obj n sp 32) : ViewFrame.Region ram (memory ram sp c b) obj n := by
  intro i
  rw [memory,CharAscii.frame _ _ _ _ (by
    intro j
    have hj := j.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hs i ⟨8+j.val,by omega⟩)]
  exact CharSave.frame ram sp c _ (hs i)

theorem data_frame {B ram sp obj dst cap pos} (h : Data B ram sp obj dst cap pos) (c : Core) (b : BitVec 8) :
    Data B (memory ram sp c b) sp obj dst cap pos := by
  have ho := region ram sp c b obj 12 h.objectStack
  refine ⟨h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    h.output,h.nowrap,h.objectStack,h.outputStack,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simp only [BitVec.add_zero] at hh
  exact hh.trans h.pointerWord

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) (b : BitVec 8) :
    ViewFrame.Region (CharSave.memory ram sp c) (memory ram sp c b) (sp+12#32) 20 := by
  intro i
  apply CharAscii.frame
  intro j
  have hi := i.isLt
  have hj := j.isLt
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using Bytes.offset_ne sp (12+i.val) (8+j.val) (by omega) (by omega) (by omega)

theorem scratch {B ram sp obj dst cap pos} (h : Data B ram sp obj dst cap pos) (c : Core) (b : BitVec 8) :
    ReadBytes.Span B img (memory ram sp c b) (sp+8#32) [b] := by
  apply ReadBytes.of_ram
  apply Bytes.of_block
  · exact Memory.sub_block h.stack (off := 8) (m := 1) (by decide) (by decide)
  · change 1 < 2^32;decide
  · intro i
    have hi : i.val = 0 := by have := i.isLt;change i.val < 1 at this;omega
    change memory ram sp c b ((sp+8#32)+BitVec.ofNat 32 i.val) = [b][i.val]
    simp only [hi,List.getElem_cons_zero]
    change memory ram sp c b ((sp+8#32)+0#32) = b
    rw [BitVec.add_zero]
    exact CharAscii.byte _ _ _
theorem frame (ram : Word → BitVec 8) (sp : Word) (c : Core) (b : BitVec 8) (x : Word)
    (hx : ∀ i : Fin 32, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp c b x = ram x := by
  rw [memory,CharAscii.frame _ _ _ _ (by
    intro j
    have hj := j.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨8+j.val,by omega⟩)]
  exact CharSave.frame ram sp c x hx
end E5R.Thermostat.CharInput
