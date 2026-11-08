import Projects.thermostat.I16Digits
import Projects.thermostat.CharLayoutFrame
import Projects.thermostat.CursorInput
import Projects.thermostat.I16Length
namespace E5R.Thermostat.I16Input
open E5R E5R.Thermostat

/-- Real caller allocations and default Formatter fields. Digit bytes and
    formatter output are conclusions of execution, never input assumptions. -/
structure Data (B : Board) (ram : Word → BitVec 8) (p ptr fmt obj dst : Word) (cap pos : Nat) (v : BitVec 16) : Prop
    extends CharInput.Data B ram (p+16#32) obj dst cap pos where
  arena : Memory.Block B p 160
  arenaAligned : p.toNat%4 = 0
  inputRam : Memory.Block B ptr 2
  inputAligned : ptr.toNat%2 = 0
  inputValue : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v
  formatter : Memory.Block B fmt 14
  formatterAligned : fmt.toNat%4 = 0
  writerWord : ramRead ram fmt .w = obj
  vtableWord : ramRead ram (fmt+4#32) .w = 0x80005c04#32
  flagsWord : ramRead ram (fmt+8#32) .w = 0x60000020#32
  widthWord : ramRead ram (fmt+12#32) .h = 0#32
  objectArena : WordRegions.Disjoint obj 12 p 160
  outputArena : WordRegions.Disjoint dst cap p 160
  inputArena : WordRegions.Disjoint ptr 2 p 160
  formatterArena : WordRegions.Disjoint fmt 14 p 160

def ScratchFrame (p : Word) (before after : Word → BitVec 8) : Prop :=
  ∀ x, (∀ i : Fin 16, x ≠ (p+144#32)+BitVec.ofNat 32 i.val) → after x = before x

theorem object_region {B ram r p ptr fmt obj dst cap pos v} (h : Data B ram p ptr fmt obj dst cap pos v)
    (hf : ScratchFrame p ram r) : ViewFrame.Region ram r obj 12 := by
  intro i
  apply hf
  intro j
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using h.objectArena i ⟨144+j.val,by have := j.isLt;omega⟩

theorem formatter_region {B ram r p ptr fmt obj dst cap pos v} (h : Data B ram p ptr fmt obj dst cap pos v)
    (hf : ScratchFrame p ram r) : ViewFrame.Region ram r fmt 14 := by
  intro i
  apply hf
  intro j
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using h.formatterArena i ⟨144+j.val,by have := j.isLt;omega⟩

theorem source_arena {p : Word} {xs : List (BitVec 8)} {off : Nat} (he : off+xs.length = 8) :
    ∀ i : Fin xs.length, ∃ j : Fin 160, ((p+144#32)+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val = p+BitVec.ofNat 32 j.val := by
  intro i
  refine ⟨⟨144+off+i.val,by have := i.isLt;omega⟩,?_⟩
  simp only [BitVec.add_assoc,←BitVec.ofNat_add]

theorem layout {B ram r p ptr fmt obj dst cap pos v} (h : Data B ram p ptr fmt obj dst cap pos v)
    (hf : ScratchFrame p ram r)
    (hs : ReadBytes.Span B img r ((p+144#32)+BitVec.ofNat 32 (I16Ready.offset v.toInt.natAbs)) (ReplyJson.decimal v.toInt.natAbs)) :
    CursorInput.Layout B r (p+112#32) obj ((p+144#32)+BitVec.ofNat 32 (I16Ready.offset v.toInt.natAbs)) dst cap pos (ReplyJson.decimal v.toInt.natAbs) := by
  have hn := ReplyJsonBounds.magnitude v
  have he := I16Ready.source_end v.toInt.natAbs hn
  have ho := object_region h hf
  refine ⟨Memory.sub_block h.arena (off := 112) (m := 32) (by decide) (by decide),Memory.word_aligned p 28 h.arenaAligned,
    h.object,h.objectAligned,h.capacity,h.position,?_,(ViewFrame.word ho 4 (by decide)).trans h.capacityWord,
    (ViewFrame.word ho 8 (by decide)).trans h.positionWord,hs,?_,h.output,h.nowrap,?_,?_,?_,?_,h.objectOutput⟩
  · have hw := ViewFrame.word ho 0 (by decide)
    simp only [BitVec.add_zero] at hw
    exact hw.trans h.pointerWord
  · have hl := ReplyJsonBounds.decimal_length 5 v.toInt.natAbs (by decide) (by omega)
    omega
  · exact Subregion.right h.objectArena 112 32 (by decide)
  · intro i j
    have hi := i.isLt;have hj := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (144+I16Ready.offset v.toInt.natAbs+i.val) (112+j.val)
      (by omega) (by omega) (by omega)
  · exact Subregion.right h.outputArena 112 32 (by decide)
  · intro i j
    obtain ⟨k,hk⟩ := source_arena he i
    rw [hk]
    exact Ne.symm (h.outputArena j k)
end E5R.Thermostat.I16Input
