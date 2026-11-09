import Projects.thermostat.FormatStoredSpace
import Projects.thermostat.StackAccess
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackFormatSpace
open E5R E5R.Thermostat FormatSpace
structure Space (ram : Word → BitVec 8) (p obj dst : Word) (cap pos : Nat) : Prop where
  arena : Memory.Block StackBoard.board p 224
  aligned : p.toNat%4 = 0
  object : Memory.Block StackBoard.board obj 12
  objectAligned : obj.toNat%4 = 0
  capacity : cap < 2^32
  position : pos ≤ cap
  pointerWord : ramRead ram obj .w = dst
  capacityWord : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap
  positionWord : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos
  output : Memory.Block StackBoard.board dst cap
  nowrap : dst.toNat+cap < 2^32
  objectArena : WordRegions.Disjoint obj 12 p 224
  outputArena : WordRegions.Disjoint dst cap p 224
  objectOutput : WordRegions.Disjoint obj 12 dst cap

theorem after_append {ram r p obj dst cap pos xs} (h : Space ram p obj dst cap pos)
    (he : AppendEffect.Effect StackBoard.board ram r p obj dst 224 cap pos xs)
    (hf : pos+xs.length ≤ cap) : Space r p obj dst cap (pos+xs.length) := by
  exact ⟨h.arena,h.aligned,h.object,h.objectAligned,h.capacity,hf,he.pointer,he.capacity,
    by simpa only [Cursor.nextPosition,ite_eq_left hf] using he.position,
    h.output,h.nowrap,h.objectArena,h.outputArena,h.objectOutput⟩

theorem cursor {ram p obj dst cap pos} (h : Space ram p obj dst cap pos)
    (off : Nat) (hoff : off+32 ≤ 224) (halign : off%4 = 0)
    (src : Word) (xs : List (BitVec 8))
    (hs : ReadBytes.Span StackBoard.board img ram src xs) (hlen : xs.length < 16)
    (hro : ∀ i : Fin xs.length, StackBoard.board.inRam (src+BitVec.ofNat 32 i.val) 1 = false) :
    CursorInput.Layout StackBoard.board ram (p+BitVec.ofNat 32 off) obj src dst cap pos xs := by
  have hb := Memory.sub_block h.arena (off := off) (m := 32) (by omega) hoff
  refine ⟨hb,?_,h.object,h.objectAligned,h.capacity,h.position,h.pointerWord,h.capacityWord,h.positionWord,
    hs,hlen,h.output,h.nowrap,Subregion.right h.objectArena off 32 hoff,
    WordRegions.outside_ram hro hb,Subregion.right h.outputArena off 32 hoff,
    WordRegions.outside_ram hro h.output,h.objectOutput⟩
  have he : off = 4*(off/4) := by omega
  rw [he]
  exact Memory.word_aligned p (off/4) h.aligned

theorem char {ram p obj dst cap pos} (h : Space ram p obj dst cap pos) :
    CharInput.Data StackBoard.board ram (p+16#32) obj dst cap pos := by
  exact ⟨Memory.sub_block h.arena (off := 16) (m := 32) (by decide) (by decide),
    Memory.word_aligned p 4 h.aligned,h.object,h.objectAligned,h.capacity,h.position,
    h.pointerWord,h.capacityWord,h.positionWord,h.output,h.nowrap,
    Subregion.right h.objectArena 16 32 (by decide),Subregion.right h.outputArena 16 32 (by decide),h.objectOutput⟩
theorem stored {ram p obj dst cap pos} (h : Space ram p obj dst cap pos) :
    Space (FormatArgumentCall.memory ram (p+160#32) obj) p obj dst cap pos := by
  have ho := stored_region (obj := obj) (ram := ram) h.objectArena
  refine ⟨h.arena,h.aligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,
    (ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    h.output,h.nowrap,h.objectArena,h.outputArena,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.pointerWord)

theorem format_stored {ram p obj dst cap pos} (h : Space ram p obj dst cap pos)
    (src : Word) (xs : List (BitVec 8))
    (hs : ReadBytes.Span StackBoard.board img (FormatArgumentCall.memory ram (p+160#32) obj) src xs)
    (hlen : xs.length < 16)
    (hro : ∀ i : Fin xs.length, StackBoard.board.inRam (src+BitVec.ofNat 32 i.val) 1 = false) :
    FormatInput.Data StackBoard.board (FormatArgumentCall.memory ram (p+160#32) obj)
      (p+96#32) (p+160#32) obj src dst 0x60000020#32 cap pos xs := by
  have hh := stored h
  have hw := FormatArgumentCall.words ram (p+160#32) obj
  refine ⟨Memory.sub_block h.arena (off := 96) (m := 64) (by decide) (by decide),Memory.word_aligned p 24 h.aligned,
    Memory.sub_block h.arena (off := 160) (m := 12) (by decide) (by decide),Memory.word_aligned p 40 h.aligned,
    hw.1,hw.2.1,hw.2.2.1,by decide +kernel,
    offsets_disjoint p 160 12 96 64 (by decide) (by decide) (by decide),?_,
    Subregion.right h.objectArena 96 64 (by decide),
    WordRegions.outside_ram hro (Memory.sub_block h.arena (off := 96) (m := 64) (by decide) (by decide)),
    Subregion.right h.outputArena 96 64 (by decide)⟩
  simpa only [BitVec.add_assoc,show (96#32+32#32) = 128#32 by decide +kernel] using cursor hh 128 (by decide) (by decide) src xs hs hlen hro
end E5R.Thermostat.StackFormatSpace
