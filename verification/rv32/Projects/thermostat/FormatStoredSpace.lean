import Projects.thermostat.FormatSpaceInput
import Projects.thermostat.FormatArgumentMemory
import Projects.thermostat.FormatSource
namespace E5R.Thermostat.FormatSpace
open E5R E5R.Thermostat

theorem stored_region {ram p obj a n} (h : WordRegions.Disjoint a n p 224) :
    ViewFrame.Region ram (FormatArgumentCall.memory ram (p+160#32) obj) a n := by
  intro i
  exact FormatArgumentCall.frame ram (p+160#32) obj _ (Subregion.right h 160 16 (by decide) i)

theorem stored {ram p obj dst cap pos} (h : Space ram p obj dst cap pos) :
    Space (FormatArgumentCall.memory ram (p+160#32) obj) p obj dst cap pos := by
  have ho := stored_region (obj := obj) (ram := ram) h.objectArena
  refine ⟨h.arena,h.aligned,h.object,h.objectAligned,h.capacity,h.position,?_,
    (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,
    (ViewFrame.word ho 8 (by decide)).trans h.positionWord,
    h.output,h.nowrap,h.objectArena,h.outputArena,h.objectOutput⟩
  have hh := ViewFrame.word ho 0 (by decide)
  simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.pointerWord)

theorem offsets_disjoint (p : Word) (a n b m : Nat) (ha : a+n ≤ 2^32) (hb : b+m ≤ 2^32)
    (hne : a+n ≤ b ∨ b+m ≤ a) : WordRegions.Disjoint (p+BitVec.ofNat 32 a) n (p+BitVec.ofNat 32 b) m := by
  intro i j
  have hi := i.isLt;have hj := j.isLt
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (a+i.val) (b+j.val) (by omega) (by omega) (by omega)

theorem format_stored {ram p obj dst cap pos} (h : Space ram p obj dst cap pos)
    (src : Word) (xs : List (BitVec 8))
    (hs : ReadBytes.Span UartPlatform.board img (FormatArgumentCall.memory ram (p+160#32) obj) src xs)
    (hlen : xs.length < 16)
    (hro : ∀ i : Fin xs.length, UartPlatform.board.inRam (src+BitVec.ofNat 32 i.val) 1 = false) :
    FormatInput.Data UartPlatform.board (FormatArgumentCall.memory ram (p+160#32) obj)
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
end E5R.Thermostat.FormatSpace
