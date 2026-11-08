import Projects.thermostat.FormatSpace
import Projects.thermostat.OutsideRam
import Projects.thermostat.CursorInput
import Projects.thermostat.CharInput
namespace E5R.Thermostat.FormatSpace
open E5R E5R.Thermostat

theorem cursor {ram p obj dst cap pos} (h : Space ram p obj dst cap pos)
    (off : Nat) (hoff : off+32 ≤ 224) (halign : off%4 = 0)
    (src : Word) (xs : List (BitVec 8))
    (hs : ReadBytes.Span UartPlatform.board img ram src xs) (hlen : xs.length < 16)
    (hro : ∀ i : Fin xs.length, UartPlatform.board.inRam (src+BitVec.ofNat 32 i.val) 1 = false) :
    CursorInput.Layout UartPlatform.board ram (p+BitVec.ofNat 32 off) obj src dst cap pos xs := by
  have hb := Memory.sub_block h.arena (off := off) (m := 32) (by omega) hoff
  refine ⟨hb,?_,h.object,h.objectAligned,h.capacity,h.position,h.pointerWord,h.capacityWord,h.positionWord,
    hs,hlen,h.output,h.nowrap,Subregion.right h.objectArena off 32 hoff,
    WordRegions.outside_ram hro hb,Subregion.right h.outputArena off 32 hoff,
    WordRegions.outside_ram hro h.output,h.objectOutput⟩
  have he : off = 4*(off/4) := by omega
  rw [he]
  exact Memory.word_aligned p (off/4) h.aligned

theorem char {ram p obj dst cap pos} (h : Space ram p obj dst cap pos) :
    CharInput.Data UartPlatform.board ram (p+16#32) obj dst cap pos := by
  exact ⟨Memory.sub_block h.arena (off := 16) (m := 32) (by decide) (by decide),
    Memory.word_aligned p 4 h.aligned,h.object,h.objectAligned,h.capacity,h.position,
    h.pointerWord,h.capacityWord,h.positionWord,h.output,h.nowrap,
    Subregion.right h.objectArena 16 32 (by decide),Subregion.right h.outputArena 16 32 (by decide),h.objectOutput⟩
end E5R.Thermostat.FormatSpace
