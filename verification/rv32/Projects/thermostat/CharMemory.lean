import Projects.thermostat.CharInput
import Projects.thermostat.Subregion
import Projects.thermostat.ByteWrite
import Projects.thermostat.StoreBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CharMemory
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj dst : Word) (pos : Nat) (xs : List (BitVec 8)) : Word → BitVec 8 :=
  ramWrite (ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs) (obj+8#32) (BitVec.ofNat 32 (pos+xs.length)) .w

theorem frame (ram : Word → BitVec 8) (obj dst x : Word) (pos : Nat) (xs : List (BitVec 8))
    (ho : ∀ i : Fin xs.length, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val)
    (hp : ∀ i : Fin 4, x ≠ (obj+8#32)+BitVec.ofNat 32 i.val) : memory ram obj dst pos xs x = ram x := by
  rw [memory,StoreBytes.frame _ _ _ _ .w hp]
  exact ByteWrite.frame ram _ _ xs ho

theorem stack {B ram sp obj dst cap pos b} (h : CharInput.Data B ram sp obj dst cap pos)
    (hf : 1 ≤ cap-pos) : ViewFrame.Region ram (memory ram obj dst pos [b]) sp 32 := by
  have hout := WordRegions.symm (Subregion.left h.outputStack pos 1 (by have := h.position;omega))
  intro i
  apply frame
  · exact hout i
  · intro j
    have hh := h.objectStack ⟨8+j.val,by have hj : j.val < 4 := j.isLt;omega⟩ i
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using Ne.symm hh

theorem position (ram : Word → BitVec 8) (obj dst : Word) (pos : Nat) (b : BitVec 8) :
    ramRead (memory ram obj dst pos [b]) (obj+8#32) .w = BitVec.ofNat 32 (pos+1) := ramRead_ramWrite_w _ _ _

theorem object_copied {B ram sp obj dst cap pos b} (h : CharInput.Data B ram sp obj dst cap pos)
    (hf : 1 ≤ cap-pos) :
    ViewFrame.Region ram (ByteWrite.write ram (dst+BitVec.ofNat 32 pos) [b]) obj 12 :=
  ByteWrite.region (Subregion.right h.objectOutput pos 1 (by have := h.position;omega)) ram

theorem pointer {B ram sp obj dst cap pos b} (h : CharInput.Data B ram sp obj dst cap pos)
    (hf : 1 ≤ cap-pos) : ramRead (memory ram obj dst pos [b]) obj .w = dst := by
  change ramRead (ramWrite _ (obj+8#32) _ .w) obj .w = _
  rw [Memory.read_word_write_other _ _ _ _ (by
    simpa only [BitVec.add_zero] using Memory.word_disjoint obj 0 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  have hh := ViewFrame.word (object_copied (b := b) h hf) 0 (by decide)
  simp only [BitVec.add_zero] at hh
  exact hh.trans h.pointerWord

theorem capacity {B ram sp obj dst cap pos b} (h : CharInput.Data B ram sp obj dst cap pos)
    (hf : 1 ≤ cap-pos) : ramRead (memory ram obj dst pos [b]) (obj+4#32) .w = BitVec.ofNat 32 cap := by
  change ramRead (ramWrite _ (obj+8#32) _ .w) (obj+4#32) .w = _
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint obj 4 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact (ViewFrame.word (object_copied (b := b) h hf) 4 (by decide)).trans h.capacityWord

theorem copied {B ram sp obj dst cap pos b} (h : CharInput.Data B ram sp obj dst cap pos)
    (hf : 1 ≤ cap-pos) : Bytes.Span B (memory ram obj dst pos [b]) (dst+BitVec.ofNat 32 pos) [b] := by
  have hb := ByteWrite.span (ram := ram) (xs := [b]) (Subregion.block h.output h.capacity h.nowrap pos 1 (by have := h.position;omega)) (by change 1 < 2^32;decide)
  apply ViewFrame.span hb
  intro i
  apply StoreBytes.frame _ _ _ _ .w
  intro j
  have hh := Subregion.right h.objectOutput pos 1 (by have := h.position;omega) ⟨8+j.val,by have hj : j.val < 4 := j.isLt;omega⟩ i
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using Ne.symm hh
end E5R.Thermostat.CharMemory
