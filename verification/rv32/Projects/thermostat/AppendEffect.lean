import Projects.thermostat.AppendPost
import Projects.thermostat.Subregion
import Projects.thermostat.BytesAppend
namespace E5R.Thermostat.AppendEffect
open E5R E5R.Thermostat

/-- Memory behavior shared by complete append calls and format-loop segments. -/
structure Effect (B : Board) (before after : Word → BitVec 8) (sp obj dst : Word)
    (scratch cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  pointer : ramRead after obj .w = dst
  capacity : ramRead after (obj+4#32) .w = BitVec.ofNat 32 cap
  position : ramRead after (obj+8#32) .w = BitVec.ofNat 32 (Cursor.nextPosition cap pos xs.length)
  written : pos+xs.length ≤ cap → Bytes.Span B after (dst+BitVec.ofNat 32 pos) xs
  refused : ¬pos+xs.length ≤ cap → ∀ x, (∀ i : Fin scratch, x ≠ sp+BitVec.ofNat 32 i.val) → after x = before x
  frame : ∀ x, (∀ i : Fin scratch, x ≠ sp+BitVec.ofNat 32 i.val) →
    (∀ i : Fin xs.length, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 4, x ≠ (obj+8#32)+BitVec.ofNat 32 i.val) → after x = before x

theorem of_append {B c d before after sp obj dst scratch cap pos xs}
    (h : AppendPost.Post B c d before after sp obj dst scratch cap pos xs) : Effect B before after sp obj dst scratch cap pos xs :=
  ⟨h.pointer,h.capacity,h.position,h.written,h.refused,h.frame⟩

theorem of_cursor {B c d before after sp obj dst cap pos xs}
    (h : Cursor.Post B c d before after sp obj dst cap pos xs) : Effect B before after sp obj dst 32 cap pos xs :=
  ⟨h.pointer,h.capacity,h.position,h.written,h.refused,h.frame⟩

theorem of_formatter {B c d before after sp obj dst cap pos xs}
    (h : FormatCursor.Post B c d before after sp obj dst cap pos xs) : Effect B before after sp obj dst 64 cap pos xs :=
  ⟨h.pointer,h.capacity,h.position,h.written,h.refused,h.frame⟩

theorem accumulates {B before after sp obj dst scratch cap xs ys}
    (h : Effect B before after sp obj dst scratch cap xs.length ys)
    (hm : Memory.Block B dst cap) (hc : cap < 2^32) (hf : xs.length+ys.length ≤ cap)
    (hs : WordRegions.Disjoint dst cap sp scratch) (ho : WordRegions.Disjoint obj 12 dst cap)
    (hx : Bytes.Span B before dst xs) : Bytes.Span B after dst (xs++ys) := by
  apply Bytes.append_of_block hm hc hf _ (h.written hf)
  apply ViewFrame.span hx
  intro i
  have hi := i.isLt
  apply h.frame _ (hs ⟨i.val,by omega⟩)
  · intro j
    have hj := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne dst i.val (xs.length+j.val) (by omega) (by omega) (by omega)
  · intro j
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (ho ⟨8+j.val,by have := j.isLt;omega⟩ ⟨i.val,by omega⟩)

theorem region {B before after sp obj dst scratch cap pos xs p n}
    (h : Effect B before after sp obj dst scratch cap pos xs) (hf : pos+xs.length ≤ cap)
    (hs : WordRegions.Disjoint p n sp scratch) (hd : WordRegions.Disjoint p n dst cap)
    (ho : WordRegions.Disjoint p n obj 12) : ViewFrame.Region before after p n := by
  intro i
  exact h.frame _ (hs i) (Subregion.right hd pos xs.length hf i) (Subregion.right ho 8 4 (by decide) i)
end E5R.Thermostat.AppendEffect

namespace E5R.Thermostat.AppendEffect
open E5R E5R.Thermostat

theorem widen {B before after p obj dst cap pos xs off size total}
    (h : Effect B before after (p+BitVec.ofNat 32 off) obj dst size cap pos xs) (hb : off+size ≤ total) :
    Effect B before after p obj dst total cap pos xs := by
  have sub (x : Word) (hx : ∀ i : Fin total, x ≠ p+BitVec.ofNat 32 i.val) :
      ∀ i : Fin size, x ≠ (p+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val := by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨off+i.val,by have := i.isLt;omega⟩
  exact ⟨h.pointer,h.capacity,h.position,h.written,fun hn x hx => h.refused hn x (sub x hx),
    fun x hx hy ho => h.frame x (sub x hx) hy ho⟩
end E5R.Thermostat.AppendEffect

namespace E5R.Thermostat.AppendEffect
open E5R E5R.Thermostat

theorem expand {B before after p obj dst size total cap pos xs}
    (h : Effect B before after p obj dst size cap pos xs) (hb : size ≤ total) : Effect B before after p obj dst total cap pos xs := by
  have sub (x : Word) (hx : ∀ i : Fin total, x ≠ p+BitVec.ofNat 32 i.val) : ∀ i : Fin size, x ≠ p+BitVec.ofNat 32 i.val :=
    fun i => hx ⟨i.val,by have := i.isLt;omega⟩
  exact ⟨h.pointer,h.capacity,h.position,h.written,fun hn x hx => h.refused hn x (sub x hx),
    fun x hx hy ho => h.frame x (sub x hx) hy ho⟩

theorem rebase {B before mid after p obj dst size cap pos xs}
    (h : Effect B mid after p obj dst size cap pos xs)
    (hf : ∀ x, (∀ i : Fin size, x ≠ p+BitVec.ofNat 32 i.val) → mid x = before x) :
    Effect B before after p obj dst size cap pos xs :=
  ⟨h.pointer,h.capacity,h.position,h.written,fun hn x hx => (h.refused hn x hx).trans (hf x hx),
    fun x hx hy ho => (h.frame x hx hy ho).trans (hf x hx)⟩
end E5R.Thermostat.AppendEffect
