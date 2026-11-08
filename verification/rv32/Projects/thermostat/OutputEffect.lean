import Projects.thermostat.BytesAppend
import Projects.thermostat.ReadFrame
import Projects.thermostat.Subregion
namespace E5R.Thermostat.OutputEffect
open E5R E5R.Thermostat

/-- Successful output append with its checked bytes and explicit RAM frame.
    The object-free interface also covers leaf HTTP encoders. -/
structure Effect (B : Board) (before after : Word → BitVec 8) (sp dst : Word)
    (scratch pos : Nat) (xs : List (BitVec 8)) : Prop where
  written : Bytes.Span B after (dst+BitVec.ofNat 32 pos) xs
  frame : ∀ x, (∀ i : Fin scratch, x≠sp+BitVec.ofNat 32 i.val) →
    (∀ i : Fin xs.length, x≠(dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) → after x=before x

/-- A later append preserves all earlier output bytes. This follows from the
    actual memory frame and separation, rather than a formatting assumption. -/
theorem accumulates {B before after sp dst scratch cap xs ys}
    (h : Effect B before after sp dst scratch xs.length ys)
    (hm : Memory.Block B dst cap) (hc : cap<2^32) (hf : xs.length+ys.length≤cap)
    (hs : WordRegions.Disjoint dst cap sp scratch) (hx : Bytes.Span B before dst xs) :
    Bytes.Span B after dst (xs++ys) := by
  apply Bytes.append_of_block hm hc hf _ h.written
  apply ViewFrame.span hx
  intro i
  have hi := i.isLt
  apply h.frame _ (hs ⟨i.val,by omega⟩)
  intro j
  have hj := j.isLt
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using
    Bytes.offset_ne dst i.val (xs.length+j.val) (by omega) (by omega) (by omega)

theorem region {B before after sp dst scratch cap pos xs p n}
    (h : Effect B before after sp dst scratch pos xs) (hf : pos+xs.length≤cap)
    (hs : WordRegions.Disjoint p n sp scratch) (hd : WordRegions.Disjoint p n dst cap) :
    ViewFrame.Region before after p n := by
  intro i
  exact h.frame _ (hs i) (Subregion.right hd pos xs.length hf i)

theorem widen {B before after sp dst scratch total pos xs}
    (h : Effect B before after sp dst scratch pos xs) (hb : scratch≤total) :
    Effect B before after sp dst total pos xs := by
  refine ⟨h.written,fun x hx ho => h.frame x ?_ ho⟩
  intro i
  exact hx ⟨i.val,by have := i.isLt;omega⟩

theorem rebase {B before mid after sp dst scratch pos xs}
    (h : Effect B mid after sp dst scratch pos xs)
    (hf : ∀ x, (∀ i : Fin scratch, x≠sp+BitVec.ofNat 32 i.val) → mid x=before x) :
    Effect B before after sp dst scratch pos xs :=
  ⟨h.written,fun x hx ho => (h.frame x hx ho).trans (hf x hx)⟩
end E5R.Thermostat.OutputEffect
