import Projects.thermostat.AppendEffect
namespace E5R.Thermostat.FormatLoopFrame
open E5R E5R.Thermostat

def Frame (before after : Word → BitVec 8) (p obj dst : Word) (cap : Nat) : Prop :=
  ∀ x, (∀ i : Fin 176, x ≠ p+BitVec.ofNat 32 i.val) →
    (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 12, x ≠ obj+BitVec.ofNat 32 i.val) → after x = before x

theorem of_effect {B before after p obj dst cap pos xs}
    (he : AppendEffect.Effect B before after p obj dst 176 cap pos xs) (hf : pos+xs.length ≤ cap) :
    Frame before after p obj dst cap := by
  intro x hx hd ho
  exact he.frame x hx (by intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hd ⟨pos+i.val,by have := i.isLt;omega⟩)
    (by intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using ho ⟨8+i.val,by have := i.isLt;omega⟩)

theorem trans {a b c p obj dst cap} (h : Frame a b p obj dst cap) (g : Frame b c p obj dst cap) : Frame a c p obj dst cap :=
  fun x hs hd ho => (g x hs hd ho).trans (h x hs hd ho)

theorem region {a b p obj dst cap q n} (h : Frame a b p obj dst cap)
    (hs : WordRegions.Disjoint q n p 176) (hd : WordRegions.Disjoint q n dst cap)
    (ho : WordRegions.Disjoint q n obj 12) : ViewFrame.Region a b q n := fun i => h _ (hs i) (hd i) (ho i)
end E5R.Thermostat.FormatLoopFrame
