import Projects.thermostat.OutputEffect
import Projects.thermostat.StoreWords
namespace E5R.Thermostat.ResponseHeadEnvelope
open E5R E5R.Thermostat

def Frame (before after : Word → BitVec 8) (sp dst : Word) : Prop :=
  ∀ x, (∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 192, x≠dst+BitVec.ofNat 32 i.val) → after x=before x

theorem refl (ram : Word → BitVec 8) (sp dst : Word) : Frame ram ram sp dst := fun _ _ _ => rfl

theorem trans {a b c sp dst} (h : Frame a b sp dst) (k : Frame b c sp dst) : Frame a c sp dst :=
  fun x hs hd => (k x hs hd).trans (h x hs hd)

theorem effect {B before after sp dst scratch pos xs}
    (h : OutputEffect.Effect B before after sp dst scratch pos xs)
    (hs : scratch≤16) (hd : pos+xs.length≤192) : Frame before after sp dst := by
  intro x hx ho
  apply h.frame x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩)
  intro i
  have hh := ho ⟨pos+i.val,by have := i.isLt;omega⟩
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hh

theorem word {before after sp dst} (h : Frame before after sp dst)
    (hsep : WordRegions.Disjoint sp 96 dst 192) (off : Nat) (hlo : 16≤off) (hhi : off+4≤96) :
    ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead before (sp+BitVec.ofNat 32 off) .w := by
  apply ramRead_w_congr
  intro i hi
  apply h _
  · intro j
    simpa only [BitVec.add_zero] using StoreWords.offsets sp off 4 0 16 (by omega) (by decide) (by omega) ⟨i,hi⟩ j
  · intro j
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hsep ⟨off+i,by omega⟩ j

theorem region {before after sp dst p n} (h : Frame before after sp dst)
    (hs : WordRegions.Disjoint p n sp 16) (hd : WordRegions.Disjoint p n dst 192) :
    ViewFrame.Region before after p n := fun i => h _ (hs i) (hd i)
end E5R.Thermostat.ResponseHeadEnvelope
