import Projects.thermostat.HeadHeaderActionFrame
import Projects.thermostat.HeadHeaderHost
namespace E5R.Thermostat.HeadHeaderMemoryFrame
open E5R E5R.Thermostat

def At (before after : Word → BitVec 8) (sp : Word) : Prop :=
  ∀ off len : Nat, off+len≤4294967296 → 4≤off → (off+len≤312 ∨ 327≤off) →
    ViewFrame.Region before after (sp+BitVec.ofNat 32 off) len

theorem refl (ram : Word → BitVec 8) (sp : Word) : At ram ram sp := fun _ _ _ _ _ _ => rfl

theorem host {ram after sp} (effect : after=ram ∨ after=HeadHostFlagStore.memory ram sp) : At ram after sp := by
  intro off len bound _ outside
  rcases effect with same | store
  · rw [same];intro _;rfl
  · rw [store]
    exact HeadHostFlagMemory.region ram sp off len bound (by omega)

theorem alt {ram after sp} (ve le : Nat)
    (effect : HeadHeaderActionView.Effect (HeadHeaderScratch.memory ram sp ve le) after sp) : At ram after sp :=
  fun off len bound scratch outside => HeadHeaderActionFrame.alt_region ve le effect off len bound scratch outside

theorem word {before after sp} (h : At before after sp) (off : Nat)
    (bound : off+4≤4294967296) (scratch : 4≤off) (outside : off+4≤312 ∨ 327≤off) :
    ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead before (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (h off 4 bound scratch outside) 0 (by decide)

theorem metadata {before after sp length cap} (h : At before after sp) (view : HeadFieldsMeta.At before sp length cap) :
    HeadFieldsMeta.At after sp length cap :=
  ⟨(word h 8 (by decide) (by decide) (by decide)).trans view.body,
    (word h 12 (by decide) (by decide) (by decide)).trans view.before,
    (word h 16 (by decide) (by decide) (by decide)).trans view.next,
    (word h 32 (by decide) (by decide) (by decide)).trans view.mask,
    (word h 36 (by decide) (by decide) (by decide)).trans view.maximum,
    (word h 40 (by decide) (by decide) (by decide)).trans view.limit,
    (word h 44 (by decide) (by decide) (by decide)).trans view.buffer,
    (word h 48 (by decide) (by decide) (by decide)).trans view.raw,
    (word h 52 (by decide) (by decide) (by decide)).trans view.output⟩
end E5R.Thermostat.HeadHeaderMemoryFrame
