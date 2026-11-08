import Projects.thermostat.HeadHeaderAlt
namespace E5R.Thermostat.HeadHeaderActionFrame
open E5R E5R.Thermostat

theorem region {ram after : Word → BitVec 8} {sp : Word} (effect : HeadHeaderActionView.Effect ram after sp)
    (off len : Nat) (bound : off+len≤4294967296) (outside : off+len≤312 ∨ 327≤off) :
    ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) len := by
  rcases effect with same | ⟨value,cl⟩ | te
  · rw [same];intro _;rfl
  · rw [cl]
    exact HeadClStoreMemory.region ram sp value off len bound (by omega) (by omega)
  · rw [te]
    exact HeadTeFlagMemory.region ram sp off len bound (by omega)

theorem alt_region {ram after : Word → BitVec 8} {sp : Word} (ve le : Nat)
    (effect : HeadHeaderActionView.Effect (HeadHeaderScratch.memory ram sp ve le) after sp)
    (off len : Nat) (bound : off+len≤4294967296) (scratch : 4≤off) (outside : off+len≤312 ∨ 327≤off) :
    ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) len := by
  intro i
  exact (region effect off len bound outside i).trans (HeadHeaderScratch.region ram sp ve le off len bound scratch i)

theorem alt_word {ram after : Word → BitVec 8} {sp : Word} (ve le off : Nat)
    (effect : HeadHeaderActionView.Effect (HeadHeaderScratch.memory ram sp ve le) after sp)
    (bound : off+4≤4294967296) (scratch : 4≤off) (outside : off+4≤312 ∨ 327≤off) :
    ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (alt_region ve le effect off 4 bound scratch outside) 0 (by decide)

theorem alt_metadata {ram after : Word → BitVec 8} {sp : Word} {length cap : Nat} (ve le : Nat)
    (h : HeadFieldsMeta.At ram sp length cap)
    (effect : HeadHeaderActionView.Effect (HeadHeaderScratch.memory ram sp ve le) after sp) :
    HeadFieldsMeta.At after sp length cap := by
  exact ⟨(alt_word ve le 8 effect (by decide) (by decide) (by decide)).trans h.body,
    (alt_word ve le 12 effect (by decide) (by decide) (by decide)).trans h.before,
    (alt_word ve le 16 effect (by decide) (by decide) (by decide)).trans h.next,
    (alt_word ve le 32 effect (by decide) (by decide) (by decide)).trans h.mask,
    (alt_word ve le 36 effect (by decide) (by decide) (by decide)).trans h.maximum,
    (alt_word ve le 40 effect (by decide) (by decide) (by decide)).trans h.limit,
    (alt_word ve le 44 effect (by decide) (by decide) (by decide)).trans h.buffer,
    (alt_word ve le 48 effect (by decide) (by decide) (by decide)).trans h.raw,
    (alt_word ve le 52 effect (by decide) (by decide) (by decide)).trans h.output⟩
end E5R.Thermostat.HeadHeaderActionFrame
