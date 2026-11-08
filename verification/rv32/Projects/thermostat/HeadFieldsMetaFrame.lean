import Projects.thermostat.HeadFieldsMeta
namespace E5R.Thermostat.HeadFieldsMetaFrame
open E5R E5R.Thermostat

/-- Stable parser metadata depends only on its actual bytes8..55. Header-array
    and flag stores preserve it by proving this byte region unchanged. -/
theorem preserve {before after : Word → BitVec 8} {sp : Word} {length cap : Nat}
    (h : HeadFieldsMeta.At before sp length cap) (frame : ViewFrame.Region before after (sp+8#32) 48) :
    HeadFieldsMeta.At after sp length cap := by
  have word (off : Nat) (hl : 8≤off) (hu : off+4≤56) :
      ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead before (sp+BitVec.ofNat 32 off) .w := by
    have w := ViewFrame.word frame (off-8) (by omega)
    have a : 8#32+BitVec.ofNat 32 (off-8)=BitVec.ofNat 32 off := by
      change BitVec.ofNat 32 8+BitVec.ofNat 32 (off-8)=BitVec.ofNat 32 off
      rw [←BitVec.ofNat_add,Nat.add_sub_of_le hl]
    simpa only [BitVec.add_assoc,a] using w
  exact ⟨(word 8 (by decide) (by decide)).trans h.body,
    (word 12 (by decide) (by decide)).trans h.before,(word 16 (by decide) (by decide)).trans h.next,
    (word 32 (by decide) (by decide)).trans h.mask,(word 36 (by decide) (by decide)).trans h.maximum,
    (word 40 (by decide) (by decide)).trans h.limit,(word 44 (by decide) (by decide)).trans h.buffer,
    (word 48 (by decide) (by decide)).trans h.raw,(word 52 (by decide) (by decide)).trans h.output⟩
end E5R.Thermostat.HeadFieldsMetaFrame
