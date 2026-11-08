import Projects.thermostat.MainRamCall264
namespace E5R.Thermostat.MainSavedGpr
open E5R E5R.Thermostat

def regs : List Reg := [2,8,9,18,19,20,21,22,23,24,25,26,27]
def Frame (c d : Core) : Prop := ∀ rr∈regs, d.get rr=c.get rr

theorem refl (c : Core) : Frame c c := fun _ _ => rfl
theorem trans {a b c : Core} (ab : Frame a b) (bc : Frame b c) : Frame a c := fun r safe => (bc r safe).trans (ab r safe)

/-- The actual memcpy ABI certificate preserves all thirteen registers used
    by main here, including SP; RA intentionally changes at the call. -/
theorem returned {c d retPC} (saved : HeadSaved.CoreAt d (MainRamCall264.values c retPC)) (sp : d.get 2=c.get 2) : Frame c d := by
  intro rr safe
  have casesReg : rr=2 ∨ rr=8 ∨ rr=9 ∨ rr=18 ∨ rr=19 ∨ rr=20 ∨ rr=21 ∨ rr=22 ∨ rr=23 ∨ rr=24 ∨ rr=25 ∨ rr=26 ∨ rr=27 := by
    simpa only [regs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
  rcases casesReg with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst rr
  · exact sp
  · simpa only [MainRamCall264.values,show ¬((8 : Reg)=1) by decide,ite_false] using saved.x8
  · simpa only [MainRamCall264.values,show ¬((9 : Reg)=1) by decide,ite_false] using saved.x9
  · simpa only [MainRamCall264.values,show ¬((18 : Reg)=1) by decide,ite_false] using saved.x18
  · simpa only [MainRamCall264.values,show ¬((19 : Reg)=1) by decide,ite_false] using saved.x19
  · simpa only [MainRamCall264.values,show ¬((20 : Reg)=1) by decide,ite_false] using saved.x20
  · simpa only [MainRamCall264.values,show ¬((21 : Reg)=1) by decide,ite_false] using saved.x21
  · simpa only [MainRamCall264.values,show ¬((22 : Reg)=1) by decide,ite_false] using saved.x22
  · simpa only [MainRamCall264.values,show ¬((23 : Reg)=1) by decide,ite_false] using saved.x23
  · simpa only [MainRamCall264.values,show ¬((24 : Reg)=1) by decide,ite_false] using saved.x24
  · simpa only [MainRamCall264.values,show ¬((25 : Reg)=1) by decide,ite_false] using saved.x25
  · simpa only [MainRamCall264.values,show ¬((26 : Reg)=1) by decide,ite_false] using saved.x26
  · simpa only [MainRamCall264.values,show ¬((27 : Reg)=1) by decide,ite_false] using saved.x27

theorem temps2 {c d : Core} (h : ∀ rr : Reg, rr≠10 → rr≠11 → d.get rr=c.get rr) : Frame c d := by
  intro rr safe
  have ne : ∀ rr : Reg, rr∈regs → rr≠10 ∧ rr≠11 := by decide +kernel
  obtain ⟨a0,a1⟩ := ne rr safe
  exact h rr a0 a1

theorem temps4 {c d : Core} (h : ∀ rr : Reg, rr≠10 → rr≠11 → rr≠12 → rr≠13 → d.get rr=c.get rr) : Frame c d := by
  intro rr safe
  have ne : ∀ rr : Reg, rr∈regs → rr≠10 ∧ rr≠11 ∧ rr≠12 ∧ rr≠13 := by decide +kernel
  obtain ⟨a0,a1,a2,a3⟩ := ne rr safe
  exact h rr a0 a1 a2 a3

theorem temps5 {c d : Core} (h : ∀ rr : Reg, rr≠11 → rr≠12 → rr≠13 → rr≠10 → rr≠14 → d.get rr=c.get rr) : Frame c d := by
  intro rr safe
  have ne : ∀ rr : Reg, rr∈regs → rr≠11 ∧ rr≠12 ∧ rr≠13 ∧ rr≠10 ∧ rr≠14 := by decide +kernel
  obtain ⟨a0,a1,a2,a3,a4⟩ := ne rr safe
  exact h rr a0 a1 a2 a3 a4

end E5R.Thermostat.MainSavedGpr
