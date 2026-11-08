import Projects.thermostat.MainSavedGpr
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestSaved
open E5R E5R.Thermostat

def regs : List Reg := [2,8,18,19,20,21,22,23,24,25,26,27]
def Frame (c d : Core) : Prop := ∀ r∈regs, d.get r=c.get r

theorem trans {a b c : Core} (ab : Frame a b) (bc : Frame b c) : Frame a c :=
  fun r safe => (bc r safe).trans (ab r safe)

theorem fromSaved {c d : Core} (h : MainSavedGpr.Frame c d) : Frame c d := by
  intro r safe
  have subset : ∀ r : Reg, r∈regs → r∈MainSavedGpr.regs := by decide +kernel
  exact h r (subset r safe)

theorem temps7 {c d : Core} (h : ∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → d.get r=c.get r) : Frame c d := by
  intro r safe
  have neq : ∀ r : Reg, r∈regs → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠13 ∧ r≠14 ∧ r≠15 ∧ r≠16 := by decide +kernel
  obtain ⟨a,b,e,f,g,i,j⟩ := neq r safe
  exact h r a b e f g i j

theorem temp17 {c d : Core} (h : ∀ r : Reg, r≠17 → d.get r=c.get r) : Frame c d := by
  intro r safe
  have neq : ∀ r : Reg, r∈regs → r≠17 := by decide +kernel
  exact h r (neq r safe)

theorem minor {c d : Core} (h : ∀ r : Reg, r≠9 → d.get r=c.get r) : Frame c d := by
  intro r safe
  have neq : ∀ r : Reg, r∈regs → r≠9 := by decide +kernel
  exact h r (neq r safe)

theorem zero {c d : Core} (h : ∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → d.get r=c.get r) : Frame c d := by
  intro r safe
  have neq : ∀ r : Reg, r∈regs → r≠1 ∧ r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠13 ∧ r≠14 ∧ r≠15 ∧ r≠16 := by decide +kernel
  obtain ⟨a,b,e,f,g,i,j,k⟩ := neq r safe
  exact h r a b e f g i j k
end E5R.Thermostat.MainRequestSaved
