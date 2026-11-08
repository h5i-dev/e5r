import Projects.thermostat.FormatCursor
namespace E5R.Thermostat.ResponseHeadCallee
open E5R E5R.Thermostat

def Registers (r : Reg) : Prop := r=2 ∨ r=8 ∨ r=9 ∨ r=18 ∨ r=19 ∨ r=20 ∨ r=21 ∨ r=22 ∨ r=23 ∨ r=24 ∨ r=25 ∨ r=26 ∨ r=27
instance (r : Reg) : Decidable (Registers r) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))
def Keep (c d : Core) (changed : List Reg) : Prop := ∀ r, Registers r → r∉changed → d.get r=c.get r

theorem returned {c d : Core} (h : FormatCursor.Returned c d) (r : Reg) (hr : Registers r) : d.get r=c.get r := by
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.sp
  · exact h.x8
  · exact h.x9
  · exact h.x18
  · exact h.x19
  · exact h.x20
  · exact h.x21
  · exact h.x22
  · exact h.x23
  · exact h.x24
  · exact h.x25
  · exact h.x26
  · exact h.x27
end E5R.Thermostat.ResponseHeadCallee
