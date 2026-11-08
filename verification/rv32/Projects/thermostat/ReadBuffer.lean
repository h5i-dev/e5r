import Projects.thermostat.Callee
namespace E5R.Thermostat.ReadBuffer
open E5R E5R.Thermostat

def Live (r : Reg) : Prop := r=20 ∨ r=22 ∨ r=24
instance (r : Reg) : Decidable (Live r) := inferInstanceAs (Decidable (r=20 ∨ r=22 ∨ r=24))
def Frame (c d : Core) : Prop := ∀ r, Live r → d.get r=c.get r

theorem trans {a b c} (h : Frame a b) (k : Frame b c) : Frame a c := fun r hr => (k r hr).trans (h r hr)
theorem saved {r} (h : Live r) : Callee.Saved r := by rcases h with h|h|h <;> subst r <;> decide
end E5R.Thermostat.ReadBuffer
