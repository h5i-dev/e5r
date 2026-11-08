import Theories.Logic
namespace E5R.Thermostat.I16Protected
open E5R

def Protected (r : Reg) : Prop := r = 9 ∨ 18 ≤ r.val
def Frame (c d : Core) : Prop := ∀ r, Protected r → d.get r = c.get r

theorem ne (r q : Reg) (hr : Protected r) (hq : q.val < 18) (h9 : q ≠ 9) : r ≠ q := by
  intro he
  have hv := congrArg Fin.val he
  rcases hr with hr | hr
  · exact h9 (he.symm.trans hr)
  · omega

theorem trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r hr => (k r hr).trans (h r hr)
end E5R.Thermostat.I16Protected
