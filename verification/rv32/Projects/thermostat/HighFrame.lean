import Theories.Logic
namespace E5R.Thermostat.HighFrame
open E5R

def Frame (c d : Core) : Prop := ∀ r : Reg, 20 ≤ r.val → d.get r = c.get r

theorem ne (r k : Reg) (hr : 20 ≤ r.val) (hk : k.val < 20) : r ≠ k := by
  intro he;have hh := congrArg Fin.val he;omega

theorem trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c := fun r hr => (k r hr).trans (h r hr)
end E5R.Thermostat.HighFrame
