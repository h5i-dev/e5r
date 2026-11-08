import Theories.Logic
namespace E5R.Thermostat.Upper
open E5R
/-- Kernel preservation of x22..x31, including s6..s11 used by the caller. -/
def Frame (c d : Core) : Prop := ∀ r : Reg, 22 ≤ r.val → d.get r = c.get r

theorem refl (c : Core) : Frame c c := fun _ _ => rfl

theorem trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r hr => (k r hr).trans (h r hr)

theorem ne_low (r : Reg) (hr : 22 ≤ r.val) (rd : Reg) (hd : rd.val < 22) : r ≠ rd := by
  intro he
  have hn := congrArg Fin.val he
  omega

theorem wr (c : Core) (rd : Reg) (v pc : Word) (hd : rd.val < 22) : Frame c (c.wr rd v pc) := by
  intro r hr
  exact Core.wr_get_ne c rd r v pc (ne_low r hr rd hd)

theorem goto (c : Core) (pc : Word) : Frame c (c.goto pc) := fun _ _ => rfl
end E5R.Thermostat.Upper
