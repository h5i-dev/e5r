import Projects.thermostat.CopyRegs
namespace E5R.Thermostat.CopyRegs
open E5R

theorem ne_not (r q : Reg) (hr : Preserved r) (hq : ¬Preserved q) : r≠q := by
  intro h;exact hq (h ▸ hr)
end E5R.Thermostat.CopyRegs
