import Projects.thermostat.MainBootTwo
import Projects.thermostat.MainGprBank
namespace E5R.Thermostat.MainBootConstants
open E5R E5R.Thermostat

theorem routes (c : Core) (ram : Word → BitVec 8) : (InitRoutes.execute c ram).core.get 26=3#32 := by
  simp [InitRoutes.execute,Core.wr_get,Core.wr_get_ne]

theorem second (c : Core) (ram : Word → BitVec 8) : (SecondBuffer.execute c ram).core.get 26=c.get 26 := by
  simp [SecondBuffer.execute,Core.wr_get,Core.wr_get_ne]

theorem loop (c : Core) : (LoopEntry.setup c).get 26=c.get 26 := by
  simp [LoopEntry.setup,Core.wr_get,Core.wr_get_ne]
end E5R.Thermostat.MainBootConstants
