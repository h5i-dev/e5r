import Projects.thermostat.MainInit
namespace E5R.Thermostat.MainBootTwo
open E5R E5R.Thermostat

theorem routes (c : Core) (ram : Word → BitVec 8) : (InitRoutes.execute c ram).core.get 18=2#32 := by
  simp [InitRoutes.execute,Core.wr_get,Core.wr_get_ne]

theorem second (c : Core) (ram : Word → BitVec 8) : (SecondBuffer.execute c ram).core.get 18=c.get 18 := by
  simp [SecondBuffer.execute,Core.wr_get,Core.wr_get_ne]

theorem loop (c : Core) : (LoopEntry.setup c).get 18=c.get 18 := by
  simp [LoopEntry.setup,Core.wr_get,Core.wr_get_ne]
end E5R.Thermostat.MainBootTwo
