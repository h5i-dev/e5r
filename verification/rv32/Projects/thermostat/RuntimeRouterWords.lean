import Projects.thermostat.MainRouterFutures
import Projects.thermostat.MainReadReset
namespace E5R.Thermostat.RuntimeRouterWords
open E5R E5R.Thermostat
/-- Reuse the already audited actual setup-store proof. -/
theorem capacity (ram : Word → BitVec 8) : ramRead (MainRouterSetup.memory ram) 0x80fff9fc#32 .w=832#32 :=
  MainReadReset.reply_capacity ram
end E5R.Thermostat.RuntimeRouterWords
