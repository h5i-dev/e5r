-- Compatibility names reuse existing independently audited fetch facts.
import Projects.thermostat.StateHeadCode
import Projects.thermostat.MainTempRouterCode
namespace E5R.Thermostat
open E5R
theorem sr2147488760 : fetchDecode img 2147488760#32=some ((.opimm .add 9 0 2#32),2#32) := tc2147488760
theorem sr2147488762 : fetchDecode img 2147488762#32=some ((.jal 0 4#32),2#32) := tc2147488762
end E5R.Thermostat
