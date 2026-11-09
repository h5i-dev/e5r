-- Compatibility names reuse existing independently audited fetch facts.
import Projects.thermostat.MainStateRouteCode
namespace E5R.Thermostat
open E5R
theorem sh2147488746 : fetchDecode img 2147488746#32=some ((.opimm .xor 12 12 1#32),4#32) := rt2147488746
theorem sh2147488750 : fetchDecode img 2147488750#32=some ((.op .or 12 12 13),2#32) := rt2147488750
theorem sh2147488752 : fetchDecode img 2147488752#32=some ((.opimm .sltu 12 12 1#32),4#32) := rt2147488752
theorem sh2147488756 : fetchDecode img 2147488756#32=some ((.branch .ne 12 0 1224#32),4#32) := rt2147488756
end E5R.Thermostat
