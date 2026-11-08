-- Observed candidates; both completeness and classification are kernel checked.
import Projects.thermostat.Proof
import Projects.thermostat.ControlBytes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E5R.Thermostat.Control
open E5R

def expectedSites : List Nat := [2147483648, 2147483652, 2147490458, 2147490528, 2147493648, 2147493652, 2147493676, 2147495066, 2147495346, 2147495354, 2147495566, 2147503270, 2147504968, 2147504972]

theorem sites_checked : systemSites img = expectedSites := by decide +kernel

end E5R.Thermostat.Control
