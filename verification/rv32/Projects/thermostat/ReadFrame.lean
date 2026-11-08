import Projects.thermostat.ReadBytes
import Projects.thermostat.ViewFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReadFrame
open E5R E5R.Thermostat

theorem span {B before after p xs} (h : ReadBytes.Span B img before p xs)
    (hf : ViewFrame.Region before after p xs.length) : ReadBytes.Span B img after p xs :=
  ⟨h.length,h.nowrap,fun i => (h.bytes i).frame (hf i)⟩
end E5R.Thermostat.ReadFrame
