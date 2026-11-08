import Projects.thermostat.ReadBytes
namespace E5R.Thermostat.ReadBytes
open E5R

theorem Byte.readonly {B img before after a v} (h : Byte B img before a v) (ho : B.inRam a 1 = false) :
    Byte B img after a v := by
  cases h with
  | ram hi _ => rw [ho] at hi;contradiction
  | rom hi hv => exact .rom hi hv
end E5R.Thermostat.ReadBytes
