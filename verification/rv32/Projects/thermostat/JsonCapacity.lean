import Projects.thermostat.ReplyJsonBounds
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.JsonCapacity
open E5R E5R.Thermostat

theorem boolean_length (b : Bool) : (ReplyJson.boolean b).length ≤ 5 := by cases b <;> decide

theorem mode_length (m : Spec.Mode) : (ReplyJson.mode m).length ≤ 4 := by cases m <;> decide

theorem snapshot_length (s : Spec.Snapshot) : (ReplyJson.snapshot s).length ≤ 103 := by
  have hsp := ReplyJsonBounds.signed_length s.setpoint
  have ht := ReplyJsonBounds.signed_length s.temp
  have hh := boolean_length s.heater
  have h0 := boolean_length (s.relays 0)
  have h1 := boolean_length (s.relays 1)
  have h2 := boolean_length (s.relays 2)
  have h3 := boolean_length (s.relays 3)
  have hm := mode_length s.mode
  simp only [ReplyJson.snapshot,List.length_append]
  change 15+(ReplyJson.signed s.setpoint).length+11+(ReplyJson.signed s.temp).length+10+
    (ReplyJson.boolean s.heater).length+11+(ReplyJson.boolean (s.relays 0)).length+1+
    (ReplyJson.boolean (s.relays 1)).length+1+(ReplyJson.boolean (s.relays 2)).length+1+
    (ReplyJson.boolean (s.relays 3)).length+10+(ReplyJson.mode s.mode).length+2 ≤ 103
  omega
end E5R.Thermostat.JsonCapacity
