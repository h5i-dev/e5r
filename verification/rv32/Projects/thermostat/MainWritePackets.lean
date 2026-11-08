import Projects.thermostat.MainWriteTransactionsWitness
import Projects.thermostat.MainWriteRangeTransactionsWitness
namespace E5R.Thermostat.MainWritePackets
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem auto_header : ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json")
    (ReplyJson.snapshot WriteSuccessWitness.snapshot).length false=
    WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 97\r\n\r\n" := by decide +kernel

theorem auto_json : ReplyJson.snapshot WriteSuccessWitness.snapshot=WireSpec.ascii
    "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"auto\"}" := WriteSuccessWitness.json

theorem range_header : ResponseHeadSpec.bytes 422 (WireSpec.ascii "application/json")
    (ReplyJson.errorBody .setpointOutOfRange).length true=
    WireSpec.ascii "HTTP/1.1 422 Unprocessable Content\r\nContent-Type: application/json\r\nContent-Length: 33\r\nConnection: close\r\n\r\n" := by decide +kernel

theorem range_json : ReplyJson.errorBody .setpointOutOfRange=WireSpec.ascii "{\"error\":\"setpoint_out_of_range\"}" := by decide +kernel

theorem auto_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨MainWriteWitness.core,MainWriteWitness.ram false⟩ ⟨d,after⟩ reads events ∧
      d.pc=0x800017be#32 ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      after 0x80ffebc9#32=2#8 ∧
      Observed.output events=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 97\r\n\r\n"++
        WireSpec.ascii "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"auto\"}" := by
  obtain ⟨d,n,after,reads,events,td,pd,app,inv,hb,ho,_⟩ := MainWriteTransactionsWitness.execution false
  have hmode := app.state ⟨9,by decide⟩
  change after 0x80ffebc9#32=2#8 at hmode
  refine ⟨d,n,after,reads,events,td,pd,inv,hb,hmode,?_⟩
  rw [auto_header,auto_json] at ho
  exact ho

theorem range_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨MainWriteRangeWitness.core,MainWriteRangeWitness.ram true⟩ ⟨d,after⟩ reads events ∧
      d.pc=0x80000978#32 ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Encoding.SnapshotAt after 0x80ffebc0#32 Spec.initial ∧
      Observed.output events=WireSpec.ascii "HTTP/1.1 422 Unprocessable Content\r\nContent-Type: application/json\r\nContent-Length: 33\r\nConnection: close\r\n\r\n"++
        WireSpec.ascii "{\"error\":\"setpoint_out_of_range\"}" := by
  obtain ⟨d,n,after,reads,events,td,pd,app,inv,hb,ho,_⟩ := MainWriteRangeTransactionsWitness.execution true
  refine ⟨d,n,after,reads,events,td,pd,inv,hb,app.state,?_⟩
  dsimp only [MainWriteRangeTransactionsWitness.payload] at ho
  rw [range_header,range_json] at ho
  exact ho
end E5R.Thermostat.MainWritePackets
