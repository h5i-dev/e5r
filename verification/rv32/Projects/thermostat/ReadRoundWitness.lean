import Projects.thermostat.ReadRound
import Projects.thermostat.ReadSendWitness
namespace E5R.Thermostat.ReadRoundWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
open ReadSendWitness

/-- The same real main-buffer witness reaches the selected loop boundary,
    with the committed App and free borrow, after sending the exact reply. -/
theorem execution (close head : Bool) : ∃ d n after reads events,
    Observed.Steps B img n ⟨ReadSendWitness.core,ReadSendWitness.ram close head⟩ ⟨d,after⟩ reads events ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 21=0xffffffff#32 ∧
      AppState.At after Spec.initial ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close++
        ResponseHeadSpec.body 200 head (ReplyJson.snapshot Spec.initial) := by
  obtain ⟨d,n,after,prefixReads,_,td,pd,_,_,_,ha,hi,_,_,_,d21⟩ := ReadRound.contract ReadSendWitness.core (ReadSendWitness.ram close head) Spec.initial close
    (pre close head) Spec.initial_inv (app close head)
    (by change Memory.Block B 0x80ff0000#32 65536;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    rfl rfl rfl (capacity close head) (tx_pointer close head) (tx_capacity close head) (close_byte close head)
    (headerSlots close) (bodySlots head) (by exact List.length_replicate) (by rw [head_byte];exact List.length_replicate)
  rw [head_byte] at td
  have projection := Send.projection 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial) close head (headerSlots close) (bodySlots head)
  exact ⟨d,n,after,_,_,td,pd,d21,ha,hi,ha.available,projection.2⟩

theorem closed_read : ∃ d n after reads events,
    Observed.Steps B img n ⟨ReadSendWitness.core,ReadSendWitness.ram true false⟩ ⟨d,after⟩ reads events ∧
      d.pc=0x80000978#32 ∧ d.get 21=0xffffffff#32 ∧ AppState.At after Spec.initial ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 96\r\nConnection: close\r\n\r\n"++
        WireSpec.ascii "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"off\"}" := by
  obtain ⟨d,n,after,reads,events,td,pd,d21,ha,hi,hb,ho⟩ := execution true false
  refine ⟨d,n,after,reads,events,td,pd,d21,ha,hi,hb,?_⟩
  rw [show ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length true=
    WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 96\r\nConnection: close\r\n\r\n" by decide +kernel] at ho
  rw [show ResponseHeadSpec.body 200 false (ReplyJson.snapshot Spec.initial)=ReplyJson.snapshot Spec.initial by rfl,ReplyJson.initial] at ho
  exact ho

theorem persistent_read : ∃ d n after reads events,
    Observed.Steps B img n ⟨ReadSendWitness.core,ReadSendWitness.ram false false⟩ ⟨d,after⟩ reads events ∧
      d.pc=0x800017be#32 ∧ d.get 21=0xffffffff#32 ∧ AppState.At after Spec.initial ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 := by
  obtain ⟨d,n,after,reads,events,td,pd,d21,ha,hi,hb,_⟩ := execution false false
  exact ⟨d,n,after,reads,events,td,pd,d21,ha,hi,hb⟩
end E5R.Thermostat.ReadRoundWitness
