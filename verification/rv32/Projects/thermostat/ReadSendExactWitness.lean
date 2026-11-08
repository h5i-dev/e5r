import Projects.thermostat.ReadSendWitness
import Projects.thermostat.ReadSendExact
namespace E5R.Thermostat.ReadSendWitness
open E5R E5R.Thermostat
theorem execution_exact (close head : Bool) : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram close head⟩ ⟨d,after⟩ reads events ∧ d.pc=0x80001784#32 ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ AppState.At after Spec.initial ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close++
        ResponseHeadSpec.body 200 head (ReplyJson.snapshot Spec.initial) ∧
      ramRead after 0x80fffd3c#32 .w=ResponseHeadBodyMath.boolWord close ∧ Observed.input reads=[] := by
  obtain ⟨d,n,after,_,td,pd,sp,fp,_,ha,hi,_,hc,_⟩ := ReadSend.contract_exact core (ram close head) Spec.initial close
    (pre close head) Spec.initial_inv (app close head)
    (by change Memory.Block B 0x80ff0000#32 65536;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    rfl rfl rfl (capacity close head) (tx_pointer close head) (tx_capacity close head) (close_byte close head)
    (headerSlots close) (bodySlots head) (by exact List.length_replicate) (by rw [head_byte];exact List.length_replicate)
  rw [head_byte] at td
  have projection := Send.projection 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial) close head (headerSlots close) (bodySlots head)
  exact ⟨d,n,after,_,_,td,pd,sp,fp,ha,hi,ha.available,projection.2,hc,projection.1⟩

end E5R.Thermostat.ReadSendWitness
