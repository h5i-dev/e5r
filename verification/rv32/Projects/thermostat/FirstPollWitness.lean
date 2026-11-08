import Projects.thermostat.Blocking
import Projects.thermostat.MainInitWitness
namespace E5R.Thermostat.FirstPollWitness
open E5R E5R.Thermostat

theorem reset_to_receive :
    ∃ d r, Trace.Closed UartPlatform.board img 2550 ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,r⟩ ∧
      FirstPoll.Ready UartPlatform.board d r ∧ Engine.InvariantAt r 0x80ffebbc#32 :=
  FirstPoll.reset_closed UartPlatform.board MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) rfl Blocking.stack_available

theorem concrete_no_response :
    ∃ g : Nat → Machine, g 0 = ⟨MainInitWitness.core,MainInitWitness.ram⟩ ∧
      Infinite.NoWrites UartPlatform.board img g :=
  Blocking.no_response_from_reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl)
end E5R.Thermostat.FirstPollWitness
