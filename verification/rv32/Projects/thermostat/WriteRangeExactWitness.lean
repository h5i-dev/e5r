import Projects.thermostat.MainWriteRangeTransactionsWitness
import Projects.thermostat.MainWriteTransactionsExact
namespace E5R.Thermostat.MainWriteRangeTransactionsWitness
open E5R E5R.Thermostat
theorem execution_exact (close : Bool) : ∃ d n after reads events,
    Observed.Steps B img n ⟨appCore,appRam close⟩ ⟨d,after⟩ reads events ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧
      AppState.At after (Spec.commit Spec.initial (.error .setpointOutOfRange)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=ResponseHeadSpec.bytes 422 (WireSpec.ascii "application/json") payload.length close++payload ∧
      ViewFrame.Region (appRam close) after 0x80ffec14#32 2048 ∧ Observed.input reads=[] := by
  obtain ⟨d,n,after,bn,tn,pd,_,_,_,app,inv,_,_,rx⟩ := MainWriteTransactions.error_exact appCore (appRam close)
    0x80fff880#32 0x80ffec14#32 0x80ffec19#32 0x80ffec6a#32
    MainWriteRangeWitness.raw MainWriteRangeWitness.path MainWriteRangeWitness.body MainWriteRangeWitness.entries none Spec.initial (.setpoint 301#16) .setpointOutOfRange
    rfl rfl rfl rfl rfl rfl MainWriteRangeWitness.stack (MainWriteRangeWitness.app close) Spec.initial_inv (MainWriteRangeWitness.ready close)
    (by decide +kernel) (by decide +kernel) rfl close (capacity close) (tx_pointer close) (tx_capacity close) (close_byte close)
    (headerSlots close) bodySlots (by simp [headerSlots,ErrorLiterals.status])
    (by rw [post_method];simp [bodySlots,ResponseHeadSpec.body,ResponseHeadSpec.hasBody,ErrorLiterals.status])
  refine ⟨d,n,after,_,_,tn,pd,app,inv,app.available,?_,rx,?_⟩
  · rw [Observed.output_append,UartTxLoop.output,UartTxLoop.output,post_method]
    rfl
  · rw [Observed.input_append,UartTxLoop.no_input,UartTxLoop.no_input];rfl

end E5R.Thermostat.MainWriteRangeTransactionsWitness
