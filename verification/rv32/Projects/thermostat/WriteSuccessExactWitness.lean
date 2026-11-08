import Projects.thermostat.MainWriteTransactionsWitness
import Projects.thermostat.MainWriteTransactionsExact
namespace E5R.Thermostat.MainWriteTransactionsWitness
open E5R E5R.Thermostat
theorem execution_exact (close : Bool) : ∃ d n after reads events,
    Observed.Steps B img n ⟨appCore,appRam close⟩ ⟨d,after⟩ reads events ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧
      AppState.At after (Spec.commit Spec.initial (.ok result)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot snapshot).length close++ReplyJson.snapshot snapshot ∧
      ViewFrame.Region (appRam close) after 0x80ffec14#32 2048 ∧ Observed.input reads=[] := by
  obtain ⟨d,n,after,bn,tn,pd,_,_,_,app,inv,_,_,rx⟩ := MainWriteTransactions.success_exact appCore (appRam close)
    0x80fff880#32 0x80ffec14#32 0x80ffec19#32 0x80ffec66#32
    MainWriteWitness.raw MainWriteWitness.path MainWriteWitness.body MainWriteWitness.entries none Spec.initial (.mode .auto) result
    rfl rfl rfl rfl rfl rfl MainWriteWitness.stack (MainWriteWitness.app close) Spec.initial_inv (MainWriteWitness.ready close)
    (by decide +kernel) (by decide +kernel) rfl close (capacity close) (tx_pointer close) (tx_capacity close) (close_byte close)
    (headerSlots close) bodySlots (by simp [headerSlots,snapshot,result,WriteSuccessWitness.result])
    (by rw [post_method];simp [bodySlots,ResponseHeadSpec.body,ResponseHeadSpec.hasBody,snapshot,result,WriteSuccessWitness.result])
  refine ⟨d,n,after,_,_,tn,pd,app,inv,app.available,?_,rx,?_⟩
  · rw [Observed.output_append,UartTxLoop.output,UartTxLoop.output,post_method]
    rfl
  · rw [Observed.input_append,UartTxLoop.no_input,UartTxLoop.no_input];rfl

end E5R.Thermostat.MainWriteTransactionsWitness
