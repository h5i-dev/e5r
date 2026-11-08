import Projects.thermostat.MainWriteRangeWitness
import Projects.thermostat.MainWriteTransactions
namespace E5R.Thermostat.MainWriteRangeTransactionsWitness
open E5R E5R.Thermostat
abbrev appCore := E5R.Thermostat.MainWriteRangeWitness.core
abbrev appRam := E5R.Thermostat.MainWriteRangeWitness.ram
abbrev B := UartPlatform.board
abbrev payload := ReplyJson.errorBody Spec.Error.setpointOutOfRange

theorem capacity (close : Bool) : ramRead (appRam close) 0x80fff9fc#32 .w=832#32 := by cases close <;> decide +kernel
theorem tx_pointer (close : Bool) : ramRead (appRam close) (0x80fff814#32+64#32) .w=0x80fff414#32 := by cases close <;> decide +kernel
theorem tx_capacity (close : Bool) : ramRead (appRam close) (0x80fff814#32+68#32) .w=1024#32 := by cases close <;> decide +kernel
theorem close_byte (close : Bool) : appRam close 0x80fff878#32=(if close then 1#8 else 0#8) := by cases close <;> decide +kernel
theorem post_method (close : Bool) : MainMethod.head (appRam close 0x80fff9f4#32)=false := by cases close <;> decide +kernel

def headerSlots (close : Bool) := List.replicate
  (ResponseHeadSpec.bytes 422 (WireSpec.ascii "application/json") payload.length close).length UartWriteWitness.slot1
def bodySlots := List.replicate payload.length UartWriteWitness.slot1

/-- Concrete original POST /setpoint range-refusal HTTP bytes, actual RX/TX/main object addresses,
    one not-ready poll per transmitted byte, exact 422 JSON and actual loop dispatch.
    The parsed Request metadata is explicit and satisfiable; reset-to-parser
    correspondence remains a separate obligation. -/
theorem execution (close : Bool) : ∃ d n after reads events,
    Observed.Steps B img n ⟨appCore,appRam close⟩ ⟨d,after⟩ reads events ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧
      AppState.At after (Spec.commit Spec.initial (.error .setpointOutOfRange)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=ResponseHeadSpec.bytes 422 (WireSpec.ascii "application/json") payload.length close++payload ∧
      ViewFrame.Region (appRam close) after 0x80ffec14#32 2048 := by
  obtain ⟨d,n,after,reads,bn,tn,pd,_,_,_,app,inv,_,_,rx⟩ := MainWriteTransactions.error appCore (appRam close)
    0x80fff880#32 0x80ffec14#32 0x80ffec19#32 0x80ffec6a#32
    MainWriteRangeWitness.raw MainWriteRangeWitness.path MainWriteRangeWitness.body MainWriteRangeWitness.entries none Spec.initial (.setpoint 301#16) .setpointOutOfRange
    rfl rfl rfl rfl rfl rfl MainWriteRangeWitness.stack (MainWriteRangeWitness.app close) Spec.initial_inv (MainWriteRangeWitness.ready close)
    (by decide +kernel) (by decide +kernel) rfl close (capacity close) (tx_pointer close) (tx_capacity close) (close_byte close)
    (headerSlots close) bodySlots (by simp [headerSlots,ErrorLiterals.status])
    (by rw [post_method];simp [bodySlots,ResponseHeadSpec.body,ResponseHeadSpec.hasBody,ErrorLiterals.status])
  refine ⟨d,n,after,_,_,tn,pd,app,inv,app.available,?_,rx⟩
  rw [Observed.output_append,UartTxLoop.output,UartTxLoop.output,post_method]
  rfl

end E5R.Thermostat.MainWriteRangeTransactionsWitness
