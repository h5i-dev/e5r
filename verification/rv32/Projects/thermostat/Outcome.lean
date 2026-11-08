import Projects.thermostat.Errors

namespace E5R.Thermostat.Outcome
open E5R E5R.Thermostat

/-- This ELF's Result<(Option<Snapshot>, Reply), Error> representation.
    Error and None payload bytes not written by Rust are deliberately unconstrained. -/
def At (ram : Word → BitVec 8) (out : Word) : Except Spec.Error Spec.Success → Prop
  | .error err => ram (out+10#32) = 2#8 ∧ ram out = Errors.code err
  | .ok res => Encoding.OptionAt ram out res.write ∧ Encoding.SnapshotAt ram (out+10#32) res.reply

theorem error (ram : Word → BitVec 8) (out : Word) (err : Spec.Error) :
    At (Errors.result ram out err) out (.error err) := by
  exact ⟨(Errors.result_tag ram out err).2,(Errors.result_tag ram out err).1⟩

end E5R.Thermostat.Outcome
