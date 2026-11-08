import Projects.thermostat.JsonProgram
import Projects.thermostat.FormatValue
namespace E5R.Thermostat.JsonSequence
open E5R E5R.Thermostat

/-- Eight ordered argument pairs followed by the final literal. This is a
    specification of bytes, not a semantic summary of execution. -/
def suffix (values : Fin 8 → FormatValue.Value) : Nat → List (BitVec 8)
  | 0 => JsonProgram.literal 8
  | n+1 => JsonProgram.literal (Fin.ofNat 9 (7-n)) ++ FormatValue.bytes (values (Fin.ofNat 8 (7-n))) ++ suffix values n

theorem snapshot {s : Spec.Snapshot} {values : Fin 8 → FormatValue.Value}
    (hv : ∀ i, FormatValue.bytes (values i) = JsonProgram.argument s i) :
    suffix values 8 = ReplyJson.snapshot s := by
  rw [←JsonProgram.render_snapshot]
  simp only [suffix,hv,JsonProgram.render,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
  rfl
end E5R.Thermostat.JsonSequence
