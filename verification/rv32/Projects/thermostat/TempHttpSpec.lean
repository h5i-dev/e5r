import Projects.thermostat.HeaderSpec
import Projects.thermostat.AuthSpec
import Projects.thermostat.ReplyJson
import Projects.thermostat.ResponseHeadSpec
set_option autoImplicit false
namespace E5R.Thermostat.TempHttpSpec
open E5R E5R.Thermostat

/-- Observable bytes/state only: no PCs, registers, pointers or Rust enum tags. -/
structure Reply where
  state : Spec.Snapshot
  status : Nat
  mime : List (BitVec 8)
  payload : List (BitVec 8)

def next (s : Spec.Snapshot) (temperature : BitVec 16) : Spec.Snapshot := Spec.settle {s with temp := temperature}
def run (s : Spec.Snapshot) (raw body : List (BitVec 8)) (entries : List HeaderSpec.Entry) : Reply :=
  if AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") then
    match DecimalSpec.parse (TrimMath.trim body) with
    | none => ⟨s,400,[],[]⟩
    | some temperature => ⟨next s temperature,200,WireSpec.ascii "application/json",ReplyJson.snapshot (next s temperature)⟩
  else ⟨s,401,[],[]⟩

/-- Bridge to the existing independent decoder, with its whole signed-i16
    grammar and exact trim policy. This assumes no machine decode result. -/
theorem decode (body : List (BitVec 8)) : WireSpec.decode (WireSpec.ascii "/temp") body none=
    match DecimalSpec.parse (TrimMath.trim body) with | none => .error 400 | some t => .ok (.reportTemp t) := by
  unfold WireSpec.decode
  rw [ite_eq_right (by decide +kernel),ite_eq_right (by decide +kernel),ite_eq_left rfl]
  unfold WireSpec.number
  cases DecimalSpec.parse (TrimMath.trim body) <;> rfl

theorem transition (s : Spec.Snapshot) (t : BitVec 16) :
    Spec.transition true s (.reportTemp t)=.ok ⟨some (next s t),next s t⟩ := rfl
end E5R.Thermostat.TempHttpSpec
