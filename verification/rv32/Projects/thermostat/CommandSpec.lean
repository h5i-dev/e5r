import Projects.thermostat.PathSelect
import Projects.thermostat.ModeSpec
namespace E5R.Thermostat.CommandSpec
open E5R E5R.Thermostat

def value (path body : List (BitVec 8)) (first : Option (List (BitVec 8))) : Except Nat Spec.Command :=
  if path = WireSpec.ascii "/state" then .ok .read
  else if path = WireSpec.ascii "/setpoint" then WireSpec.number Spec.Command.setpoint body
  else if path = WireSpec.ascii "/temp" then WireSpec.number Spec.Command.reportTemp body
  else if path = WireSpec.ascii "/mode" then ModeSpec.value body
  else WireSpec.relay first body

theorem as_decode (path body : List (BitVec 8)) (first : Option (List (BitVec 8))) :
    value path (TrimMath.trim body) first = WireSpec.decode path body first := by rfl

theorem target (path : List (BitVec 8)) : PathSelect.target path =
    (if path = WireSpec.ascii "/state" then 0x80002016#32
    else if path = WireSpec.ascii "/setpoint" then 0x8000208c#32
    else if path = WireSpec.ascii "/temp" then 0x800020f2#32
    else if path = WireSpec.ascii "/mode" then 0x8000215a#32 else 0x80002194#32) := by
  by_cases hs : path = WireSpec.ascii "/state"
  · rw [hs];decide +kernel
  · by_cases hp : path = WireSpec.ascii "/setpoint"
    · rw [hp];decide +kernel
    · by_cases ht : path = WireSpec.ascii "/temp"
      · rw [ht];decide +kernel
      · by_cases hm : path = WireSpec.ascii "/mode"
        · rw [hm];decide +kernel
        · simp only [PathSelect.target,PathFive.destination,ite_eq_right hs,ite_eq_right hp,ite_eq_right ht,ite_eq_right hm,ite_self]
end E5R.Thermostat.CommandSpec
