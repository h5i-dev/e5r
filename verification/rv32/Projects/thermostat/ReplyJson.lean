import Projects.thermostat.Spec
import Projects.thermostat.WireSpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReplyJson
open E5R E5R.Thermostat

/-- Independent ordinary base-ten digits, most significant first. -/
def decimal (n : Nat) : List (BitVec 8) :=
  if n < 10 then [BitVec.ofNat 8 (48+n)]
  else decimal (n/10) ++ [BitVec.ofNat 8 (48+n%10)]
termination_by n

def signed (v : BitVec 16) : List (BitVec 8) :=
  (if v.toInt < 0 then [45#8] else []) ++ decimal v.toInt.natAbs

def boolean (b : Bool) : List (BitVec 8) := WireSpec.ascii (if b then "true" else "false")
def mode : Spec.Mode → List (BitVec 8)
  | .off => WireSpec.ascii "off" | .heat => WireSpec.ascii "heat" | .auto => WireSpec.ascii "auto"

/-- Exact field order, punctuation and decimal/boolean encoding of the API. -/
def snapshot (s : Spec.Snapshot) : List (BitVec 8) :=
  WireSpec.ascii "{\"setpoint_dc\":" ++ signed s.setpoint ++
  WireSpec.ascii ",\"temp_dc\":" ++ signed s.temp ++
  WireSpec.ascii ",\"heater\":" ++ boolean s.heater ++
  WireSpec.ascii ",\"relays\":[" ++ boolean (s.relays 0) ++ WireSpec.ascii "," ++
  boolean (s.relays 1) ++ WireSpec.ascii "," ++ boolean (s.relays 2) ++ WireSpec.ascii "," ++ boolean (s.relays 3) ++
  WireSpec.ascii "],\"mode\":\"" ++ mode s.mode ++ WireSpec.ascii "\"}"

def errorStatus : Spec.Error → Nat
  | .setpointOutOfRange => 422 | .noSuchRelay => 404 | .forbidden => 403

def errorBody : Spec.Error → List (BitVec 8)
  | .setpointOutOfRange => WireSpec.ascii "{\"error\":\"setpoint_out_of_range\"}"
  | .noSuchRelay => WireSpec.ascii "{\"error\":\"no_such_relay\"}"
  | .forbidden => WireSpec.ascii "{\"error\":\"forbidden\"}"

/-- The real API truncates only its error-body copy to available output space. -/
def errorPrefix (e : Spec.Error) (capacity : Nat) := (errorBody e).take capacity

theorem minimum_signed : signed 0x8000#16 = WireSpec.ascii "-32768" := by decide +kernel
theorem maximum_signed : signed 0x7fff#16 = WireSpec.ascii "32767" := by decide +kernel
theorem zero_signed : signed 0#16 = WireSpec.ascii "0" := by decide +kernel
theorem initial : snapshot Spec.initial = WireSpec.ascii
    "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"off\"}" := by decide +kernel

theorem error_lengths (e : Spec.Error) : (errorBody e).length =
    match e with | .setpointOutOfRange => 33 | .noSuchRelay => 25 | .forbidden => 21 := by cases e <;> decide +kernel

theorem error_prefix_length (e : Spec.Error) (cap : Nat) : (errorPrefix e cap).length = min cap (errorBody e).length := by
  simp [errorPrefix]
end E5R.Thermostat.ReplyJson
