import Projects.thermostat.FirmwareOneRequest
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.UartWriteWitness
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FirmwareOneRequestWitness
open E5R E5R.Thermostat ApiRequestSpec

local instance (r : Route) : Decidable r.Valid := by
  cases r <;> unfold Route.Valid <;> infer_instance
local instance (h : Header) : Decidable h.Valid := by
  unfold Header.Valid; infer_instance
local instance (h : Header) (amount : Nat) : Decidable (h.LengthValue amount) := by
  unfold Header.LengthValue; infer_instance

inductive Case where
  | state | setpoint | temp | mode | relay3 | relay5 | relayz | unauth
  deriving DecidableEq

def route : Case → Route
  | .state => .state
  | .setpoint => .setpoint
  | .temp => .temp
  | .mode | .unauth => .mode
  | .relay3 => .relay [51#8]
  | .relay5 => .relay [53#8]
  | .relayz => .relay [122#8]

def body : Case → ApiRequestSpec.Bytes
  | .setpoint => WireSpec.ascii "22"
  | .temp => WireSpec.ascii "-1"
  | .relay3 | .relay5 | .relayz => WireSpec.ascii "on"
  | _ => WireSpec.ascii "xx"

def headers (which : Case) (close : Bool) : List Header := [
  ⟨WireSpec.ascii "hOsT",[9#8],[],[]⟩,
  ⟨WireSpec.ascii "Content-Length",[9#8,32#8],WireSpec.ascii "002",[]⟩,
  ⟨WireSpec.ascii "Authorization",[32#8],WireSpec.ascii (if which=.unauth then "Bearer bad-key" else "Bearer dev-key"),[]⟩,
  ⟨WireSpec.ascii "authorization",[],WireSpec.ascii "Bearer dev-key",[]⟩,
  ⟨WireSpec.ascii "Connection",[32#8],WireSpec.ascii (if close then "keep-alive, ClOsE" else "disclose"),[9#8]⟩,
  ⟨WireSpec.ascii "X-Audit",[],WireSpec.ascii "a b",[32#8]⟩]

/-- Domain inhabitants exercise noncanonical header case/OWS/order, an empty
    Host, leading CL zeroes, duplicate Authorization, query '?' and both closes. -/
def request (which : Case) (close : Bool) : Fixed11 where
  route := route which
  query := some (WireSpec.ascii "audit?x")
  headers := headers which close
  body := body which
  routeValid := by cases which <;> decide +kernel
  queryValid := by
    intro q eq
    cases Option.some.inj eq
    decide +kernel
  headersValid := by cases which <;> cases close <;> decide +kernel
  headerCount := by cases which <;> cases close <;> decide +kernel
  hostCount := by cases which <;> cases close <;> decide +kernel
  lengthCount := by cases which <;> cases close <;> decide +kernel
  noTransfer := by cases which <;> cases close <;> decide +kernel
  lengthValue := by cases which <;> cases close <;> decide +kernel
  headBound := by cases which <;> cases close <;> decide +kernel
  bodyBound := by cases which <;> decide +kernel

def status : Case → Nat
  | .setpoint => 422
  | .mode => 400
  | .relay5 | .relayz => 404
  | .unauth => 401
  | _ => 200

theorem statuses (which : Case) (close : Bool) : ((request which close).reply Spec.initial).status=status which := by
  cases which <;> cases close <;> decide +kernel

theorem closes (which : Case) (close : Bool) : ApiReplySpec.close (request which close)=close := by
  cases which <;> cases close <;> decide +kernel

def wire (r : Fixed11) (k : Nat) : BitVec 8 := r.bytes[k]?.getD 0#8
def plan (r : Fixed11) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire r k).toNat⟩

theorem valid (r : Fixed11) (first count : Nat) : ChunkReceivePlan.Valid (plan r) (wire r) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32; decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire r k)⟩
  intro status mem
  cases mem

def headerSlots (r : Fixed11) (close : Bool) := List.replicate
  (ResponseHeadSpec.bytes (r.reply Spec.initial).status (r.reply Spec.initial).mime (r.reply Spec.initial).payload.length close).length
  UartWriteWitness.slot1
def bodySlots (r : Fixed11) := List.replicate (r.reply Spec.initial).payload.length UartWriteWitness.slot1

/-- All eight domain inhabitants actually execute from reset via the unified
    theorem. Prefix parsing is derived generically, not recomputed per byte. -/
theorem execution (which : Case) (close : Bool) :
    let r := request which close
    ∃ n d after,
      Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
        (Firmware.reads r (plan r) (plan r) (headerSlots r) (bodySlots r) close)
        (UartTxLoop.events (ResponseHeadSpec.bytes (status which) (r.reply Spec.initial).mime
          (r.reply Spec.initial).payload.length close)++UartTxLoop.events (r.reply Spec.initial).payload) ∧
      Observed.input (Firmware.reads r (plan r) (plan r) (headerSlots r) (bodySlots r) close)=r.bytes ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.mie_=false ∧
      AppState.At after (r.reply Spec.initial).state ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Spec.Inv (r.reply Spec.initial).state ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  dsimp only
  have delivers (k : Nat) (hk : k<(request which close).bytes.length) :
      wire (request which close) k=(request which close).bytes[k]'hk := by
    simp only [wire,List.getElem?_eq_getElem hk,Option.getD_some]
  have run := Firmware.one_request (request which close) MainInitWitness.core MainInitWitness.ram
    (wire (request which close)) (plan (request which close)) (plan (request which close))
    rfl (Or.inr rfl) rfl Blocking.stack_available delivers (valid _ _ _) (valid _ _ _)
    (headerSlots (request which close)) (bodySlots (request which close))
    (fun _ => List.length_replicate) List.length_replicate
  simpa only [closes,statuses] using run

end E5R.Thermostat.FirmwareOneRequestWitness
