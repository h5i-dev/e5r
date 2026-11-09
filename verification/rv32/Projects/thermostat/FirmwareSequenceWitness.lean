import Projects.thermostat.FirmwareRequestSequence
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.UartWriteWitness
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.FirmwareSequenceWitness
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

theorem initial_closes (which : Case) (close : Bool) : ApiReplySpec.close (request which close)=close := by
  cases which <;> cases close <;> decide +kernel

def wire (r : Fixed11) (k : Nat) : BitVec 8 := r.bytes[k]?.getD 0#8
def plan (r : Fixed11) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire r k).toNat⟩

theorem valid (r : Fixed11) (first count : Nat) : ChunkReceivePlan.Valid (plan r) (wire r) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32; decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire r k)⟩
  intro status mem;cases mem

def one (r : Fixed11) (s : Spec.Snapshot) : RequestSchedules.One r s where
  wire := wire r
  headerPlan := plan r
  bodyPlan := plan r
  delivers := by
    intro k hk
    simp only [wire,List.getElem?_eq_getElem hk,Option.getD_some]
  headerValid := valid r _ _
  bodyValid := valid r _ _
  hs := fun close => List.replicate
    (ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length close).length UartWriteWitness.slot1
  bs := List.replicate (r.reply s).payload.length UartWriteWitness.slot1
  headerLengths := by intro close;rw [List.length_replicate]
  bodyLength := List.length_replicate

def many : (requests : List Fixed11) → (s : Spec.Snapshot) → (served : Nat) → RequestSchedules.Many requests s served
  | [],s,served => .nil s served
  | r::rs,s,served => .cons (one r s) (many rs (r.reply s).state (LoopSpec.nextCount r served))

/-- Satisfiable finite environment for every finite domain sequence. -/
theorem execution (requests : List Fixed11) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
      (RequestSchedules.reads (many requests Spec.initial 0)) (UartTxLoop.events (LoopSpec.output requests Spec.initial 0)) ∧
      Observed.input (RequestSchedules.reads (many requests Spec.initial 0))=LoopSpec.input requests ∧
      LoopReady.At d after (LoopSpec.final requests Spec.initial 0).1 (LoopSpec.final requests Spec.initial 0).2 ∧
      AppState.At after (LoopSpec.final requests Spec.initial 0).1 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Spec.Inv (LoopSpec.final requests Spec.initial 0).1 :=
  Firmware.request_sequence requests (many requests Spec.initial 0) MainInitWitness.core MainInitWitness.ram
    rfl (Or.inr rfl) rfl Blocking.stack_available

def mixed : List Fixed11 := [request .state false,request .relay3 false,request .temp false,request .setpoint false,
  request .unauth false,request .relay5 false,request .mode false,request .relayz false,request .state true,request .relay3 false]

theorem mixed_final : (LoopSpec.final mixed Spec.initial 0).2=1 ∧
    (LoopSpec.final mixed Spec.initial 0).1.temp=0xffff#16 ∧
    (LoopSpec.final mixed Spec.initial 0).1.relays 3=true := by decide +kernel

/-- The 100th actual transaction restarts serve; the following request uses
    fresh count1 and still updates the persisted relay state. -/
def hundred : List Fixed11 := List.replicate 100 (request .state false)++[request .relay3 false]

theorem hundred_count : (LoopSpec.final hundred Spec.initial 0).2=1 := by decide +kernel

theorem hundred_execution :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
      (RequestSchedules.reads (many hundred Spec.initial 0)) (UartTxLoop.events (LoopSpec.output hundred Spec.initial 0)) ∧
      LoopReady.At d after (LoopSpec.final hundred Spec.initial 0).1 1 ∧ ramRead after 0x80ffebbc#32 .w=0#32 := by
  obtain ⟨n,d,after,steps,_,ready,_,borrow,_⟩ := execution hundred
  rw [hundred_count] at ready
  exact ⟨n,d,after,steps,ready,borrow⟩
end E5R.Thermostat.FirmwareSequenceWitness
