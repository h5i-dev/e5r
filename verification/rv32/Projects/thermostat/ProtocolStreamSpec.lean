import Projects.thermostat.RouteSpec
import Projects.thermostat.ChunkBufferSpec
import Projects.thermostat.HttpRequestBytes
import Projects.thermostat.MainCloseSpec
import Projects.thermostat.MainRequestInputs
set_option autoImplicit false
namespace E5R.Thermostat.ProtocolStreamSpec
open E5R E5R.Thermostat HttpRequestSpec

/-- This machine observes RBR/THR bytes. LSR polling and instruction scheduling
    stutter; it adds no readiness, FIFO, EOF or fairness guarantee. -/
inductive Action where
  | rx (byte : BitVec 8)
  | tx (byte : BitVec 8)
  deriving DecidableEq,Repr

structure Pending where
  response : ApiWriteHttpSpec.Reply
  close : Bool
  nextCount : Nat
  remaining : List (BitVec 8)

inductive Phase where
  | head (bytes : List (BitVec 8))
  | length (original : List (BitVec 8)) (head : Head) (amount : Nat) (body : List (BitVec 8))
  | chunked (original : List (BitVec 8)) (head : Head) (rawUsed : Nat) (decoder : CState) (body : List (BitVec 8))
  | reply (pending : Pending)

structure State where
  snapshot : Spec.Snapshot
  served : Nat
  phase : Phase

def initial : State := ⟨Spec.initial,0,.head []⟩

def enqueue (m : State) (response : ApiWriteHttpSpec.Reply) (close headOnly : Bool) : State :=
  {m with phase := .reply ⟨response,close,(if close then 0 else m.served+1),
    ResponseHeadSpec.bytes response.status response.mime response.payload.length close++
      ResponseHeadSpec.body response.status headOnly response.payload⟩}

def reject (m : State) (status : Nat) : State := enqueue m ⟨m.snapshot,status,[],[]⟩ true false

def dispatch (m : State) (original body : List (BitVec 8)) (head : Head) : State :=
  let method := MainMethodSpec.decode (MainMethodBytes.token original head.method.2)
  let path := MainRequestSpans.path original head
  let entries := MainRequestInputs.entries head
  enqueue m (RouteSpec.reply m.snapshot method path original body entries)
    (MainCloseSpec.mustClose head.minor (m.served+1) original entries) (decide (method=.head))

def chunkContinue (m : State) (original : List (BitVec 8)) (head : Head)
    (rawUsed : Nat) (decoder : CState) (body : List (BitVec 8)) : State :=
  if rawUsed=2048 then reject m 413
  else {m with phase := .chunked original head rawUsed decoder body}

/-- Pure one-byte request parsing. It uses the reviewed independent parser,
    dechunker, route/auth/control evaluator and HTTP serializer. Invalid phase
    actions are absent rather than silently accepting extra data during TX. -/
def receive (m : State) (byte : BitVec 8) : Option State :=
  match m.phase with
  | .head input =>
    if input.length<2048 then
      let next := input++[byte]
      match HttpRequestBytes.parse next 1024 1024 with
      | .incomplete => some {m with phase := .head next}
      | .reject status => some (reject m status)
      | .done head =>
        match head.framing with
        | .empty => some (dispatch m next [] head)
        | .length amount =>
          if amount=0 then some (dispatch m next [] head)
          else some {m with phase := .length next head amount []}
        | .chunked => some {m with phase := .chunked next head head.len cStart []}
    else none
  | .length original head amount body =>
    if body.length<amount then
      let next := body++[byte]
      if next.length=amount then some (dispatch m original next head)
      else some {m with phase := .length original head amount next}
    else none
  | .chunked original head rawUsed decoder body =>
    if rawUsed<2048 then
      let (after,out) := chunkStep decoder byte.toNat 1024
      match out with
      | .nothing => some (chunkContinue m original head (rawUsed+1) after body)
      | .data => some (chunkContinue m original head (rawUsed+1) after (body++[byte]))
      | .done => some (dispatch m original body head)
      | .reject status => some (reject m status)
    else none
  | .reply _ => none

/-- Silent internal steps permit the real computation/restart between byte
    events. A reply commits only at its designated completed boundary. -/
inductive Step : State → Option Action → State → Prop where
  | idle (m : State) : Step m none m
  | receive {m next byte} : receive m byte=some next → Step m (some (.rx byte)) next
  | transmit {m p byte rest} : m.phase=.reply p → p.remaining=byte::rest →
      Step m (some (.tx byte)) {m with phase := .reply {p with remaining := rest}}
  | complete {m p} : m.phase=.reply p → p.remaining=[] →
      Step m none ⟨p.response.state,p.nextCount,.head []⟩

inductive Run : State → List Action → State → Prop where
  | refl (m) : Run m [] m
  | step {a b c label old} : Run a old b → Step b label c → Run a (old++label.toList) c

/-- Reply transmission emits exactly a prefix of the queued representation;
    an incomplete output cannot be mistaken for a completed transaction. -/
theorem transmit_suffix {m p byte rest} (phase : m.phase=.reply p) (bytes : p.remaining=byte::rest) :
    Step m (some (.tx byte)) {m with phase := .reply {p with remaining := rest}} := .transmit phase bytes

theorem reject_reset (m : State) (status : Nat) :
    (match (reject m status).phase with | .reply p => p.close=true ∧ p.nextCount=0 ∧ p.response.state=m.snapshot | _ => False) := by
  exact ⟨rfl,rfl,rfl⟩

/-- No program observation can consume another input byte while a response
    is pending; this does not say the environment cannot buffer future bytes. -/
theorem no_rx_during_reply {m p} (phase : m.phase=.reply p) (byte : BitVec 8) : receive m byte=none := by
  simp only [receive,phase]
end E5R.Thermostat.ProtocolStreamSpec
