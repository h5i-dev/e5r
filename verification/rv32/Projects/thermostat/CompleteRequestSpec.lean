import Projects.thermostat.RouteSpec
import Projects.thermostat.MainHeaderStreamSpec
import Projects.thermostat.ChunkBufferSpec
import Projects.thermostat.MainCloseSpec
import Projects.thermostat.MainMethodSpec
import Projects.thermostat.MainMethodBytes
import Projects.thermostat.MainRequestInputs
import Projects.thermostat.ResponseHeadSpec
set_option autoImplicit false
namespace E5R.Thermostat.CompleteRequestSpec
open E5R E5R.Thermostat HttpRequestSpec

/-- Pure accepted complete-input domain, independent of machine layouts and
    outcomes. Malformed and partial streams belong to the separate T3 machine. -/
inductive Framed (wire : Nat → BitVec 8) (head : Head) where
  | empty (kind : head.framing=.empty)
  | length (amount : Nat) (kind : head.framing=.length amount)
  | chunked (budget : Nat) (kind : head.framing=.chunked)
      (space : head.len+budget≤2048)
      (done : (ChunkBufferSpec.consume wire budget head.len head.len cStart []).stop=.done)

structure Request where
  wire : Nat → BitVec 8
  fuel : Nat
  head : Head
  space : fuel≤2048
  accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head
  framed : Framed wire head

def Request.original (r : Request) := (MainHeaderStreamSpec.consume r.wire r.fuel []).input

def Request.body (r : Request) : List (BitVec 8) := match r.framed with
  | .empty _ => []
  | .length amount _ => MainHeaderStreamSpec.arrivals r.wire r.head.len amount
  | .chunked budget _ _ _ => (ChunkBufferSpec.consume r.wire budget r.head.len r.head.len cStart []).body

def Request.bodyCount (r : Request) : Nat := match r.framed with
  | .empty _ => 0
  | .length amount _ => amount
  | .chunked budget _ _ _ => (ChunkBufferSpec.consume r.wire budget r.head.len r.head.len cStart []).read-r.head.len

def Request.input (r : Request) := r.original++MainHeaderStreamSpec.arrivals r.wire r.head.len r.bodyCount

def Request.reply (r : Request) (s : Spec.Snapshot) :=
  RouteSpec.reply s (MainMethodSpec.decode (MainMethodBytes.token r.original r.head.method.2))
    (MainRequestSpans.path r.original r.head) r.original r.body (MainRequestInputs.entries r.head)

def Request.isHead (r : Request) := decide (MainMethodSpec.decode (MainMethodBytes.token r.original r.head.method.2)=.head)

def Request.close (r : Request) (served : Nat) := MainCloseSpec.mustClose r.head.minor (served+1) r.original (MainRequestInputs.entries r.head)

def Request.nextCount (r : Request) (served : Nat) := if r.close served then 0 else served+1

def Request.output (r : Request) (s : Spec.Snapshot) (served : Nat) :=
  ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length (r.close served)++
    ResponseHeadSpec.body (r.reply s).status r.isHead (r.reply s).payload

def final : List Request → Spec.Snapshot → Nat → Spec.Snapshot × Nat
  | [],s,served => (s,served)
  | r::rs,s,served => final rs (r.reply s).state (r.nextCount served)

def output : List Request → Spec.Snapshot → Nat → List (BitVec 8)
  | [],_,_ => []
  | r::rs,s,served => r.output s served++output rs (r.reply s).state (r.nextCount served)

def input (rs : List Request) := rs.flatMap Request.input
end E5R.Thermostat.CompleteRequestSpec
