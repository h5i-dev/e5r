import Projects.thermostat.ApiWriteHttpSpec
import Projects.thermostat.HttpRequestBytes
set_option autoImplicit false
namespace E5R.Thermostat.ApiRequestSpec
open E5R E5R.Thermostat HttpRequestSpec

abbrev Bytes := List (BitVec 8)

inductive Route where
  | state | setpoint | temp | mode
  | relay (segment : Bytes)
  deriving DecidableEq, Repr

def Route.path : Route → Bytes
  | .state => WireSpec.ascii "/state"
  | .setpoint => WireSpec.ascii "/setpoint"
  | .temp => WireSpec.ascii "/temp"
  | .mode => WireSpec.ascii "/mode"
  | .relay segment => WireSpec.ascii "/relay/" ++ segment

def Route.method : Route → Bytes
  | .state => WireSpec.ascii "GET"
  | .temp => WireSpec.ascii "POST"
  | _ => WireSpec.ascii "PUT"

def Route.Valid : Route → Prop
  | .relay segment => segment ≠ [] ∧ ∀ b ∈ segment,
      isTargetByte b.toNat = true ∧ b ≠ 47#8 ∧ b ≠ 63#8
  | _ => True

def Route.capture : Route → Option Bytes
  | .relay segment => some segment
  | _ => none

/-- Decomposed OWS is only a representation of the raw field bytes. Names,
    order, case, ordinary duplicates, and internal value whitespace are free. -/
structure Header where
  name : Bytes
  before : Bytes := []
  value : Bytes
  after : Bytes := []
  deriving DecidableEq, Repr

def Header.bytes (h : Header) : Bytes :=
  h.name ++ [58#8] ++ h.before ++ h.value ++ h.after ++ [13#8,10#8]

def Header.Valid (h : Header) : Prop :=
  h.name ≠ [] ∧ (∀ b ∈ h.name, isTchar b.toNat = true) ∧
  (∀ b ∈ h.before, isOws b.toNat = true) ∧
  (∀ b ∈ h.value, isFieldByte b.toNat = true) ∧
  (∀ b ∈ h.after, isOws b.toNat = true) ∧
  (h.value = [] → h.after = []) ∧
  (h.value ≠ [] → isOws (h.value.headD 0#8).toNat = false ∧
    isOws (h.value.getLastD 0#8).toNat = false)

def Header.kind (h : Header) : Nat :=
  let name := h.name.map (fun b => HttpRequestSpec.lower b.toNat)
  if name = litHost then 1
  else if name = litContentLength then 2
  else if name = litTransferEncoding then 3
  else 0

/-- Arbitrarily many leading zeroes are allowed within the head-size bound. -/
def decimal (digits : Bytes) : Nat :=
  digits.foldl (fun acc b => 10*acc + (b.toNat-48)) 0

def Header.LengthValue (h : Header) (amount : Nat) : Prop :=
  h.after = [] ∧ h.value ≠ [] ∧
  (∀ b ∈ h.value, 48 ≤ b.toNat ∧ b.toNat ≤ 57) ∧ decimal h.value = amount

def Header.field (h : Header) (offset : Nat) : Field :=
  let colon := offset+h.name.length
  let start := colon+1+h.before.length
  ⟨offset,colon,start,start+h.value.length⟩

def fieldsAt : List Header → Nat → List Field
  | [],_ => []
  | h::hs,offset => h.field offset :: fieldsAt hs (offset+h.bytes.length)

def target (route : Route) (query : Option Bytes) : Bytes :=
  route.path ++ match query with | none => [] | some q => 63#8::q

def requestLine (route : Route) (query : Option Bytes) : Bytes :=
  route.method ++ [32#8] ++ target route query ++ WireSpec.ascii " HTTP/1.1\r\n"

def headBytes (route : Route) (query : Option Bytes) (headers : List Header) : Bytes :=
  requestLine route query ++ headers.flatMap Header.bytes ++ [13#8,10#8]

/-- Structural T1 domain. No parser result, handler outcome, PC, register or
    machine layout is a field of this domain. Authentication and body decoding
    are deliberately unrestricted. Other framing/methods remain in T3 scope. -/
structure Fixed11 where
  route : Route
  query : Option Bytes
  headers : List Header
  body : Bytes
  routeValid : route.Valid
  queryValid : ∀ q, query = some q → ∀ b ∈ q, isTargetByte b.toNat = true
  headersValid : ∀ h ∈ headers, h.Valid
  headerCount : headers.length ≤ 16
  hostCount : (headers.filter (fun h => decide (h.kind = 1))).length = 1
  lengthCount : (headers.filter (fun h => decide (h.kind = 2))).length = 1
  noTransfer : ∀ h ∈ headers, h.kind ≠ 3
  lengthValue : ∀ h ∈ headers, h.kind = 2 → h.LengthValue body.length
  headBound : (headBytes route query headers).length ≤ 1024
  bodyBound : body.length ≤ 1024

def Fixed11.headBytes (r : Fixed11) := ApiRequestSpec.headBytes r.route r.query r.headers
def Fixed11.bytes (r : Fixed11) := r.headBytes ++ r.body

/-- Offsets are computed from syntax, independently of the executable parser. -/
def Fixed11.head (r : Fixed11) : Head :=
  let m := r.route.method.length
  ⟨(0,m),(m+1,m+1+(target r.route r.query).length),1,
    fieldsAt r.headers (requestLine r.route r.query).length,
    r.headBytes.length,.length r.body.length⟩

def Fixed11.reply (r : Fixed11) (s : Spec.Snapshot) : ApiWriteHttpSpec.Reply :=
  match r.route with
  | .state => ⟨s,200,WireSpec.ascii "application/json",ReplyJson.snapshot s⟩
  | route => ApiWriteHttpSpec.run s route.path route.capture r.bytes r.body
      (r.head.headers.map HttpRequestBytes.entry)

theorem Fixed11.total_bound (r : Fixed11) : r.bytes.length ≤ 2048 := by
  have := r.headBound
  have := r.bodyBound
  simp only [Fixed11.bytes,List.length_append]
  exact Nat.add_le_add ‹r.headBytes.length ≤ 1024› ‹r.body.length ≤ 1024›

theorem Fixed11.framing (r : Fixed11) : r.head.framing = .length r.body.length := rfl

end E5R.Thermostat.ApiRequestSpec
