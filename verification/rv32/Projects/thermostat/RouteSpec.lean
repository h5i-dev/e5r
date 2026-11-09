import Projects.thermostat.ApiReplySpec
set_option autoImplicit false
namespace E5R.Thermostat.RouteSpec
open E5R E5R.Thermostat ApiRequestSpec

/-- Fixed application's path policy, from its five registrations and its own
    path.rs segment matcher. URI/query splitting happens before this function.
    Exact case and trailing slashes matter; a relay capture is one nonempty
    segment. There is no percent decoding or unrelated HTTP policy here. -/
def relayPath (path : Bytes) : Prop :=
  path.take 7=WireSpec.ascii "/relay/" ∧ path.drop 7≠[] ∧ ∀ b∈path.drop 7, b≠47#8
instance (path : Bytes) : Decidable (relayPath path) := by unfold relayPath;infer_instance

def select (path : Bytes) : Option Route :=
  if path=WireSpec.ascii "/state" then some .state
  else if path=WireSpec.ascii "/setpoint" then some .setpoint
  else if path=WireSpec.ascii "/temp" then some .temp
  else if path=WireSpec.ascii "/mode" then some .mode
  else if relayPath path then some (.relay (path.drop 7)) else none

/-- A HEAD request runs the GET route; other mismatched methods are405.
    Route::dispatch tries earlier registrations first. These five fixed path
    families are disjoint, so this selection preserves their precedence. -/
def allows : Route → MainMethodSpec.Method → Bool
  | .state,.get | .state,.head | .temp,.post => true
  | .setpoint,.put | .mode,.put | .relay _,.put => true
  | _,_ => false

/-- Pure path/method/auth/decoder/control response. No internal ABI, parser
    result, successful handler or final machine state is a field or premise. -/
def reply (s : Spec.Snapshot) (method : MainMethodSpec.Method) (path raw body : Bytes)
    (entries : List HeaderSpec.Entry) : ApiWriteHttpSpec.Reply :=
  match select path with
  | none => ⟨s,404,[],[]⟩
  | some route =>
    if allows route method then
      match route with
      | .state => ⟨s,200,WireSpec.ascii "application/json",ReplyJson.snapshot s⟩
      | _ => ApiWriteHttpSpec.run s path route.capture raw body entries
    else ⟨s,405,[],[]⟩

/-- HEAD reports the representation length but suppresses its payload bytes.
    UART close is the existing serve/counter/buffer policy, not a TCP event. -/
def bytes (minor served : Nat) (s : Spec.Snapshot) (method : MainMethodSpec.Method) (path raw body : Bytes)
    (entries : List HeaderSpec.Entry) : Bytes :=
  let response := reply s method path raw body entries
  ResponseHeadSpec.bytes response.status response.mime response.payload.length (MainCloseSpec.mustClose minor served raw entries)++
    ResponseHeadSpec.body response.status (decide (method=.head)) response.payload

theorem not_found {path : Bytes} (missing : select path=none) (s : Spec.Snapshot) (method : MainMethodSpec.Method)
    (raw body : Bytes) (entries : List HeaderSpec.Entry) : reply s method path raw body entries=⟨s,404,[],[]⟩ := by
  simp only [reply,missing]

theorem wrong_method {path : Bytes} {route : Route} {method : MainMethodSpec.Method}
    (selected : select path=some route) (wrong : allows route method=false) (s : Spec.Snapshot)
    (raw body : Bytes) (entries : List HeaderSpec.Entry) : reply s method path raw body entries=⟨s,405,[],[]⟩ := by
  simp only [reply,selected,wrong,Bool.false_eq_true,ite_false]

theorem invariant (s : Spec.Snapshot) (method : MainMethodSpec.Method) (path raw body : Bytes)
    (entries : List HeaderSpec.Entry) (inv : Spec.Inv s) : Spec.Inv (reply s method path raw body entries).state := by
  cases selected : select path with
  | none => simpa only [reply,selected] using inv
  | some route =>
    simp only [reply,selected]
    split
    · cases route with
      | state => exact inv
      | setpoint | temp | mode | relay segment => exact ApiReplySpec.write_inv _ _ _ _ _ _ inv
    · exact inv

theorem policy_examples :
    select (WireSpec.ascii "/state")=some .state ∧ select (WireSpec.ascii "/state/")=none ∧
    select (WireSpec.ascii "/State")=none ∧ select (WireSpec.ascii "/relay/")=none ∧
    select (WireSpec.ascii "/relay/3/x")=none ∧ select (WireSpec.ascii "/relay/3")=some (.relay [51#8]) ∧
    allows .state .head=true ∧ allows .temp .head=false := by decide +kernel
end E5R.Thermostat.RouteSpec
