import Projects.thermostat.RouteSpec
import Projects.thermostat.RouteLiteralInfo
set_option autoImplicit false
namespace E5R.Thermostat.RouteCaseSpec
open E5R E5R.Thermostat

def routePath (path : List (BitVec 8)) : ApiRequestSpec.Route → Prop
  | .state => path=WireSpec.ascii "/state"
  | .setpoint => path=WireSpec.ascii "/setpoint"
  | .temp => path=WireSpec.ascii "/temp"
  | .mode => path=WireSpec.ascii "/mode"
  | .relay segment => RouteSpec.relayPath path ∧ segment=path.drop 7

theorem selected (path : List (BitVec 8)) (route : ApiRequestSpec.Route) (h : RouteSpec.select path=some route) : routePath path route := by
  unfold RouteSpec.select at h
  by_cases state : path=WireSpec.ascii "/state"
  · rw [if_pos state] at h;cases h;exact state
  rw [if_neg state] at h
  by_cases setpoint : path=WireSpec.ascii "/setpoint"
  · rw [if_pos setpoint] at h;cases h;exact setpoint
  rw [if_neg setpoint] at h
  by_cases temp : path=WireSpec.ascii "/temp"
  · rw [if_pos temp] at h;cases h;exact temp
  rw [if_neg temp] at h
  by_cases mode : path=WireSpec.ascii "/mode"
  · rw [if_pos mode] at h;cases h;exact mode
  rw [if_neg mode] at h
  by_cases relay : RouteSpec.relayPath path
  · rw [if_pos relay] at h;cases h;exact ⟨relay,rfl⟩
  · rw [if_neg relay] at h;cases h

theorem literal (kind : RouteLiteralInfo.Kind) : RouteSpec.select (RouteLiteralInfo.text kind)=some (RouteLiteralInfo.route kind) := by
  cases kind <;> decide +kernel

theorem relay_disjoint {path : List (BitVec 8)} (h : RouteSpec.relayPath path) (kind : RouteLiteralInfo.Kind) : path≠RouteLiteralInfo.text kind := by
  intro selected
  have headPrefix := h.1
  rw [selected] at headPrefix
  have wrong : (RouteLiteralInfo.text kind).take 7≠WireSpec.ascii "/relay/" := by cases kind <;> decide +kernel
  exact wrong headPrefix

theorem relay_selected {path : List (BitVec 8)} (h : RouteSpec.relayPath path) : RouteSpec.select path=some (.relay (path.drop 7)) := by
  have p0 := relay_disjoint h .state
  have p1 := relay_disjoint h .setpoint
  have p2 := relay_disjoint h .temp
  have p3 := relay_disjoint h .mode
  change path≠WireSpec.ascii "/state" at p0
  change path≠WireSpec.ascii "/setpoint" at p1
  change path≠WireSpec.ascii "/temp" at p2
  change path≠WireSpec.ascii "/mode" at p3
  simp only [RouteSpec.select,p0,p1,p2,p3,h,ite_false,ite_true]

theorem missing {path : List (BitVec 8)} (h : RouteSpec.select path=none) :
    (∀ kind : RouteLiteralInfo.Kind,path≠RouteLiteralInfo.text kind) ∧ ¬RouteSpec.relayPath path := by
  constructor
  · intro kind equal
    rw [equal,literal] at h;cases h
  · intro valid
    rw [relay_selected valid] at h;cases h

theorem different (a b : RouteLiteralInfo.Kind) (h : a≠b) : RouteLiteralInfo.text a≠RouteLiteralInfo.text b := by
  cases a <;> cases b <;> first | exact False.elim (h rfl) | decide +kernel
theorem write_body (s : Spec.Snapshot) (path raw body : List (BitVec 8)) (first : Option (List (BitVec 8))) (entries : List HeaderSpec.Entry) :
    ResponseHeadSpec.body (ApiWriteHttpSpec.run s path first raw body entries).status false (ApiWriteHttpSpec.run s path first raw body entries).payload=
      (ApiWriteHttpSpec.run s path first raw body entries).payload := by
  unfold ApiWriteHttpSpec.run
  split
  · cases decoded : WireSpec.decode path body first with
    | error status => simp only [ResponseHeadSpec.body,ite_self]
    | ok cmd =>
      dsimp only
      cases result : Spec.transition true s cmd with
      | error err => cases err <;> rfl
      | ok out => rfl
  · rfl

end E5R.Thermostat.RouteCaseSpec
