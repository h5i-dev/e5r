import Projects.thermostat.RouteSpec
import Projects.thermostat.RouteLiteralInfo
set_option autoImplicit false
namespace E5R.Thermostat.RouteRefusalSpec
open E5R E5R.Thermostat

def known (path : List (BitVec 8)) : Prop := path=WireSpec.ascii "/state" ∨ path=WireSpec.ascii "/setpoint" ∨ path=WireSpec.ascii "/temp" ∨ path=WireSpec.ascii "/mode"
instance (path : List (BitVec 8)) : Decidable (known path) := by unfold known;infer_instance

def status (path : List (BitVec 8)) : Nat := if known path then 405 else 404

theorem reply (s : Spec.Snapshot) (method : MainMethodSpec.Method) (path raw body : List (BitVec 8)) (entries : List HeaderSpec.Entry)
    (denied : ∀ kind : RouteLiteralInfo.Kind,path=RouteLiteralInfo.text kind → RouteSpec.allows (RouteLiteralInfo.route kind) method=false)
    (missing : ¬RouteSpec.relayPath path) : RouteSpec.reply s method path raw body entries=⟨s,status path,[],[]⟩ := by
  by_cases state : path=WireSpec.ascii "/state"
  · have selected : RouteSpec.select path=some .state := by rw [state];decide +kernel
    have bad : RouteSpec.allows .state method=false := denied .state state
    have code : status path=405 := if_pos (Or.inl state)
    rw [RouteSpec.wrong_method selected bad,code]
  by_cases setpoint : path=WireSpec.ascii "/setpoint"
  · have selected : RouteSpec.select path=some .setpoint := by rw [setpoint];decide +kernel
    have bad : RouteSpec.allows .setpoint method=false := denied .setpoint setpoint
    have code : status path=405 := if_pos (Or.inr (Or.inl setpoint))
    rw [RouteSpec.wrong_method selected bad,code]
  by_cases temp : path=WireSpec.ascii "/temp"
  · have selected : RouteSpec.select path=some .temp := by rw [temp];decide +kernel
    have bad : RouteSpec.allows .temp method=false := denied .temp temp
    have code : status path=405 := if_pos (Or.inr (Or.inr (Or.inl temp)))
    rw [RouteSpec.wrong_method selected bad,code]
  by_cases mode : path=WireSpec.ascii "/mode"
  · have selected : RouteSpec.select path=some .mode := by rw [mode];decide +kernel
    have bad : RouteSpec.allows .mode method=false := denied .mode mode
    have code : status path=405 := if_pos (Or.inr (Or.inr (Or.inr mode)))
    rw [RouteSpec.wrong_method selected bad,code]
  have selected : RouteSpec.select path=none := by simp only [RouteSpec.select,state,setpoint,temp,mode,missing,ite_false]
  have code : status path=404 := if_neg (by simp only [known,state,setpoint,temp,mode,false_or,not_false_eq_true])
  rw [RouteSpec.not_found selected,code]
end E5R.Thermostat.RouteRefusalSpec
