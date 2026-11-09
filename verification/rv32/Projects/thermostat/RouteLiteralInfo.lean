import Projects.thermostat.ApiRequestSpec
import Projects.thermostat.RomSpan
import Projects.thermostat.UartPlatform
import Projects.thermostat.WordRegions
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralInfo
open E5R E5R.Thermostat
inductive Kind where | state | setpoint | temp | mode deriving DecidableEq

def pointer : Kind → Word
  | .state => 0x80005b83#32 | .setpoint => 0x80005b89#32 | .temp => 0x80005b92#32 | .mode => 0x80005b97#32

def first : Kind → BitVec 8 | .state | .setpoint => 115#8 | .temp => 116#8 | .mode => 109#8
def rest : Kind → List (BitVec 8)
  | .state => WireSpec.ascii "tate" | .setpoint => WireSpec.ascii "etpoint" | .temp => WireSpec.ascii "emp" | .mode => WireSpec.ascii "ode"
def text (kind : Kind) := 47#8::first kind::rest kind
def route : Kind → ApiRequestSpec.Route | .state => .state | .setpoint => .setpoint | .temp => .temp | .mode => .mode

theorem pure_route (kind : Kind) : text kind=(route kind).path := by cases kind <;> rfl

theorem static (kind : Kind) : (∀ b∈first kind::rest kind,b≠47#8) ∧ first kind≠123#8 ∧
    (text kind).length≤2048 ∧ (first kind::rest kind).length≤8 := by cases kind <;> decide +kernel

/-- Fixed literal RAM/ROM read conditions are checked against this same ELF,
    rather than environmental assumptions supplied by a request. -/
theorem span (kind : Kind) (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram (pointer kind) (text kind) := by
  cases kind <;> apply ReadBytes.of_data <;> decide +kernel

theorem separate (kind : Kind) : WordRegions.Disjoint (pointer kind) (text kind).length 0x80ffeb30#32 96 :=
  WordRegions.before _ _ _ _ (by cases kind <;> decide +kernel) (by decide +kernel)
end E5R.Thermostat.RouteLiteralInfo
