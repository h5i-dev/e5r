import Projects.thermostat.RouteRelay
import Projects.thermostat.MainRelayCaptured
set_option autoImplicit false
namespace E5R.Thermostat.RelaySuccessMemory
open E5R E5R.Thermostat

/-- Successful one-segment matching determines both real capture words. -/
theorem memory (ram : Word → BitVec 8) (params : Word) (path : List (BitVec 8)) (matched : RouteSpec.relayPath path) :
    RouteRelayBody.memory ram params path=MainRelayCapture.memory ram params (BitVec.ofNat 32 path.length) := by
  have scan := RouteLiteralTail.noSlash_length (path.drop 7) matched.2.2
  have positive := List.length_pos_iff.mpr matched.2.1
  have lower : 7≤path.length := by
    have sizes := congrArg List.length matched.1
    rw [List.length_take] at sizes
    change min 7 path.length=7 at sizes
    omega
  have length : 7+(path.drop 7).length=path.length := by simp only [List.length_drop];omega
  unfold RouteRelayBody.memory RelayCaptureTail.memory
  rw [if_pos matched.1,scan,if_neg (by omega),length]

theorem count (path : List (BitVec 8)) (matched : RouteSpec.relayPath path) : RouteRelayBody.count path=1#32 := by
  have scan := RouteLiteralTail.noSlash_length (path.drop 7) matched.2.2
  have positive := List.length_pos_iff.mpr matched.2.1
  unfold RouteRelayBody.count
  rw [if_pos matched.1,scan,if_neg (by omega)]

theorem path (path : List (BitVec 8)) (matched : RouteSpec.relayPath path) : MainRelayCaptured.path (path.drop 7)=path := by
  unfold MainRelayCaptured.path
  rw [←matched.1,List.take_append_drop]
end E5R.Thermostat.RelaySuccessMemory
