import Projects.thermostat.RuntimeRelayMatch
import Projects.thermostat.RuntimeRelayCaptured
import Projects.thermostat.RelaySuccessMemory
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelaySuccess
open E5R E5R.Thermostat HttpRequestSpec

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeLiteralInput.At c ram input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32)
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head)) :
    ∃ n d after,Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      RuntimeRelayCaptured.At c ram d after input s head amount rawUsed served lowValue close ((RuntimeRequestSpans.path input head).drop 7) ∧
      ViewFrame.Region ram after RuntimeRouteEnvelope.sp 3304 := by
  let param := (RuntimeRequestSpans.path input head).drop 7
  have pathEq : RuntimeRequestSpans.path input head=RuntimeRelayCaptured.path param := (RelaySuccessMemory.path _ route).symm
  have leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys := by
    rw [pathEq];exact ⟨WireSpec.ascii "relay/"++param,rfl⟩
  obtain ⟨n,d,bound,trace,pc,result,captures,abi,csr,low,high,stable⟩ := RuntimeRelayMatch.contract h leading
  have memory : RuntimeRelayMatch.memory ram c input head=RuntimeRelayCaptured.memory ram c param := by
    unfold RuntimeRelayMatch.memory RuntimeRelayCaptured.memory
    rw [RelaySuccessMemory.memory _ _ _ route,pathEq]
    have len : (RuntimeRelayCaptured.path param).length=7+param.length := by unfold RuntimeRelayCaptured.path;rw [List.length_append];rfl
    rw [len];rfl
  have flag : d.get 10=1#32 := by simpa only [route,ite_true] using result
  have count : d.get 11=1#32 := by rw [RelaySuccessMemory.count _ route] at captures;exact captures
  refine ⟨n,d,_,trace,⟨h.live,pathEq,route.2.1,route.2.2,memory,pc,flag,count,?_,?_,csr⟩,?_⟩
  · intro r member
    have subset : ∀ r : Reg,r∈[2,8,18,19,22,23,24,26] → r∈[1,2,3,4,5,6,7,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := by decide
    exact abi r (subset r member)
  · exact (abi 24 (by decide)).trans h.live.firstSlot
  · intro i;exact low ⟨i.val,by have := i.isLt;omega⟩
end E5R.Thermostat.RuntimeRelaySuccess
