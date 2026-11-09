import Projects.thermostat.RuntimeRelayCaptured
import Projects.thermostat.StackRuntimeLiteralInput
set_option autoImplicit false
namespace E5R.Thermostat.StackRuntimeRelayCaptured
open E5R E5R.Thermostat HttpRequestSpec RuntimeRelayCaptured
theorem path_view {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) (param : List (BitVec 8))
    (route : MainRequestSpans.path input head=path param) (nonempty : param≠[]) :
    Bytes.Span StackBoard.board ram (RuntimeRouteEnvelope.rx+BitVec.ofNat 32 head.target.1) (path param) ∧
      MainRequestBuild.pathLength input head=size param ∧ 8≤(size param).toNat ∧
      WordRegions.Disjoint (RuntimeRouteEnvelope.rx+BitVec.ofNat 32 head.target.1) (path param).length 0x80ffeb30#32 96 := by
  obtain ⟨span,length,separate⟩ := StackRuntimeLiteralInput.literal_view h (path param) route
  have count : (path param).length=7+param.length := by unfold path;rw [List.length_append];rfl
  have bound : 7+param.length<2^32 := by rw [←count];exact span.length
  refine ⟨span,?_,?_,separate⟩
  · change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=size param
    rw [length,count];rfl
  · unfold size
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
    have positive := List.length_pos_iff.mpr nonempty
    omega
end E5R.Thermostat.StackRuntimeRelayCaptured
