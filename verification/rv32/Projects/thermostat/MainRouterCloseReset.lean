import Projects.thermostat.MainRouterCloseFrames
import Projects.thermostat.MainCloseRequestReset
import Projects.thermostat.MainCloseRequest
namespace E5R.Thermostat.MainCloseRequestReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec

/-- Reset through actual UART reception, parsing, complete Request, general
    Connection scan and persisted main close flag to actual router entry.
    Pure head acceptance/framing remain explicit G0 obligations. -/
theorem contract_routes (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head) (amount : Nat)
    (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let bytes := input++arrivals wire input.length missing
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after close, n≤4740+(77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainCloseReady.At d after bytes Spec.initial head amount 1 close ∧
      Observed.input reads=bytes ∧ MainRouterTable.At after := by
  obtain ⟨first,a,mid,bound,trace,state,bytes,routes⟩ := MainRequestBuildReset.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨last,d,after,close,lastBound,steps,ready,_,table⟩ := MainCloseRequest.contract_routes state routes
  rw [MainRequestSpans.raw_length state] at lastBound
  simp only [MainRequestInputs.entries,List.length_map] at lastBound
  refine ⟨first+last,d,after,close,by omega,?_,ready,bytes,table⟩
  simpa only [List.append_nil] using trace.trans steps.observed

end E5R.Thermostat.MainCloseRequestReset
