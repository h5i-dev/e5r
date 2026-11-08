import Projects.thermostat.MainRequestBuildReset
import Projects.thermostat.MainRouterEntry
namespace E5R.Thermostat.MainRouterEntryReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Reset to the actual first path matcher with derived pattern/path/params
    arguments, real route future stores, App/RX/Request/serve preservation and
    startup-derived route contents. No matcher or handler result is assumed. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
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
    ∃ n d after close, n≤4823+(77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainRouterEntry.At d after bytes Spec.initial head amount 1 close ∧
      Observed.input reads=bytes := by
  obtain ⟨first,a,mid,close,bound,trace,ready,bytes,routes⟩ := MainCloseRequestReset.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨d,entry,post,_⟩ := MainRouterEntry.contract ready routes
  refine ⟨first+83,d,_,close,by omega,?_,post,bytes⟩
  simpa only [List.append_nil] using trace.trans entry.observed
end E5R.Thermostat.MainRouterEntryReset
