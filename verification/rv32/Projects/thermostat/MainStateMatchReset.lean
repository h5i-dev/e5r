import Projects.thermostat.MainRequestBuildReset
import Projects.thermostat.MainRouterEntryReset
import Projects.thermostat.MainStateMatch
namespace E5R.Thermostat.MainStateMatchReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Reset through actual received bytes and the first /state route match.
    Acceptance/framing/readiness remain explicit pure upstream obligations. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head) (amount : Nat)
    (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length))
    (route : MainRequestSpans.path ((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) head=WireSpec.ascii "/state") :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let bytes := input++arrivals wire input.length missing
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after close, n≤5010+(77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainStateMatch.Ready d after bytes Spec.initial head amount 1 close ∧
      Observed.input reads=bytes := by
  obtain ⟨first,a,mid,close,bound,trace,ready,bytes⟩ := MainRouterEntryReset.contract c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨d,matched,post,_⟩ := MainStateMatch.contract ready route
  refine ⟨first+187,d,_,close,by omega,?_,post,bytes⟩
  simpa only [List.append_nil] using trace.trans matched.observed
end E5R.Thermostat.MainStateMatchReset
