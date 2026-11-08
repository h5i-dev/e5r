import Projects.thermostat.MainRelayChain
import Projects.thermostat.MainRelayWriteInput
import Projects.thermostat.MainReadReset
namespace E5R.Thermostat.MainRelayEntryReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Reset and actual UART bytes derive all five route attempts, real capture
    stores and every generic write-handler prerequisite. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head) (amount : Nat) (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length))
    (param : List (BitVec 8)) (nonempty : param≠[]) (noSlash : ∀ b∈param, b≠47#8)
    (route : MainRequestSpans.path ((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) head=MainRelayCaptured.path param)
    (method : MainMethodSpec.decode (MainMethodBytes.token ((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) head.method.2)=.put) :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let bytes := input++arrivals wire input.length missing
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after close, n≤5730+5*param.length+(77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+
        MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧
      MainApiWriteCaller.Ready 3 0x80fffa2c#32 (MainRelayCaptured.path param) (some param) d after bytes Spec.initial head amount 1 close ∧
      d.mie_=false ∧ Observed.input reads=bytes := by
  obtain ⟨first,a,mid,close,bound,trace,ready,bytes,routes⟩ := MainCloseRequestReset.contract_routes c ram wire headerPlan fuel head amount bodyPlan
    hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨b,entry,entered,_⟩ := MainRouterEntry.contract ready routes
  obtain ⟨origin,before,z,r2,n,chainBound,chain,captured⟩ := MainRelayChain.contract entered
    (MainRouterFutures.initialized mid) param nonempty noSlash route (MainReadReset.reply_capacity mid)
  obtain ⟨d,called,input,dm⟩ := MainRelayWriteInput.contract captured method
  refine ⟨first+83+n+26,d,_,close,by omega,?_,input,dm,bytes⟩
  simpa only [List.append_nil,Nat.add_assoc] using trace.trans ((entry.trans chain).trans called).observed
end E5R.Thermostat.MainRelayEntryReset
