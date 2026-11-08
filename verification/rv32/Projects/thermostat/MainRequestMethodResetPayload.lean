import Projects.thermostat.MainServeNextResetPayload
import Projects.thermostat.MainRequestMethod
import Projects.thermostat.MainRequestPayloadWords
namespace E5R.Thermostat.MainRequestMethodResetPayload
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Actual reset through fixed-body parsing, URI splitting and full method
    conversion. Exact UART bytes determine the path, query and typed method. -/
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
    ∃ n d after, n≤4209+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainRequestMethod.Ready d after bytes Spec.initial head amount 1 ∧ MainServeNextPayloadWords.At after MainServeNext.sp ∧
      Observed.input reads=bytes := by
  obtain ⟨first,a,mid,bound,trace,state,payload,bytes⟩ := MainServeNextResetPayload.contract c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨b,counter,readyB,_⟩ := MainRequestTarget.contract state
  have payloadB := MainRequestPayloadWords.counter mid MainServeNext.sp 0#32 (BitVec.ofNat 32 (head.len+amount)) payload
  obtain ⟨queryCount,d,queryBound,query,readyD,_⟩ := MainRequestQuery.contract readyB
  obtain ⟨methodCount,e,methodBound,method,readyE,_⟩ := MainRequestMethod.contract readyD
  refine ⟨first+(17+queryCount+methodCount),e,_,by omega,?_,readyE,payloadB,bytes⟩
  simpa only [List.append_nil] using trace.trans ((counter.trans query).trans method).observed

end E5R.Thermostat.MainRequestMethodResetPayload
