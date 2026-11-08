-- G3: initialized routes survive existing Next, method and Request contracts.
import Projects.thermostat.MainRouterBankBodyFrames
import Projects.thermostat.MainRouterTable
import Projects.thermostat.MainRequestBuildReset
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainNextLengthResetBank
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
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
    ∃ n d after, n≤3391+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainNextLength.Ready d after bytes Spec.initial head amount ∧
      Observed.input reads=bytes ∧ head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry) ∧ MainGprBank.At d ∧ MainServeLayout.At after 0 ∧ MainNextLengthPayloadWords.At after MainNextLength.sp ∧ MainRouterTable.At after := by
  obtain ⟨first,a,mid,bound,trace,pc,state,bytes,a25,bank,serve,routes⟩ := MainLengthResetBank.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  have full : head.len+amount≤((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)).length := by
    simp only [List.length_append,arrivals,List.length_map,List.length_range]
    omega
  obtain ⟨d,finish,ready,regs,_⟩ := MainNextLength.contract state pc a25 full
  have serveFrame : MainServeLayout.Frame mid (MainNextLengthMemory.memory mid MainNextLength.sp head amount) := by
    apply MainServeMemoryFrames.whole (size := 92)
    · simpa only [show MainNextLength.sp+3204#32=MainServeLayout.fp by decide +kernel] using MainNextLengthMemory.frame mid MainNextLength.sp head amount 3204 92 (by decide) (by decide)
    · decide
  have exactResult := exact_result wire fuel [] (by decide +kernel)
  have parsed : HttpRequestBytes.parse (consume wire fuel []).input 1024 1024=.done head := exactResult.symm.trans accepted
  have contained := MainHeadContained.bytes _ head parsed
  refine ⟨first+407,d,_,by omega,?_,ready,bytes,contained.1,contained.2,MainGprBank.preserve regs bank,MainServeLayout.preserve serveFrame serve,MainNextLengthPayloadWords.contract mid MainNextLength.sp head amount,?_⟩
  · simpa only [List.append_nil] using trace.trans finish.observed
  · apply MainRouterTable.preserve (MainRouterTable.initialized routes)
    simpa only [ViewFrame.Region,show MainNextLength.sp+72#32=0x80ffebd8#32 by decide +kernel] using MainNextLengthMemory.frame mid MainNextLength.sp head amount 72 60 (by decide) (by decide)

end E5R.Thermostat.MainNextLengthResetBank

namespace E5R.Thermostat.MainServeNextResetPayload
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
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
    ∃ n d after, n≤4146+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainServeNext.Ready d after bytes Spec.initial head amount 0 ∧ MainServeNextPayloadWords.At after MainServeNext.sp ∧
      Observed.input reads=bytes ∧ MainRouterTable.At after := by
  obtain ⟨first,a,mid,bound,trace,next,bytes,inside,headers,bank,serve,payload,routes⟩ := MainNextLengthResetBank.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨d,finish,ready,_⟩ := MainServeNext.contract next bank serve (by decide) payload ⟨inside,headers⟩
  refine ⟨first+755,d,_,by omega,?_,ready,MainServeNextPayloadWords.stored mid _,bytes,?_⟩
  · simpa only [List.append_nil] using trace.trans finish.observed
  · apply MainRouterTable.preserve routes
    simpa only [ViewFrame.Region,show MainServeNext.sp+72#32=0x80ffebd8#32 by decide +kernel] using MainServeNextMemory.frame mid MainServeNext.sp 72 60 (by decide)

end E5R.Thermostat.MainServeNextResetPayload

namespace E5R.Thermostat.MainRequestMethodResetPayload
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
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
    ∃ n d after, n≤4209+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainRequestMethod.Ready d after bytes Spec.initial head amount 1 ∧ MainServeNextPayloadWords.At after MainServeNext.sp ∧
      Observed.input reads=bytes ∧ MainRouterTable.At after := by
  obtain ⟨first,a,mid,bound,trace,state,payload,bytes,routes⟩ := MainServeNextResetPayload.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨b,counter,readyB,_⟩ := MainRequestTarget.contract state
  have payloadB := MainRequestPayloadWords.counter mid MainServeNext.sp 0#32 (BitVec.ofNat 32 (head.len+amount)) payload
  obtain ⟨queryCount,d,queryBound,query,readyD,_⟩ := MainRequestQuery.contract readyB
  obtain ⟨methodCount,e,methodBound,method,readyE,_⟩ := MainRequestMethod.contract readyD
  refine ⟨first+(17+queryCount+methodCount),e,_,by omega,?_,readyE,payloadB,bytes,?_⟩
  · simpa only [List.append_nil] using trace.trans ((counter.trans query).trans method).observed
  · apply MainRouterTable.preserve routes
    simpa only [ViewFrame.Region,show MainServeNext.sp+72#32=0x80ffebd8#32 by decide +kernel] using MainRequestCounterMemory.frame mid MainServeNext.sp 0#32 (BitVec.ofNat 32 (head.len+amount)) 72 60 (by decide) (Or.inl (by decide))

end E5R.Thermostat.MainRequestMethodResetPayload

namespace E5R.Thermostat.MainRequestBuildReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
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
    ∃ n d after, n≤4669+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainRequestBuild.Ready d after bytes Spec.initial head amount 1 ∧
      Observed.input reads=bytes ∧ MainRouterTable.At after := by
  obtain ⟨first,a,mid,bound,trace,state,payload,bytes,routes⟩ := MainRequestMethodResetPayload.contract_routes c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  obtain ⟨d,build,ready,_⟩ := MainRequestBuild.contract state payload
  let received := (consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length (head.len+amount-(consume wire fuel []).input.length)
  refine ⟨first+460,d,_,by omega,?_,ready,bytes,?_⟩
  · simpa only [List.append_nil] using trace.trans build.observed
  · apply MainRouterTable.preserve routes
    simpa only [ViewFrame.Region,MainRequestBuild.memory,received,show MainRequestBuild.sp+72#32=0x80ffebd8#32 by decide +kernel] using MainRequestMemoryGlobalFrame.contract mid MainRequestBuild.sp MainRequestBuild.rx head amount (MainRequestBuild.method received head) (MainRequestBuild.rx+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength received head) (MainRequestBuild.queryPtr received head) (MainRequestBuild.queryLength received head) 72 60 (by decide) (Or.inl (by decide))

end E5R.Thermostat.MainRequestBuildReset
