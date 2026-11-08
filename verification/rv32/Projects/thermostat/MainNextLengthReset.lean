import Projects.thermostat.MainLengthResetEnd
import Projects.thermostat.MainNextLength
import Projects.thermostat.MainHeadContained
namespace E5R.Thermostat.MainNextLengthReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Reset to the actual fixed-length Next::Ready dispatch boundary. All
    request spans, body positions and actual RAM/register layouts are derived
    from the received stream. Routing/authentication and replies follow later. -/
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
    ∃ n d after, n≤3391+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ MainNextLength.Ready d after bytes Spec.initial head amount ∧
      Observed.input reads=bytes ∧ head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry) := by
  obtain ⟨first,a,mid,bound,trace,pc,state,bytes,a25⟩ := MainLengthResetEnd.contract c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid
  have full : head.len+amount≤((consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)).length := by
    simp only [List.length_append,arrivals,List.length_map,List.length_range]
    omega
  obtain ⟨d,finish,ready,_,_⟩ := MainNextLength.contract state pc a25 full
  have exactResult := exact_result wire fuel [] (by decide +kernel)
  have parsed : HttpRequestBytes.parse (consume wire fuel []).input 1024 1024=.done head := exactResult.symm.trans accepted
  have contained := MainHeadContained.bytes _ head parsed
  refine ⟨first+407,d,_,by omega,?_,ready,bytes,contained.1,contained.2⟩
  simpa only [List.append_nil] using trace.trans finish.observed
end E5R.Thermostat.MainNextLengthReset
