import Projects.thermostat.MainHeaderResetBodyBank
import Projects.thermostat.MainLengthBodyRegs
namespace E5R.Thermostat.MainLengthResetBank
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Reset through actual header parsing, successful framing dispatch and all
    fixed-length body reception. This ends before Request/routing/authentication
    and response emission. Every status/data read remains explicit. -/
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
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after, n≤2984+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ d.pc=0x80000c98#32 ∧
      MainLengthState.At d after (input++arrivals wire input.length missing) Spec.initial head amount ∧
      Observed.input reads=input++arrivals wire input.length missing ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.At d ∧ MainServeLayout.At after 0 := by
  obtain ⟨hn,a,mid,headBound,headTrace,headReady,headBytes,bank,serve⟩ := MainHeaderResetBodyBank.contract c ram wire headerPlan fuel head hp mpp masked stack space headerValid accepted
  obtain ⟨bn,d,after,bodyBound,bodyTrace,pc,state,_,last25,regs,serveFrame⟩ := MainLengthBodyRegs.contract headReady amount kind wire bodyPlan bodyValid
  refine ⟨hn+bn,d,after,by omega,?_,pc,state,?_,last25,MainGprBank.preserve regs bank,MainServeLayout.preserve serveFrame serve⟩
  · simpa only [List.append_nil] using headTrace.trans bodyTrace
  · rw [Observed.input_append,headBytes,MainLengthStreamPlan.logs_wire bodyPlan wire _ _ _ bodyValid (Nat.le_refl _)]
end E5R.Thermostat.MainLengthResetBank
