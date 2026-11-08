import Projects.thermostat.MainLengthWitness
import Projects.thermostat.MainLengthResetEnd
namespace E5R.Thermostat.MainLengthWitnessEnd
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthWitness
/-- Three actual reset-to-complete-fixed-body executions: zero, three and
    maximum1024 bytes. The nonconstant alphabet pattern is stored exactly;
    committed App state and every parsed Head field remain valid. -/
theorem execution (kind : Fin 3) : ∃ n d after reads, n≤150000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind++body kind ∧ d.pc=0x80000c98#32 ∧
      MainLengthState.At d after (header kind++body kind) Spec.initial (expected kind) (amount kind) ∧ d.get 25=BitVec.ofNat 32 ((header kind).length+amount kind) := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,limit,trace,pc,state,bytes,last25⟩ := MainLengthResetEnd.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) (amount kind) (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+amount kind-(header kind).length=amount kind := by rw [fs.2.1];omega
  rw [missing] at trace
  rw [missing,body_arrivals] at state bytes
  refine ⟨n,d,after,_,?_,trace,bytes,pc,state,by simpa only [fs.2.1] using last25⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  have bc (first count : Nat) : MainLengthStreamPlan.cost (plan kind) first count=33*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainLengthStreamPlan.cost,ih,Nat.mul_succ];change (25+4*2)+_= _;omega
  rw [hc,bc,missing] at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainLengthWitnessEnd
