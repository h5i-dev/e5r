import Projects.thermostat.MainRequestMethodWitness
import Projects.thermostat.MainRequestBuildReset
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainRequestBuildWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainRequestMethodWitness
/-- All six declared methods, lowercase get and a last-character DELETE
    mismatch, through actual reset, UART parsing, URI and method conversion. -/
theorem execution (kind : Fin 8) : ∃ n d after reads, n≤151000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind ∧ MainRequestBuild.Ready d after (header kind) Spec.initial (expected kind) 0 1 ∧
      after (MainRequestBuild.sp+3684#32)=BitVec.ofNat 8 (if kind.val<6 then kind.val else 6) := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,limit,trace,state,bytes⟩ := MainRequestBuildReset.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) 0 (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+0-(header kind).length=0 := by rw [fs.2.1];omega
  rw [missing] at limit trace state bytes
  simp only [arrivals,List.range_zero,List.map_nil,List.append_nil] at state bytes
  have method := state.methodByte
  rw [fs.2.2.2.1] at method
  refine ⟨n,d,after,_,?_,trace,bytes,state,method⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  rw [hc,fs.2.2.2.2] at limit
  change n≤4669+5*3+(47+8+HeadColdFutureComplete.budget 1024)*(header kind).length+0 at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainRequestBuildWitness
