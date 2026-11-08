-- Satisfying reset/UART cases for initialized route-table preservation.
import Projects.thermostat.MainRouterCloseReset
import Projects.thermostat.MainCloseRequestWitness
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainCloseRequestWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
theorem execution_routes (kind : Fin 4) : ∃ n d after reads, n≤500000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind ∧
      MainCloseReady.At d after (header kind) Spec.initial (expected kind) 0 1 (closes kind) ∧ MainRouterTable.At after := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,close,limit,trace,state,bytes,table⟩ := MainCloseRequestReset.contract_routes MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) 0 (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+0-(header kind).length=0 := by rw [fs.2.1];omega
  rw [missing] at limit trace state bytes
  simp only [arrivals,List.range_zero,List.map_nil,List.append_nil] at state bytes
  have rawEq : MainRequestSpans.raw (header kind) (expected kind) 0=header kind := by simp only [MainRequestSpans.raw,Nat.add_zero,fs.2.1,List.take_length]
  have selected : close=closes kind := state.spec.trans (by rw [rawEq];exact pure_close kind)
  rw [selected] at state
  refine ⟨n,d,after,_,?_,trace,bytes,state,table⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  rw [hc,fs.2.2.2.1] at limit
  have proofBound := fs.2.2.2.2
  simp only [Nat.add_zero,MainLengthStreamPlan.cost] at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainCloseRequestWitness
