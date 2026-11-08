import Projects.thermostat.MainHeaderLoopStep
import Projects.thermostat.MainHeaderStreamPlan
namespace E5R.Thermostat.MainHeaderStream
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Finite stream refinement of the actual main header receive/reparse loop.
    Every recorded status/data read is supplied by an explicit valid logical
    schedule. No physical timing, FIFO behavior or fairness is inferred. -/
theorem contract (wire : Nat → BitVec 8) (plan : MainHeaderStreamPlan.Plan) (fuel : Nat)
    {c ram input s} (h : MainHeaderLoopStep.Ready c ram input s)
    (space : input.length+fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire input.length fuel) :
    let r := consume wire fuel input
    ∃ n d after, n≤MainHeaderStreamPlan.cost plan input.length fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan input.length r.received) [] ∧
      MainHeaderLoopStep.Boundary d after r.input s r.result ∧ d.sameCsr c := by
  change ∃ n d after, n≤MainHeaderStreamPlan.cost plan input.length fuel ∧
    Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan input.length (consume wire fuel input).received) [] ∧
    MainHeaderLoopStep.Boundary d after (consume wire fuel input).input s (consume wire fuel input).result ∧ d.sameCsr c
  induction fuel generalizing c ram input with
  | zero => exact ⟨0,c,ram,by simp only [MainHeaderStreamPlan.cost];omega,.refl _,h,rfl⟩
  | succ fuel ih =>
    obtain ⟨pendingOK,readyOK,datumOK⟩ := valid input.length (by omega) (by omega)
    have byteEq : (UartPoll.byte (plan.datum input.length)).setWidth 8=wire input.length := datumOK
    let next := input++[wire input.length]
    have nextLength : next.length=input.length+1 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
    have step := MainHeaderLoopStep.contract h (plan.pending input.length) (plan.ready input.length) (plan.datum input.length) pendingOK readyOK
    dsimp only at step
    rw [byteEq] at step
    obtain ⟨first,a,mid,firstBound,firstTrace,boundary,firstCsr⟩ := step
    change MainHeaderLoopStep.Boundary a mid next s (HttpRequestBytes.parse next 1024 1024) at boundary
    have firstBound' : first≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024 :=
      Nat.le_trans firstBound (Nat.add_le_add_left (MainHeaderStreamPlan.parser_budget next.length) _)
    cases result : HttpRequestBytes.parse next 1024 1024 with
    | incomplete =>
      have nextReady : MainHeaderLoopStep.Ready a mid next s := by simpa only [result,MainHeaderLoopStep.Boundary] using boundary
      have validNext : MainHeaderStreamPlan.Valid plan wire next.length fuel := by
        rw [nextLength]
        exact ChunkReceivePlan.valid_tail valid
      obtain ⟨rest,d,after,restBound,restTrace,post,csr⟩ := ih nextReady (by rw [nextLength];omega) validNext
      have runEq : consume wire (fuel+1) input={ consume wire fuel next with received := (consume wire fuel next).received+1 } := by
        rw [consume]
        change (match HttpRequestBytes.parse next 1024 1024 with | .incomplete => _ | .reject _ => _ | .done _ => _)=_
        rw [result]
      rw [runEq]
      dsimp only
      refine ⟨first+rest,d,after,?_,?_,post,csr.trans firstCsr⟩
      · rw [nextLength] at restBound
        change first+rest≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024+MainHeaderStreamPlan.cost plan (input.length+1) fuel
        omega
      · have trace := firstTrace.trans restTrace
        simpa only [MainHeaderStreamPlan.logs,nextLength,List.append_nil] using trace
    | reject status =>
      have runEq : consume wire (fuel+1) input=⟨1,next,.reject status⟩ := by
        rw [consume]
        change (match HttpRequestBytes.parse next 1024 1024 with | .incomplete => _ | .reject _ => _ | .done _ => _)=_
        rw [result]
      rw [runEq]
      dsimp only
      refine ⟨first,a,mid,?_,?_,?_,firstCsr⟩
      · change first≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024+MainHeaderStreamPlan.cost plan (input.length+1) fuel
        omega
      · simpa only [MainHeaderStreamPlan.logs,List.append_nil] using firstTrace
      · simpa only [result] using boundary
    | done head =>
      have runEq : consume wire (fuel+1) input=⟨1,next,.done head⟩ := by
        rw [consume]
        change (match HttpRequestBytes.parse next 1024 1024 with | .incomplete => _ | .reject _ => _ | .done _ => _)=_
        rw [result]
      rw [runEq]
      dsimp only
      refine ⟨first,a,mid,?_,?_,?_,firstCsr⟩
      · change first≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024+MainHeaderStreamPlan.cost plan (input.length+1) fuel
        omega
      · simpa only [MainHeaderStreamPlan.logs,List.append_nil] using firstTrace
      · simpa only [result] using boundary
end E5R.Thermostat.MainHeaderStream
