import Projects.thermostat.MainLengthLoopStep
import Projects.thermostat.MainLengthStreamPlan
namespace E5R.Thermostat.MainLengthStream
open E5R E5R.Thermostat MainLengthState MainHeaderStreamSpec

/-- Complete actual fixed-length body receiving under a finite explicit
    readiness/data schedule. Exactly the missing bytes extend the live RX
    buffer; no parsing, authentication or command result is postulated. -/
theorem contract (wire : Nat → BitVec 8) (plan : MainLengthStreamPlan.Plan) (fuel : Nat)
    {c ram input s head amount} (h : Boundary c ram input s head amount)
    (remaining : input.length+fuel=head.len+amount)
    (valid : MainLengthStreamPlan.Valid plan wire input.length fuel) :
    ∃ n d after, n≤MainLengthStreamPlan.cost plan input.length fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthStreamPlan.logs plan input.length fuel) [] ∧
      d.pc=0x80000c98#32 ∧ At d after (input++arrivals wire input.length fuel) s head amount ∧ d.sameCsr c := by
  induction fuel generalizing c ram input with
  | zero =>
    have full : ¬input.length<head.len+amount := by omega
    have post : c.pc=0x80000c98#32 ∧ At c ram input s head amount := by simpa only [Boundary,full,ite_false] using h
    refine ⟨0,c,ram,by simp only [MainLengthStreamPlan.cost];omega,?_,post.1,?_,rfl⟩
    · exact .refl _
    · simpa only [arrivals,List.range_zero,List.map_nil,List.append_nil] using post.2
  | succ fuel ih =>
    have short : input.length<head.len+amount := by omega
    have ready : Ready c ram input s head amount := by simpa only [Boundary,short,ite_true] using h
    obtain ⟨pendingOK,readyOK,datumOK⟩ := valid input.length (by omega) (by omega)
    change (UartPoll.byte (plan.datum input.length)).setWidth 8=wire input.length at datumOK
    let next := input++[wire input.length]
    have length : next.length=input.length+1 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
    have step := MainLengthLoopStep.contract ready (plan.pending input.length) (plan.ready input.length) (plan.datum input.length) pendingOK readyOK
    dsimp only at step
    rw [datumOK] at step
    obtain ⟨first,a,mid,firstBound,firstTrace,boundary,firstCsr⟩ := step
    have validNext : MainLengthStreamPlan.Valid plan wire next.length fuel := by rw [length];exact ChunkReceivePlan.valid_tail valid
    obtain ⟨rest,d,after,restBound,restTrace,pc,post,csr⟩ := ih boundary (by rw [length];omega) validNext
    have bytes : next++arrivals wire next.length fuel=input++arrivals wire input.length (fuel+1) := by
      rw [length,arrivals_succ]
      simp only [next,List.append_assoc,List.singleton_append]
    rw [bytes] at post
    refine ⟨first+rest,d,after,?_,?_,pc,post,csr.trans firstCsr⟩
    · rw [length] at restBound
      change first+rest≤25+4*(plan.pending input.length).length+MainLengthStreamPlan.cost plan (input.length+1) fuel
      omega
    · have trace := firstTrace.trans restTrace
      simpa only [MainLengthStreamPlan.logs,length,List.append_nil,List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using trace
end E5R.Thermostat.MainLengthStream
