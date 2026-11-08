import Projects.thermostat.MainLengthEnter
import Projects.thermostat.MainLengthStream
namespace E5R.Thermostat.MainLengthBody
open E5R E5R.Thermostat HttpRequestSpec MainLengthState MainHeaderStreamSpec

/-- Real fixed-length body entry through complete receiving. The initial RX
    may already contain some or all body bytes. Progress needs only the exact
    remaining finite status/data schedule, with zero reads if already full. -/
theorem contract {c ram input s head} (h : MainHeaderToBody.Ready c ram input s head)
    (amount : Nat) (kind : head.framing=.length amount) (wire : Nat → BitVec 8) (plan : MainLengthStreamPlan.Plan)
    (valid : MainLengthStreamPlan.Valid plan wire input.length (head.len+amount-input.length)) :
    ∃ n d after, n≤17+MainLengthStreamPlan.cost plan input.length (head.len+amount-input.length) ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthStreamPlan.logs plan input.length (head.len+amount-input.length)) [] ∧
      d.pc=0x80000c98#32 ∧ At d after (input++arrivals wire input.length (head.len+amount-input.length)) s head amount ∧ d.sameCsr c := by
  obtain ⟨first,a,mid,lo,hi,start,boundary,firstCsr⟩ := MainLengthEnter.contract h amount kind
  by_cases within : input.length≤head.len+amount
  · obtain ⟨rest,d,after,bound,finish,pc,state,csr⟩ := MainLengthStream.contract wire plan (head.len+amount-input.length) boundary (by omega) valid
    refine ⟨first+rest,d,after,by omega,?_,pc,state,csr.trans firstCsr⟩
    simpa only [List.nil_append] using start.observed.trans finish
  · have short : ¬input.length<head.len+amount := by omega
    have missing : head.len+amount-input.length=0 := by omega
    have post : a.pc=0x80000c98#32 ∧ At a mid input s head amount := by simpa only [Boundary,short,ite_false] using boundary
    refine ⟨first,a,mid,?_,?_,post.1,?_,firstCsr⟩
    · simp only [missing,MainLengthStreamPlan.cost];omega
    · simpa only [missing,MainLengthStreamPlan.logs] using start.observed
    · simpa only [missing,arrivals,List.range_zero,List.map_nil,List.append_nil] using post.2
end E5R.Thermostat.MainLengthBody
