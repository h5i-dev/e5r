import Projects.thermostat.MainHeaderResetTwo
import Projects.thermostat.MainHeaderToBody
namespace E5R.Thermostat.MainHeaderResetBody
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Conditional reset-to-body entry for any finitely scheduled successful
    header stream. Parsing, copied spans, limits and framing are all derived
    from actual UART bytes. Authentication, command handling and replies remain
    subsequent obligations. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (plan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) :
    ∃ n d after, n≤2967+MainHeaderStreamPlan.cost plan 0 fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan 0 (consume wire fuel []).received) [] ∧
      MainHeaderToBody.Ready d after (consume wire fuel []).input Spec.initial head ∧
      Observed.input (MainHeaderStreamPlan.logs plan 0 (consume wire fuel []).received)=(consume wire fuel []).input := by
  obtain ⟨hn,a,mid,bound,trace,boundary,bytes,exactResult⟩ := MainHeaderResetTwo.contract c ram wire plan fuel hp mpp masked stack space valid
  try dsimp only at boundary exactResult bound trace bytes
  have doneBoundary : MainHeaderLoopTwo.Boundary a mid (consume wire fuel []).input Spec.initial (.done head) := by simpa only [accepted] using boundary
  have parsed : HttpRequestBytes.parse (consume wire fuel []).input 1024 1024=.done head := exactResult.symm.trans accepted
  obtain ⟨bn,d,lo,hi,finish,ready,_⟩ := MainHeaderToBody.contract doneBoundary parsed
  refine ⟨hn+bn,d,_,by omega,?_,ready,bytes⟩
  simpa only [List.append_nil] using trace.trans finish.observed
end E5R.Thermostat.MainHeaderResetBody
