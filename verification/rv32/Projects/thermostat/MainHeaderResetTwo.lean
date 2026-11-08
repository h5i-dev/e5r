import Projects.thermostat.MainHeaderFirstTwo
import Projects.thermostat.MainHeaderResetQuiet
import Projects.thermostat.MainHeaderStreamTwo
namespace E5R.Thermostat.MainHeaderResetTwo
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

/-- Reset to a bounded header-stream boundary. The loader/reset/stack premises
    and every UART status/data read are explicit. No response has been emitted
    at the success/refusal cutpoints of this theorem. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (plan : MainHeaderStreamPlan.Plan) (fuel : Nat)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel) :
    let r := consume wire fuel []
    ∃ n d after, n≤2550+MainHeaderStreamPlan.cost plan 0 fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan 0 r.received) [] ∧
      MainHeaderLoopTwo.Boundary d after r.input Spec.initial r.result ∧
      Observed.input (MainHeaderStreamPlan.logs plan 0 r.received)=r.input ∧
      r.result=HttpRequestBytes.parse r.input 1024 1024 := by
  obtain ⟨old,oldRam,quiet,_⟩ := MainHeaderResetQuiet.contract B c ram hp mpp stack
  obtain ⟨a,mid,det,extended,two⟩ := MainHeaderFirstTwo.reset_contract B c ram hp mpp stack
  have equal := DetRunUnique.steps quiet.det det
  rw [equal] at quiet
  have boot : Quiet.Steps B img 2550 ⟨c,ram⟩ ⟨a,mid⟩ := quiet
  have ready : MainHeaderFirstPoll.Ready B a mid := ⟨extended.pc,extended.sp,extended.fp,extended.uart,extended.one,extended.zero,extended.dst,extended.stack,extended.app,extended.future,extended.masked,extended.header⟩
  obtain ⟨n,d,after,bound,trace,post,_⟩ := MainHeaderStreamTwo.contract wire plan fuel (MainHeaderLoopTwo.first ready two) (by simpa only [List.length_nil,Nat.zero_add] using space) valid
  have inputEq := input_bytes wire fuel []
  have logs := MainHeaderStreamPlan.logs_wire plan wire 0 (consume wire fuel []).received fuel valid (received_le wire fuel [])
  have exactResult := exact_result wire fuel [] (by decide +kernel)
  refine ⟨2550+n,d,after,by simpa only [List.length_nil] using Nat.add_le_add_left bound 2550,?_,post,?_,exactResult⟩
  · simpa only [List.nil_append,List.length_nil] using boot.observed.trans trace
  · simpa only [List.nil_append,List.length_nil] using logs.trans inputEq.symm

/-- Conditional completion of header parsing, not eventual UART response.
    Completeness and finite readiness are separately stated source properties. -/
theorem terminal (wire : Nat → BitVec 8) (fuel : Nat)
    (complete : HttpRequestBytes.parse (arrivals wire 0 fuel) 1024 1024≠.incomplete) :
    (consume wire fuel []).result≠.incomplete := by
  apply complete_progress wire fuel [] (by decide +kernel)
  simpa only [List.length_nil,List.nil_append] using complete
end E5R.Thermostat.MainHeaderResetTwo
