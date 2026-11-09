import Projects.thermostat.CompleteRequestSchedules
set_option autoImplicit false
namespace E5R.Thermostat.CompleteRequestSchedules
open E5R E5R.Thermostat CompleteRequestSpec

inductive Many : List Request → Spec.Snapshot → Nat → Type where
  | nil (s : Spec.Snapshot) (served : Nat) : Many [] s served
  | cons {r : Request} {rs : List Request} {s : Spec.Snapshot} {served : Nat}
      (one : One r s) (rest : Many rs (r.reply s).state (r.nextCount served)) : Many (r::rs) s served

def manyReads : {rs : List Request} → {s : Spec.Snapshot} → {served : Nat} → Many rs s served → List Observed.Read
  | _,_,_,.nil _ _ => []
  | _::_,_,served,.cons one rest => reads served one++manyReads rest

/-- Every complete accepted request re-establishes all concrete prerequisites
    for the next request, including real close/restart/count100 behavior. -/
theorem execute_many {rs s served} (plans : Many rs s served) {c ram} (h : LoopReady.At c ram s served) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (manyReads plans)
      (UartTxLoop.events (CompleteRequestSpec.output rs s served)) ∧
      Observed.input (manyReads plans)=CompleteRequestSpec.input rs ∧
      LoopReady.At d after (CompleteRequestSpec.final rs s served).1 (CompleteRequestSpec.final rs s served).2 := by
  induction plans generalizing c ram with
  | nil s served => exact ⟨0,c,ram,.refl _,rfl,h⟩
  | @cons r rs s served one rest ih =>
    obtain ⟨first,a,mid,trace,ready⟩ := execute one h
    obtain ⟨last,d,after,finish,acceptedRest,post⟩ := ih ready
    refine ⟨first+last,d,after,?_,?_,post⟩
    · simpa only [manyReads,CompleteRequestSpec.output,UartTxLoop.events,List.map_append,List.append_assoc] using trace.trans finish
    · simp only [manyReads,Observed.input_append,accepted one served,acceptedRest,CompleteRequestSpec.input,List.flatMap_cons]
end E5R.Thermostat.CompleteRequestSchedules

namespace E5R.Thermostat.Firmware
open E5R E5R.Thermostat CompleteRequestSpec

/-- Complete accepted-input integration, beyond Fixed11: all methods/paths,
    Empty/Content-Length/complete bounded Chunked, original-header auth and
    close policy, exact accepted RBR and complete HTTP output, committed RAM and
    reusable loop boundary. Finite valid schedules give conditional progress;
    arbitrary partial/rejected streams and every-prefix safety remain separate. -/
theorem complete_request_sequence (requests : List Request)
    (plans : CompleteRequestSchedules.Many requests Spec.initial 0) (c : Core) (ram : Word → BitVec 8)
    (pc : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (_masked : c.mie_=false)
    (stack : Memory.Block UartPlatform.board 0x80ff0000#32 65536) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (CompleteRequestSchedules.manyReads plans)
      (UartTxLoop.events (CompleteRequestSpec.output requests Spec.initial 0)) ∧
      Observed.input (CompleteRequestSchedules.manyReads plans)=CompleteRequestSpec.input requests ∧
      LoopReady.At d after (CompleteRequestSpec.final requests Spec.initial 0).1 (CompleteRequestSpec.final requests Spec.initial 0).2 ∧
      AppState.At after (CompleteRequestSpec.final requests Spec.initial 0).1 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Spec.Inv (CompleteRequestSpec.final requests Spec.initial 0).1 := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset c ram pc mpp stack
  obtain ⟨last,d,after,steps,accepted,post⟩ := CompleteRequestSchedules.execute_many plans ready
  refine ⟨2550+last,d,after,?_,accepted,post,post.receive.stable.app,post.receive.stable.app.available,post.receive.stable.invariant⟩
  simpa only [List.nil_append] using boot.observed.trans steps
end E5R.Thermostat.Firmware
