import Projects.thermostat.RejectHeaderCycle
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.UartWriteWitness
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.RejectHeaderWitness
open E5R E5R.Thermostat

def wire (k : Nat) : BitVec 8 := [13#8,10#8][k]?.getD 0#8
def plan : MainHeaderStreamPlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire k).toNat⟩
def slots := List.replicate (ResponseHeadSpec.bytes 400 [] 0 true).length UartWriteWitness.slot1

theorem valid : MainHeaderStreamPlan.Valid plan wire 0 2 := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire k)⟩
  intro status mem;cases mem

theorem rejects : (MainHeaderStreamSpec.consume wire 2 []).result=.reject 400 := by decide +kernel

theorem received : (MainHeaderStreamSpec.consume wire 2 []).received=2 := by decide +kernel

theorem input : Observed.input (MainHeaderStreamPlan.logs plan 0 2++UartTxLoop.reads slots)=[13#8,10#8] := by
  rw [Observed.input_append,UartTxLoop.no_input,List.append_nil]
  decide +kernel

/-- Nonvacuous reset-to-actual-malformed-request, full actual HTTP400 close
    response and next poll. Committed state/borrow/invariant are unchanged. -/
theorem execution :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 2++UartTxLoop.reads slots)
      (UartTxLoop.events (ResponseHeadSpec.bytes 400 [] 0 true)) ∧
      LoopReady.At d after Spec.initial 0 ∧ AppState.At after Spec.initial ∧ ramRead after 0x80ffebbc#32 .w=0#32 := by
  obtain ⟨a,mid,reset,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  obtain ⟨d,n,after,_,cycle,next⟩ := RejectHeaderCycle.contract ready wire 2 400 plan (by decide) valid rejects slots (List.length_replicate)
  rw [received] at cycle
  exact ⟨2550+n,d,after,by simpa only [List.nil_append] using reset.observed.trans cycle,next,next.receive.stable.app,next.receive.stable.app.available⟩
end E5R.Thermostat.RejectHeaderWitness
