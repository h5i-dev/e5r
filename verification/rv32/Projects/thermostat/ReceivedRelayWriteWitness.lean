import Projects.thermostat.ReceivedRelayWriteCycle
import Projects.thermostat.RuntimeLastMatchWitness
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedRelayWriteWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
open RuntimeLastMatchWitness

def slots (close : Bool) : List UartTxLoop.Slot := List.replicate (ResponseHeadSpec.bytes 401 [] 0 close).length
  ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩

/-- The new real relay capture/setup/auth path has a concrete reset witness;
    missing credentials refuse401 before empty-body decoding and preserve App. -/
theorem execution :
    ∃ n d after reads close,Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
      (UartTxLoop.events (ResponseHeadSpec.bytes 401 [] 0 close)) ∧ LoopReady.At d after Spec.initial (if close then 0 else 1) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  have reply : ReceivedRelayWriteCycle.reply Spec.initial ((headBytes .valid).take (head .valid).len) [] (head .valid)=⟨Spec.initial,401,[],[]⟩  := by
    have denied : AuthSpec.authorized (HeaderSpec.lookup ((headBytes .valid).take (head .valid).len) (WireSpec.ascii "authorization") (RuntimeRequestInputs.entries (head .valid))) (WireSpec.ascii "dev-key")=false := by decide +kernel
    simp only [ReceivedRelayWriteCycle.reply,ApiWriteHttpSpec.run,denied,Bool.false_eq_true,ite_false]
  obtain ⟨n,d,after,close,receive,closeSpec,final⟩ := ReceivedRelayWriteCycle.empty ready (wire .valid) (headBytes .valid).length (head .valid) (plan .valid)
    (by decide +kernel) (valid _ _ _) (by rw [consumed]) (by decide +kernel)
    (by rw [consumed];decide +kernel) (by rw [consumed];decide +kernel) slots []
    (fun close => by rw [consumed,reply];exact List.length_replicate ..) (by rw [consumed,reply];rfl)
  refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan .valid) 0 (headBytes .valid).length++UartTxLoop.reads (slots close),close,?_,?_⟩
  · simpa only [consumed,reply,UartTxLoop.events,List.map_nil,List.append_nil,UartTxLoop.reads,List.flatMap_nil,List.nil_append,List.length_nil] using boot.observed.trans receive
  · simpa only [consumed,reply,Nat.zero_add] using final
end E5R.Thermostat.ReceivedRelayWriteWitness
