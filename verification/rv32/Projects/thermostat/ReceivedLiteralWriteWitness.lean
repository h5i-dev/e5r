import Projects.thermostat.ReceivedLiteralWriteHeaderCerts
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedLiteralWriteWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
theorem valid (which : Case) (first count : Nat) : ChunkReceivePlan.Valid (plan which) (wire which) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire which k)⟩
  intro status member;cases member

theorem header (which : Case) : consume (wire which) (headBytes which).length []=⟨(headBytes which).length,headBytes which,.done (head which)⟩ := by
  cases which with
  | setpoint => exact header_setpoint
  | temp => exact header_temp
  | mode => exact header_mode
  | range => exact header_range
  | noAuth => exact header_noAuth
  | malformed => exact header_malformed

theorem chunks (which : Case) :
    (ChunkBufferSpec.consume (wire which) (encoded which).length (head which).len (head which).len cStart []).body=body which ∧
    (ChunkBufferSpec.consume (wire which) (encoded which).length (head which).len (head which).len cStart []).stop=.done := by
  cases which <;> decide +kernel

/-- Concrete reset/UART witnesses exercise all3 literal writes, successful
    commits, kernel422, auth401 and malformed400 under chunked framing. -/
theorem execution (which : Case) :
    ∃ n d after reads close,Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
      (UartTxLoop.events (ResponseHeadSpec.bytes (response which).status (response which).mime (response which).payload.length close)++UartTxLoop.events (response which).payload) ∧
      LoopReady.At d after (response which).state (if close then 0 else 1) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  obtain ⟨received,n,d,after,raw,close,_,_,_,receive,_,_,_,final⟩ := ReceivedLiteralWriteCycle.chunked ready
    (wire which) (headBytes which).length (encoded which).length (head which) (plan which) (plan which)
    (by cases which <;> decide +kernel) (valid _ _ _) (by rw [header]) (by cases which <;> decide +kernel)
    (by cases which <;> decide +kernel) (valid _ _ _) (chunks which).2 (kind which)
    (by cases which <;> decide +kernel) (by rw [header];cases which <;> decide +kernel)
    (by rw [header];cases which <;> decide +kernel) (hs which) (bs which)
    (fun close => by rw [header,(chunks which).1];exact List.length_replicate ..) (by rw [header,(chunks which).1];exact List.length_replicate ..)
  refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan which) 0 (headBytes which).length++ChunkReceivePlan.logs (plan which) (head which).len received++UartTxLoop.reads (hs which close)++UartTxLoop.reads (bs which),close,?_,?_⟩
  · simpa only [header,(chunks which).1,response,List.nil_append] using boot.observed.trans receive
  · simpa only [header,(chunks which).1,response,Nat.zero_add] using final
end E5R.Thermostat.ReceivedLiteralWriteWitness
