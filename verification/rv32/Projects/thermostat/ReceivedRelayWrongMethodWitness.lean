import Projects.thermostat.ReceivedRelayWrongMethodCycle
import Projects.thermostat.ReadSendWitness
import Projects.thermostat.MainInitWitness
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.Blocking
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedRelayWrongMethodWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
inductive Case where | empty | chunked deriving DecidableEq

def headBytes : Case → List (BitVec 8)
  | .empty => WireSpec.ascii "GET /relay/3 HTTP/1.0\r\nHost: x\r\n\r\n"
  | .chunked => WireSpec.ascii "GET /relay/3 HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n"
def body : Case → List (BitVec 8)
  | .empty => []
  | .chunked => WireSpec.ascii "2\r\n-1\r\n0\r\n\r\n"
def amount : Case → Nat | .empty => 0 | .chunked => 2
def head (which : Case) : Head := match HttpRequestBytes.parse (headBytes which) 1024 1024 with
  | .done h => h | _ => ⟨(0,0),(0,0),0,[],0,.empty⟩
def wire (which : Case) (k : Nat) := (headBytes which++body which)[k]?.getD 0#8
def plan (which : Case) : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire which k).toNat⟩
def used (which : Case) := (head which).len+(body which).length

theorem valid (which : Case) (first count : Nat) : ChunkReceivePlan.Valid (plan which) (wire which) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire which k)⟩
  intro status member;cases member

theorem header (which : Case) : consume (wire which) (headBytes which).length []=⟨(headBytes which).length,headBytes which,.done (head which)⟩ := by
  cases which <;> decide +kernel

theorem chunk_result :
    ChunkBufferSpec.consume (wire .chunked) (body .chunked).length (head .chunked).len (head .chunked).len cStart []=
      ⟨used .chunked,(head .chunked).len+2,⟨7,0,0,2⟩,WireSpec.ascii "-1",.done⟩ := by decide +kernel

def slots (close : Bool) : List UartTxLoop.Slot := List.replicate (ResponseHeadSpec.bytes 405 [] 0 close).length
  ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩

/-- Satisfying reset/receive/parse/actual relay capture/wrong-method405/nextRX
    runs for both Empty and Chunked requests, including body compaction. -/
theorem execution (which : Case) :
    ∃ n d after reads close,
      Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
        (UartTxLoop.events (ResponseHeadSpec.bytes 405 [] 0 close)) ∧
      LoopReady.At d after Spec.initial (if close then 0 else 1) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  cases which with
  | empty =>
    obtain ⟨n,d,after,close,receive,_,final⟩ := ReceivedRelayWrongMethodCycle.empty ready (wire .empty) (headBytes .empty).length (head .empty) (plan .empty)
      (by decide +kernel) (valid _ _ _) (by rw [header]) (by decide +kernel)
      (by rw [header];decide +kernel) (by rw [header];decide +kernel)
      slots (fun _ => List.length_replicate)
    refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan .empty) 0 (headBytes .empty).length++UartTxLoop.reads (slots close),close,?_,final⟩
    simpa only [header,List.nil_append] using boot.observed.trans receive
  | chunked =>
    obtain ⟨received,n,d,after,raw,close,_,_,_,receive,_,_,_,final⟩ := ReceivedRelayWrongMethodCycle.chunked ready (wire .chunked) (headBytes .chunked).length (body .chunked).length
      (head .chunked) (plan .chunked) (plan .chunked) (by decide +kernel) (valid _ _ _) (by rw [header]) (by decide +kernel)
      (by decide +kernel) (valid _ _ _) (by rw [chunk_result])
      (by rw [header];decide +kernel) (by rw [header];decide +kernel)
      slots (fun _ => List.length_replicate)
    refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan .chunked) 0 (headBytes .chunked).length++ChunkReceivePlan.logs (plan .chunked) (head .chunked).len received++UartTxLoop.reads (slots close),close,?_,final⟩
    simpa only [header,List.nil_append] using boot.observed.trans receive
end E5R.Thermostat.ReceivedRelayWrongMethodWitness
