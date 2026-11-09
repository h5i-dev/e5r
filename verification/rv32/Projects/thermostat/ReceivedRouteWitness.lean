import Projects.thermostat.ReceivedRouteRequest
import Projects.thermostat.MainInitWitness
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.Blocking
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedRouteWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
inductive Case where | empty | chunked deriving DecidableEq

def headBytes : Case → List (BitVec 8)
  | .empty => WireSpec.ascii "GET /state HTTP/1.0\r\nHost: x\r\n\r\n"
  | .chunked => WireSpec.ascii "POST /temp HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n"
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

/-- Satisfying actual reset-to-router runs for both new receive paths:
    HTTP/1.0 Empty and an HTTP/1.1 dechunked temperature body. -/
theorem execution (which : Case) :
    ∃ n d after reads raw lowValue close,
      Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      RuntimeRouterEntry.At d after raw Spec.initial (head which) (amount which) (used which) 1 lowValue close ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 (used which)) ∧
      raw.take (head which).len=headBytes which ∧
      RuntimeRequestSpans.body raw (head which) (amount which)=(if which=.chunked then WireSpec.ascii "-1" else []) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  cases which with
  | empty =>
    obtain ⟨n,d,after,lowValue,close,receive,entry,metadata,_⟩ := ReceivedRouteRequest.empty ready (wire .empty) (headBytes .empty).length
      (head .empty) (plan .empty) (by decide +kernel) (valid _ _ _) (by rw [header]) (by decide +kernel)
    rw [header] at entry
    refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan .empty) 0 (headBytes .empty).length,headBytes .empty,lowValue,close,?_,?_,?_,?_,?_⟩
    · simpa only [header,List.nil_append] using boot.observed.trans receive
    · simpa only [used,body,amount,List.length_nil,Nat.add_zero] using entry
    · simpa only [used,body,List.length_nil,Nat.add_zero] using metadata
    · have len : (head .empty).len=(headBytes .empty).length := by decide +kernel
      rw [len,List.take_length]
    · simp only [amount,RuntimeRequestSpans.body,List.take_zero,reduceCtorEq,ite_false]
  | chunked =>
    obtain ⟨received,n,d,after,raw,lowValue,close,_,_,len,receive,entry,headerEq,payload,metadata,_⟩ :=
      ReceivedRouteRequest.chunked ready (wire .chunked) (headBytes .chunked).length (body .chunked).length (head .chunked) (plan .chunked) (plan .chunked)
        (by decide +kernel) (valid _ _ _) (by rw [header]) (by decide +kernel) (by decide +kernel) (valid _ _ _)
        (by rw [chunk_result])
    rw [chunk_result] at len entry payload metadata
    have bodyLength : (WireSpec.ascii "-1").length=2 := by decide +kernel
    rw [bodyLength] at entry payload
    refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan .chunked) 0 (headBytes .chunked).length++ChunkReceivePlan.logs (plan .chunked) (head .chunked).len received,raw,lowValue,close,?_,?_,metadata,?_,?_⟩
    · simpa only [header,List.nil_append] using boot.observed.trans receive
    · simpa only [amount,Nat.zero_add] using entry
    · rw [header] at headerEq
      exact headerEq
    · simpa only [amount,reduceCtorEq,ite_true] using payload
end E5R.Thermostat.ReceivedRouteWitness
