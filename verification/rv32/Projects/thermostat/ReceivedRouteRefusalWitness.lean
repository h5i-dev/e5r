import Projects.thermostat.ReceivedRouteRefusalCycle
import Projects.thermostat.ReadSendWitness
import Projects.thermostat.MainInitWitness
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.Blocking
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedRouteRefusalWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
inductive Case where | empty | chunked deriving DecidableEq

def headBytes (wrong : Bool) : Case → List (BitVec 8)
  | .empty => if wrong then WireSpec.ascii "POST /state HTTP/1.0\r\nHost: x\r\n\r\n" else WireSpec.ascii "PUT /relay/3/x HTTP/1.0\r\nHost: x\r\n\r\n"
  | .chunked => if wrong then WireSpec.ascii "POST /state HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n" else WireSpec.ascii "PUT /relay/3/x HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n"
def body : Case → List (BitVec 8)
  | .empty => []
  | .chunked => WireSpec.ascii "2\r\n-1\r\n0\r\n\r\n"
def amount : Case → Nat | .empty => 0 | .chunked => 2
def head (wrong : Bool) (which : Case) : Head := match HttpRequestBytes.parse (headBytes wrong which) 1024 1024 with
  | .done h => h | _ => ⟨(0,0),(0,0),0,[],0,.empty⟩
def wire (wrong : Bool) (which : Case) (k : Nat) := (headBytes wrong which++body which)[k]?.getD 0#8
def plan (wrong : Bool) (which : Case) : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire wrong which k).toNat⟩
def used (wrong : Bool) (which : Case) := (head wrong which).len+(body which).length

theorem valid (wrong : Bool) (which : Case) (first count : Nat) : ChunkReceivePlan.Valid (plan wrong which) (wire wrong which) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire wrong which k)⟩
  intro status member;cases member

theorem header (wrong : Bool) (which : Case) : consume (wire wrong which) (headBytes wrong which).length []=⟨(headBytes wrong which).length,headBytes wrong which,.done (head wrong which)⟩ := by
  cases which <;> cases wrong <;> decide +kernel

theorem chunk_result (wrong : Bool) :
    ChunkBufferSpec.consume (wire wrong .chunked) (body .chunked).length (head wrong .chunked).len (head wrong .chunked).len cStart []=
      ⟨used wrong .chunked,(head wrong .chunked).len+2,⟨7,0,0,2⟩,WireSpec.ascii "-1",.done⟩ := by cases wrong <;> decide +kernel

def code (wrong : Bool) : Nat := if wrong then 405 else 404
def slots (wrong close : Bool) : List UartTxLoop.Slot := List.replicate (ResponseHeadSpec.bytes (code wrong) [] 0 close).length ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩

theorem status (wrong : Bool) (which : Case) : RouteRefusalSpec.status (RuntimeRequestSpans.path (headBytes wrong which) (head wrong which))=code wrong := by
  cases which <;> cases wrong <;> decide +kernel

/-- Satisfying unchanged-ELF reset/receive/parse/all5routes/404or405/nextRX
    runs for both Empty and Chunked requests, including body compaction. -/
theorem execution (wrong : Bool) (which : Case) :
    ∃ n d after reads close,
      Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
        (UartTxLoop.events (ResponseHeadSpec.bytes (code wrong) [] 0 close)) ∧
      LoopReady.At d after Spec.initial (if close then 0 else 1) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  cases which with
  | empty =>
    obtain ⟨n,d,after,close,receive,_,final⟩ := ReceivedRouteRefusalCycle.empty ready (wire wrong .empty) (headBytes wrong .empty).length (head wrong .empty) (plan wrong .empty)
      (by cases wrong <;> decide +kernel) (valid _ _ _ _) (by rw [header]) (by cases wrong <;> decide +kernel)
      (by intro kind;rw [header];cases wrong <;> cases kind <;> decide +kernel) (by rw [header];cases wrong <;> decide +kernel)
      (slots wrong) (fun close => by rw [header,status];exact List.length_replicate ..)
    refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan wrong .empty) 0 (headBytes wrong .empty).length++UartTxLoop.reads (slots wrong close),close,?_,final⟩
    simpa only [header,status,List.nil_append] using boot.observed.trans receive
  | chunked =>
    obtain ⟨received,n,d,after,raw,close,_,_,_,receive,_,_,_,final⟩ := ReceivedRouteRefusalCycle.chunked ready (wire wrong .chunked) (headBytes wrong .chunked).length (body .chunked).length
      (head wrong .chunked) (plan wrong .chunked) (plan wrong .chunked) (by cases wrong <;> decide +kernel) (valid _ _ _ _) (by rw [header]) (by cases wrong <;> decide +kernel)
      (by cases wrong <;> decide +kernel) (valid _ _ _ _) (by rw [chunk_result])
      (by intro kind;rw [header];cases wrong <;> cases kind <;> decide +kernel) (by rw [header];cases wrong <;> decide +kernel)
      (slots wrong) (fun close => by rw [header,status];exact List.length_replicate ..)
    refine ⟨2550+n,d,after,MainHeaderStreamPlan.logs (plan wrong .chunked) 0 (headBytes wrong .chunked).length++ChunkReceivePlan.logs (plan wrong .chunked) (head wrong .chunked).len received++UartTxLoop.reads (slots wrong close),close,?_,final⟩
    simpa only [header,status,List.nil_append] using boot.observed.trans receive
end E5R.Thermostat.ReceivedRouteRefusalWitness
