import Projects.thermostat.MainConsumeCongr
import Projects.thermostat.ChunkRejectCycle
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.UartWriteWitness
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ChunkRejectWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec

inductive Case where
  | digit | oversized | extension | trailer | afterData
  deriving DecidableEq

def headBytes := WireSpec.ascii "POST /temp HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n"
def head : Head := match HttpRequestBytes.parse headBytes 1024 1024 with
  | .done h => h
  | _ => ⟨(0,0),(0,0),0,[],0,.empty⟩
def body : Case → List (BitVec 8)
  | .digit => WireSpec.ascii "z"
  | .oversized => WireSpec.ascii "401\r\n"
  | .extension => WireSpec.ascii "1;x"
  | .trailer => WireSpec.ascii "0\r\nX"
  | .afterData => WireSpec.ascii "1\r\na\r\nz"
def status : Case → Nat | .oversized => 413 | _ => 400
def received : Case → Nat | .digit => 1 | .oversized => 4 | .extension => 2 | .trailer => 4 | .afterData => 7

def wire (which : Case) (k : Nat) : BitVec 8 := (headBytes++body which)[k]?.getD 0#8
def plan (which : Case) : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire which k).toNat⟩
def slots (which : Case) := List.replicate (ResponseHeadSpec.bytes (status which) [] 0 true).length UartWriteWitness.slot1

theorem valid (which : Case) (first count : Nat) : ChunkReceivePlan.Valid (plan which) (wire which) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire which k)⟩
  intro status mem;cases mem

theorem header_base : consume (wire .digit) headBytes.length []=⟨headBytes.length,headBytes,.done head⟩ := by decide +kernel

theorem header (which : Case) : consume (wire which) headBytes.length []=⟨headBytes.length,headBytes,.done head⟩ := by
  have same := MainHeaderStreamSpec.consume_congr (wire which) (wire .digit) headBytes.length [] (by
    intro k lo hi
    have inside : k<headBytes.length := by simpa only [List.length_nil,Nat.zero_add] using hi
    have firstBytes (which : Case) : wire which k=headBytes[k]'inside := by
      have bound : k<(headBytes++body which).length := by rw [List.length_append];omega
      rw [wire,List.getElem?_eq_getElem bound,Option.getD_some,List.getElem_append_left inside]
    exact (firstBytes which).trans (firstBytes .digit).symm)
  exact same.trans header_base

theorem head_length : head.len=headBytes.length := by decide +kernel

theorem framing : head.framing=.chunked := by decide +kernel

theorem rejects (which : Case) :
    (ChunkBufferSpec.consume (wire which) (body which).length head.len head.len cStart []).stop=.reject (status which) := by
  cases which <;> decide +kernel

theorem body_count (which : Case) :
    (ChunkBufferSpec.consume (wire which) (body which).length head.len head.len cStart []).read-head.len=received which := by
  cases which <;> decide +kernel

/-- Real reset/receive/chunk reject/send/restart for five pure malformed-body
    classes, including rejection after in-place compaction and a raw LF that
    remains unread when the preceding CR already selects413. -/
theorem execution (which : Case) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
      (ChunkRejectCycle.reads (plan which) (plan which) (slots which) (wire which) headBytes.length (received which))
      (UartTxLoop.events (ResponseHeadSpec.bytes (status which) [] 0 true)) ∧
      LoopReady.At d after Spec.initial 0 ∧ AppState.At after Spec.initial ∧ ramRead after 0x80ffebbc#32 .w=0#32 := by
  obtain ⟨a,mid,reset,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  have accepted : (consume (wire which) headBytes.length []).result=.done head := by rw [header]
  have space : (consume (wire which) headBytes.length []).input.length+(body which).length≤2048 := by rw [header];cases which <;> decide +kernel
  have reject : (ChunkBufferSpec.consume (wire which) ((consume (wire which) headBytes.length []).input.length-head.len+(body which).length) head.len head.len cStart []).stop=.reject (status which) := by
    rw [header,head_length,Nat.sub_self,Nat.zero_add];simpa only [head_length] using rejects which
  obtain ⟨count,d,n,after,_,exactCount,cycle,_,next,app,borrow⟩ := ChunkRejectCycle.contract ready (wire which) headBytes.length (body which).length
    (status which) head (plan which) (plan which) (by decide +kernel) (valid which _ _) accepted framing space (valid which _ _) reject (slots which) (List.length_replicate)
  have countEq : count=received which := by
    have bound : (consume (wire which) headBytes.length []).input.length≤head.len+1 := by rw [header,head_length];dsimp only;omega
    have exact := exactCount bound
    rw [header,←head_length,Nat.sub_self,Nat.zero_add,body_count] at exact
    exact exact
  rw [countEq] at cycle
  exact ⟨2550+n,d,after,by simpa only [List.nil_append] using reset.observed.trans cycle,next,app,borrow⟩
end E5R.Thermostat.ChunkRejectWitness
