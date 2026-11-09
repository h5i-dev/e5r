import Projects.thermostat.ChunkCapacityCycle
import Projects.thermostat.ChunkRejectWitness
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ChunkCapacityWitness
open E5R E5R.Thermostat HttpRequestSpec

def byte (q : Nat) : BitVec 8 := match q%6 with | 0 => 49#8 | 1 => 13#8 | 2 => 10#8 | 3 => 97#8 | 4 => 13#8 | _ => 10#8

def wire (k : Nat) : BitVec 8 := if k<60 then ChunkRejectWitness.headBytes[k]?.getD 0#8 else byte (k-60)

def state (n : Nat) : CState := ⟨0,0,0,n⟩

theorem block (n i : Nat) : wire (60+6*n+i)=byte i := by
  rw [wire,ite_eq_right (by omega),show 60+6*n+i-60=6*n+i by omega]
  simp [byte,Nat.add_mod]

theorem one (n : Nat) (bound : n<1024) (body : List (BitVec 8)) :
    ChunkBufferSpec.consume wire 6 (60+6*n) (60+n) (state n) body=
      ⟨60+6*(n+1),60+n+1,state (n+1),body++[97#8],.needInput⟩ := by
  have w0 : wire (60+6*n)=49#8 := by simpa only [Nat.add_zero,byte] using block n 0
  have w1 : wire (60+6*n+1)=13#8 := block n 1
  have w2 : wire (60+6*n+2)=10#8 := block n 2
  have w3 : wire (60+6*n+3)=97#8 := block n 3
  have w4 : wire (60+6*n+4)=13#8 := block n 4
  have w5 : wire (60+6*n+5)=10#8 := block n 5
  simp only [Nat.add_assoc] at w1 w2 w3 w4 w5
  simp [ChunkBufferSpec.consume,chunkStep,sizeStep,expectStep,hexv,state,w0,w1,w2,w3,w4,w5,
    show ¬1024<n by omega,show ¬1024-n<1 by omega,Nat.add_assoc,Nat.mul_add]
theorem chunks (n : Nat) (bound : n≤1024) :
    ChunkBufferSpec.consume wire (6*n) 60 60 cStart []=
      ⟨60+6*n,60+n,state n,List.replicate n 97#8,.needInput⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1)=6*n+6 by omega,ChunkBufferConcat.consume_add,ih (by omega)]
    simp only [ite_true]
    rw [one n (by omega)]
    simp [List.replicate_succ',Nat.add_assoc,Nat.mul_add]

theorem incomplete : (ChunkBufferSpec.consume wire 1988 60 60 cStart []).stop=.needInput := by
  rw [show 1988=6*331+2 by decide,ChunkBufferConcat.consume_add,chunks 331 (by decide)]
  decide +kernel

theorem header : MainHeaderStreamSpec.consume wire 60 []=⟨60,ChunkRejectWitness.headBytes,.done ChunkRejectWitness.head⟩ := by
  have same := MainHeaderStreamSpec.consume_congr wire (ChunkRejectWitness.wire .digit) 60 [] (by
    intro k lo hi
    have inside : k<60 := by simpa only [List.length_nil,Nat.zero_add] using hi
    rw [wire,ite_eq_left inside,ChunkRejectWitness.wire,List.getElem?_append_left inside])
  exact same.trans ChunkRejectWitness.header_base

def plan : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire k).toNat⟩
def slots := List.replicate (ResponseHeadSpec.bytes 413 [] 0 true).length UartWriteWitness.slot1

theorem valid (first count : Nat) : ChunkReceivePlan.Valid plan wire first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire k)⟩
  intro status mem;cases mem

/-- A satisfying real reset execution receives60head bytes and1988encoded
    body bytes:331complete one-byte chunks and the next size/CR prefix. The
    actual full-buffer guard returns413 and restarts before any further RBR. -/
theorem execution :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
      (ChunkRejectCycle.reads plan plan slots wire 60 1988)
      (UartTxLoop.events (ResponseHeadSpec.bytes 413 [] 0 true)) ∧
      LoopReady.At d after Spec.initial 0 ∧ AppState.At after Spec.initial ∧ ramRead after 0x80ffebbc#32 .w=0#32 := by
  obtain ⟨a,mid,reset,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  have accepted : (MainHeaderStreamSpec.consume wire 60 []).result=.done ChunkRejectWitness.head := by rw [header]
  have full : (MainHeaderStreamSpec.consume wire 60 []).input.length+1988=2048 := by rw [header];decide +kernel
  have pending : (ChunkBufferSpec.consume wire ((MainHeaderStreamSpec.consume wire 60 []).input.length-ChunkRejectWitness.head.len+1988)
      ChunkRejectWitness.head.len ChunkRejectWitness.head.len cStart []).stop=.needInput := by
    rw [header,ChunkRejectWitness.head_length,show ChunkRejectWitness.headBytes.length=60 by decide +kernel,Nat.sub_self,Nat.zero_add]
    exact incomplete
  obtain ⟨d,n,after,cycle,_,next,app,borrow⟩ := ChunkCapacityCycle.contract ready wire 60 1988 ChunkRejectWitness.head plan plan
    (by decide) (valid _ _) accepted ChunkRejectWitness.framing full (valid _ _) pending slots (List.length_replicate)
  exact ⟨2550+n,d,after,by simpa only [List.nil_append] using reset.observed.trans cycle,next,app,borrow⟩
end E5R.Thermostat.ChunkCapacityWitness
