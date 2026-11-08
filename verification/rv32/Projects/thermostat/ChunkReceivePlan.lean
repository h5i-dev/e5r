import Projects.thermostat.MainChunkRefill
namespace E5R.Thermostat.ChunkReceivePlan
open E5R E5R.Thermostat

/-- A finite logical device-read schedule. It supplies neither physical
    timing nor a fairness guarantee for the original arbitrary-device model. -/
structure Plan where
  pending : Nat → List Word
  ready : Nat → Word
  datum : Nat → Word

def byte (p : Plan) (k : Nat) : BitVec 8 := (UartPoll.byte (p.datum k)).setWidth 8

def Valid (p : Plan) (wire : Nat → BitVec 8) (first count : Nat) : Prop :=
  ∀ k, first≤k → k<first+count →
    (∀ status ∈ p.pending k, MainChunkPoll.mask status=0#32) ∧
    MainChunkPoll.mask (p.ready k)≠0#32 ∧ byte p k=wire k

def logs (p : Plan) : Nat → Nat → List Observed.Read
  | _,0 => []
  | first,n+1 => MainChunkRefill.reads (p.pending first) (p.ready first) (p.datum first)++logs p (first+1) n

def cost (p : Plan) : Nat → Nat → Nat
  | _,0 => 0
  | first,n+1 => (25+5*(p.pending first).length)+cost p (first+1) n

theorem valid_tail {p wire first count} (h : Valid p wire first (count+1)) :
    Valid p wire (first+1) count := by
  intro k hk he
  exact h k (by omega) (by omega)

theorem lsr_input (statuses : List Word) : Observed.input (MainChunkWait.reads statuses)=[] := by
  induction statuses with
  | nil => rfl
  | cons status statuses ih =>
    simpa only [MainChunkWait.reads,List.map_cons,Observed.input,List.filterMap_cons,
      show ¬(0x10000005#32=0x10000000#32 ∧ Width.b.bytes=1) by decide +kernel,ite_false] using ih

theorem refill_input (pending : List Word) (ready datum : Word) :
    Observed.input (MainChunkRefill.reads pending ready datum)=[(UartPoll.byte datum).setWidth 8] := by
  rw [MainChunkRefill.reads,Observed.input_append,lsr_input]
  rfl

theorem logs_input (p : Plan) (first count : Nat) :
    Observed.input (logs p first count)=(List.range count).map (fun i => byte p (first+i)) := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [logs,Observed.input_append,refill_input,ih]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def,List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [show first+(i+1)=first+1+i by omega]
end E5R.Thermostat.ChunkReceivePlan
