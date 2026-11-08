import Projects.thermostat.MainLengthReset
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainLengthWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

def header (kind : Fin 3) : List (BitVec 8) :=
  if kind=0 then [80,79,83,84,32,47,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=1 then [80,79,83,84,32,47,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,51,13,10,13,10]
  else [80,79,83,84,32,47,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,49,48,50,52,13,10,13,10]

def amount (kind : Fin 3) : Nat := if kind=0 then 0 else if kind=1 then 3 else 1024

def expected (kind : Fin 3) : Head :=
  if kind=0 then ⟨(0,4),(5,6),0,[⟨17,31,32,33⟩],37,.length 0⟩
  else if kind=1 then ⟨(0,4),(5,6),0,[⟨17,31,32,33⟩],37,.length 3⟩
  else ⟨(0,4),(5,6),0,[⟨17,31,32,36⟩],40,.length 1024⟩

def body (kind : Fin 3) : List (BitVec 8) := (List.range (amount kind)).map (fun i => BitVec.ofNat 8 (97+i%26))

def wire (kind : Fin 3) (k : Nat) : BitVec 8 :=
  if k<(header kind).length then (header kind)[k]?.getD 0#8 else BitVec.ofNat 8 (97+(k-(header kind).length)%26)

def plan (kind : Fin 3) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire kind k).toNat⟩

theorem valid (kind : Fin 3) (first count : Nat) : ChunkReceivePlan.Valid (plan kind) (wire kind) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire kind k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

theorem consumed : ∀ kind : Fin 3, consume (wire kind) (header kind).length []=⟨(header kind).length,header kind,.done (expected kind)⟩ := by
  decide +kernel

theorem facts : ∀ kind : Fin 3, (header kind).length≤40 ∧ (expected kind).len=(header kind).length ∧
    (expected kind).framing=.length (amount kind) ∧ amount kind≤1024 := by decide +kernel

theorem body_arrivals (kind : Fin 3) : arrivals (wire kind) (header kind).length (amount kind)=body kind := by
  unfold arrivals body
  apply List.map_congr_left
  intro i hi
  simp only [wire,show ¬(header kind).length+i<(header kind).length by omega,ite_false,Nat.add_sub_cancel_left]

/-- Three actual reset-to-complete-fixed-body executions: zero, three and
    maximum1024 bytes. The nonconstant alphabet pattern is stored exactly;
    committed App state and every parsed Head field remain valid. -/
theorem execution (kind : Fin 3) : ∃ n d after reads, n≤150000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind++body kind ∧ d.pc=0x80000c98#32 ∧
      MainLengthState.At d after (header kind++body kind) Spec.initial (expected kind) (amount kind) := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,limit,trace,pc,state,bytes⟩ := MainLengthReset.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) (amount kind) (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+amount kind-(header kind).length=amount kind := by rw [fs.2.1];omega
  rw [missing] at trace
  rw [missing,body_arrivals] at state bytes
  refine ⟨n,d,after,_,?_,trace,bytes,pc,state⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  have bc (first count : Nat) : MainLengthStreamPlan.cost (plan kind) first count=33*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainLengthStreamPlan.cost,ih,Nat.mul_succ];change (25+4*2)+_= _;omega
  rw [hc,bc,missing] at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainLengthWitness
