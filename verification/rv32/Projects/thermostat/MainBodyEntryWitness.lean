import Projects.thermostat.MainHeaderResetBody
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainBodyEntryWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

def input (kind : Fin 3) : List (BitVec 8) :=
  if kind=0 then [71,69,84,32,47,32,72,84,84,80,47,49,46,48,13,10,13,10]
  else if kind=1 then [80,79,83,84,32,47,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,51,13,10,13,10]
  else [80,79,83,84,32,47,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,84,114,97,110,115,102,101,114,45,69,110,99,111,100,105,110,103,58,99,104,117,110,107,101,100,13,10,13,10]

def expected (kind : Fin 3) : Head :=
  if kind=0 then ⟨(0,3),(4,5),0,[],18,.empty⟩
  else if kind=1 then ⟨(0,4),(5,6),0,[⟨17,31,32,33⟩],37,.length 3⟩
  else ⟨(0,4),(5,6),1,[⟨17,21,22,23⟩,⟨25,42,43,50⟩],54,.chunked⟩

def wire (kind : Fin 3) (k : Nat) := (input kind)[k]?.getD 0#8

def plan (kind : Fin 3) : MainHeaderStreamPlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire kind k).toNat⟩

theorem valid (kind : Fin 3) : MainHeaderStreamPlan.Valid (plan kind) (wire kind) 0 (input kind).length := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire kind k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

theorem consumed : ∀ kind : Fin 3, consume (wire kind) (input kind).length []=⟨(input kind).length,input kind,.done (expected kind)⟩ := by
  decide +kernel

theorem length_bound : ∀ kind : Fin 3, (input kind).length≤54 := by decide +kernel

/-- Three satisfiable complete reset executions reach the distinct empty,
    fixed-length and chunked body entries, with every copied Head field checked.
    Two failed polls precede each byte; the App remains initially valid. -/
theorem execution (kind : Fin 3) : ∃ n d after reads, n≤150000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=input kind ∧ MainHeaderToBody.Ready d after (input kind) Spec.initial (expected kind) := by
  have accepted : (consume (wire kind) (input kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,limit,trace,ready,bytes⟩ := MainHeaderResetBody.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (input kind).length (expected kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by have := length_bound kind;omega) (valid kind) accepted
  rw [consumed kind] at trace ready bytes
  refine ⟨n,d,after,MainHeaderStreamPlan.logs (plan kind) 0 (input kind).length,?_,trace,bytes,ready⟩
  have length := length_bound kind
  have cost : MainHeaderStreamPlan.cost (plan kind) 0 (input kind).length≤(47+8+HeadColdFutureComplete.budget 1024)*(input kind).length := by
    have general (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
      induction count generalizing first with
      | zero => simp only [MainHeaderStreamPlan.cost,Nat.mul_zero]
      | succ count ih =>
        rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ]
        change (47+4*2+HeadColdFutureComplete.budget 1024)+(47+8+HeadColdFutureComplete.budget 1024)*count=_
        omega
    exact Nat.le_of_eq (general _ _)
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at cost
  omega
end E5R.Thermostat.MainBodyEntryWitness
