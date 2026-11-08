import Projects.thermostat.MainHeaderResetStream
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
namespace E5R.Thermostat.MainHeaderResetWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

def input (kind : Fin 4) : List (BitVec 8) :=
  if kind=0 then [71,69,84,32,47,32,72,84,84,80,47,49,46,48,13,10,13,10]
  else if kind=1 then [71,69,84,32,47,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,13,10]
  else if kind=2 then [71,69,84,32,47,32,72,84,84,80,47,49,46,49,13,10,13,10]
  else [71,69,84,32,47,32,72,84,84,80,47,49,46,49,10]

def expected (kind : Fin 4) : HeadR :=
  if kind=0 then .done ⟨(0,3),(4,5),0,[],18,.empty⟩
  else if kind=1 then .done ⟨(0,3),(4,5),1,[⟨16,20,21,22⟩],26,.empty⟩
  else .reject 400

def wire (kind : Fin 4) (k : Nat) := (input kind)[k]?.getD 0#8

def plan (kind : Fin 4) : MainHeaderStreamPlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire kind k).toNat⟩

theorem valid (kind : Fin 4) : MainHeaderStreamPlan.Valid (plan kind) (wire kind) 0 (input kind).length := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire kind k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

theorem consumed : ∀ kind : Fin 4, consume (wire kind) (input kind).length []=⟨(input kind).length,input kind,expected kind⟩ := by
  decide +kernel

theorem length_bound : ∀ kind : Fin 4, (input kind).length≤26 := by decide +kernel

/-- Four complete reset-to-main header executions, with two not-ready polls
    per byte, a nontrivial ready status and explicit expected successful/refused
    objects. This still ends before response emission or command execution. -/
theorem execution (kind : Fin 4) : ∃ n d after reads, n≤60000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=input kind ∧ MainHeaderLoopStep.Boundary d after (input kind) Spec.initial (expected kind) := by
  obtain ⟨n,d,after,limit,trace,boundary,bytes,result⟩ := MainHeaderResetStream.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (input kind).length
    rfl (Or.inr rfl) rfl Blocking.stack_available (by have := length_bound kind;omega) (valid kind)
  rw [consumed kind] at trace boundary bytes
  refine ⟨n,d,after,MainHeaderStreamPlan.logs (plan kind) 0 (input kind).length,?_,trace,bytes,boundary⟩
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
end E5R.Thermostat.MainHeaderResetWitness
