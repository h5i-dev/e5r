import Projects.thermostat.MainRequestQueryReset
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainRequestQueryWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
def header (kind : Fin 3) : List (BitVec 8) :=
  if kind=0 then [80,79,83,84,32,47,63,97,63,98,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=1 then [80,79,83,84,32,47,97,63,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else [80,79,83,84,32,47,112,108,97,105,110,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
def expected (kind : Fin 3) : Head :=
  if kind=0 then ⟨(0,4),(5,10),0,[⟨21,35,36,37⟩],41,.length 0⟩
  else if kind=1 then ⟨(0,4),(5,8),0,[⟨19,33,34,35⟩],39,.length 0⟩
  else ⟨(0,4),(5,11),0,[⟨22,36,37,38⟩],42,.length 0⟩
def wire (kind : Fin 3) (k : Nat) : BitVec 8 := (header kind)[k]?.getD 0#8

def plan (kind : Fin 3) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire kind k).toNat⟩

theorem valid (kind : Fin 3) (first count : Nat) : ChunkReceivePlan.Valid (plan kind) (wire kind) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire kind k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

theorem consumed : ∀ kind : Fin 3, consume (wire kind) (header kind).length []=⟨(header kind).length,header kind,.done (expected kind)⟩ := by decide +kernel

theorem facts : ∀ kind : Fin 3, (header kind).length≤45 ∧ (expected kind).len=(header kind).length ∧ (expected kind).framing=.length 0 ∧
    MainQuerySpec.pathLength (MainQuerySpec.bytes (header kind)) (expected kind).target.1 (expected kind).target.2=(if kind=0 then 1 else if kind=1 then 2 else 6) ∧
    MainQuerySpec.queryLength (MainQuerySpec.bytes (header kind)) (expected kind).target.1 (expected kind).target.2=(if kind=0 then 3 else 0) ∧
    MainQuerySpec.queryStart (MainQuerySpec.bytes (header kind)) (expected kind).target.1 (expected kind).target.2=(if kind=0 then 7 else if kind=1 then 8 else 5) := by decide +kernel

/-- Actual reset witnesses: first of two question marks, trailing question mark,
    and no question mark. They include real UART polling and unchanged App state. -/
theorem execution (kind : Fin 3) : ∃ n d after reads, n≤151000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind ∧ MainRequestQuery.Ready d after (header kind) Spec.initial (expected kind) 0 1 ∧
      d.get 28=BitVec.ofNat 32 (if kind=0 then 1 else if kind=1 then 2 else 6) ∧
      d.get 13=BitVec.ofNat 32 (if kind=0 then 3 else 0) ∧
      d.get 12=MainRequestQuery.rx+BitVec.ofNat 32 (if kind=0 then 7 else if kind=1 then 8 else 5) := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,limit,trace,state,bytes⟩ := MainRequestQueryReset.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) 0 (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+0-(header kind).length=0 := by rw [fs.2.1];omega
  rw [missing] at limit trace state bytes
  simp only [arrivals,List.range_zero,List.map_nil,List.append_nil] at state bytes
  have path := state.pathLength
  have query := state.queryLength
  have ptr := state.queryPtr
  rw [fs.2.2.2.1] at path
  rw [fs.2.2.2.2.1] at query
  rw [fs.2.2.2.2.2] at ptr
  refine ⟨n,d,after,_,?_,trace,bytes,state,path,query,ptr⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  rw [hc] at limit
  have target : (expected kind).target.2-(expected kind).target.1≤6 := by
    have all : ∀ k : Fin 3, (expected k).target.2-(expected k).target.1≤6 := by decide +kernel
    exact all kind
  change n≤4175+5*((expected kind).target.2-(expected kind).target.1)+(47+8+HeadColdFutureComplete.budget 1024)*(header kind).length+0 at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainRequestQueryWitness
