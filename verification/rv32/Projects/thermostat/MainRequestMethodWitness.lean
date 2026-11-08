import Projects.thermostat.MainRequestMethodReset
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainRequestMethodWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
def header (kind : Fin 8) : List (BitVec 8) :=
  if kind=0 then [71,69,84,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=1 then [72,69,65,68,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=2 then [80,79,83,84,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=3 then [80,85,84,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=4 then [80,65,84,67,72,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=5 then [68,69,76,69,84,69,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=6 then [103,101,116,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else [68,69,76,69,84,101,32,47,63,113,32,72,84,84,80,47,49,46,48,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
def expected (kind : Fin 8) : Head :=
  if kind=0 then ⟨(0,3),(4,7),0,[⟨18,32,33,34⟩],38,.length 0⟩
  else if kind=1 then ⟨(0,4),(5,8),0,[⟨19,33,34,35⟩],39,.length 0⟩
  else if kind=2 then ⟨(0,4),(5,8),0,[⟨19,33,34,35⟩],39,.length 0⟩
  else if kind=3 then ⟨(0,3),(4,7),0,[⟨18,32,33,34⟩],38,.length 0⟩
  else if kind=4 then ⟨(0,5),(6,9),0,[⟨20,34,35,36⟩],40,.length 0⟩
  else if kind=5 then ⟨(0,6),(7,10),0,[⟨21,35,36,37⟩],41,.length 0⟩
  else if kind=6 then ⟨(0,3),(4,7),0,[⟨18,32,33,34⟩],38,.length 0⟩
  else ⟨(0,6),(7,10),0,[⟨21,35,36,37⟩],41,.length 0⟩
def wire (kind : Fin 8) (k : Nat) : BitVec 8 := (header kind)[k]?.getD 0#8

def plan (kind : Fin 8) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire kind k).toNat⟩

theorem valid (kind : Fin 8) (first count : Nat) : ChunkReceivePlan.Valid (plan kind) (wire kind) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire kind k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

theorem consumed0 : consume (wire 0) (header 0).length []=⟨(header 0).length,header 0,.done (expected 0)⟩ := by decide +kernel
theorem consumed1 : consume (wire 1) (header 1).length []=⟨(header 1).length,header 1,.done (expected 1)⟩ := by decide +kernel
theorem consumed2 : consume (wire 2) (header 2).length []=⟨(header 2).length,header 2,.done (expected 2)⟩ := by decide +kernel
theorem consumed3 : consume (wire 3) (header 3).length []=⟨(header 3).length,header 3,.done (expected 3)⟩ := by decide +kernel
theorem consumed4 : consume (wire 4) (header 4).length []=⟨(header 4).length,header 4,.done (expected 4)⟩ := by decide +kernel
theorem consumed5 : consume (wire 5) (header 5).length []=⟨(header 5).length,header 5,.done (expected 5)⟩ := by decide +kernel
theorem consumed6 : consume (wire 6) (header 6).length []=⟨(header 6).length,header 6,.done (expected 6)⟩ := by decide +kernel
theorem consumed7 : consume (wire 7) (header 7).length []=⟨(header 7).length,header 7,.done (expected 7)⟩ := by decide +kernel

theorem consumed : ∀ kind : Fin 8, consume (wire kind) (header kind).length []=⟨(header kind).length,header kind,.done (expected kind)⟩ := by
  intro kind
  have casesKind : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 ∨ kind=6 ∨ kind=7 := by omega
  rcases casesKind with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact consumed0
  · exact consumed1
  · exact consumed2
  · exact consumed3
  · exact consumed4
  · exact consumed5
  · exact consumed6
  · exact consumed7

theorem facts : ∀ kind : Fin 8, (header kind).length≤45 ∧ (expected kind).len=(header kind).length ∧ (expected kind).framing=.length 0 ∧
    MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token (header kind) (expected kind).method.2))=(if kind.val<6 then kind.val else 6) ∧
    (expected kind).target.2-(expected kind).target.1=3 := by decide +kernel

/-- All six declared methods, lowercase get and a last-character DELETE
    mismatch, through actual reset, UART parsing, URI and method conversion. -/
theorem execution (kind : Fin 8) : ∃ n d after reads, n≤151000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind ∧ MainRequestMethod.Ready d after (header kind) Spec.initial (expected kind) 0 1 ∧
      d.get 14=BitVec.ofNat 32 (if kind.val<6 then kind.val else 6) := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,limit,trace,state,bytes⟩ := MainRequestMethodReset.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) 0 (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+0-(header kind).length=0 := by rw [fs.2.1];omega
  rw [missing] at limit trace state bytes
  simp only [arrivals,List.range_zero,List.map_nil,List.append_nil] at state bytes
  have method := state.method
  rw [fs.2.2.2.1] at method
  refine ⟨n,d,after,_,?_,trace,bytes,state,method⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  rw [hc,fs.2.2.2.2] at limit
  change n≤4209+5*3+(47+8+HeadColdFutureComplete.budget 1024)*(header kind).length+0 at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainRequestMethodWitness
