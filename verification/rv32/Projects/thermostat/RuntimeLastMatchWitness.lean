import Projects.thermostat.RuntimeLastMatch
import Projects.thermostat.ReceivedFirstMatch
import Projects.thermostat.MainInitWitness
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.Blocking
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.RuntimeLastMatchWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec

inductive Case where | missing | wrong | empty | extra | valid deriving DecidableEq

def headBytes : Case → List (BitVec 8)
  | .missing => WireSpec.ascii "GET /missing HTTP/1.1\r\nHost: x\r\n\r\n"
  | .wrong => WireSpec.ascii "POST /state HTTP/1.1\r\nHost: x\r\n\r\n"
  | .empty => WireSpec.ascii "PUT /relay/ HTTP/1.1\r\nHost: x\r\n\r\n"
  | .extra => WireSpec.ascii "PUT /relay/3/x HTTP/1.1\r\nHost: x\r\n\r\n"
  | .valid => WireSpec.ascii "PUT /relay/3 HTTP/1.1\r\nHost: x\r\n\r\n"
def head (which : Case) : Head := match HttpRequestBytes.parse (headBytes which) 1024 1024 with
  | .done h => h | _ => ⟨(0,0),(0,0),0,[],0,.empty⟩
def wire (which : Case) (k : Nat) := (headBytes which)[k]?.getD 0#8
def plan (which : Case) : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire which k).toNat⟩

theorem valid (which : Case) (first count : Nat) : ChunkReceivePlan.Valid (plan which) (wire which) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire which k)⟩
  intro status member;cases member

theorem consumed (which : Case) : consume (wire which) (headBytes which).length []=⟨(headBytes which).length,headBytes which,.done (head which)⟩ := by
  cases which <;> decide +kernel

theorem denied (which : Case) (kind : RouteLiteralInfo.Kind) : RuntimeRequestSpans.path (headBytes which) (head which)=RouteLiteralInfo.text kind →
    RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token (headBytes which) (head which).method.2))=false := by
  cases which <;> cases kind <;> decide +kernel

/-- Satisfying reset/UART executions cover unknown/wrong-method routes and
    empty, extra-slash and valid relay captures through the real final RET. -/
theorem execution (which : Case) :
    ∃ n d after reads,Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=headBytes which ∧ d.pc=0x80001856#32 ∧
      d.get 10=(if which=.valid then 1#32 else 0#32) ∧
      d.get 11=(if which=.valid ∨ which=.extra then 1#32 else 0#32) ∧
      d.get 9=(if which=.wrong then 2#32 else 3#32) ∧
      MainTransactionStable.At d after (headBytes which) Spec.initial ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 (head which).len) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  obtain ⟨nr,b,rb,lowValue,close,receive,pc,result,captures,metadata,live,_⟩ := ReceivedFirstMatch.empty ready (wire which) (headBytes which).length
    (head which) (plan which) (by cases which <;> decide +kernel) (valid _ _ _) (by rw [consumed]) (by cases which <;> decide +kernel)
  rw [consumed] at live result
  have leading := RouteReceivedPath.received_path (wire which) (headBytes which).length (head which) (by rw [consumed])
  rw [consumed] at leading
  obtain ⟨nm,d,after,_,route,pcFinal,matchFinal,countFinal,flag,stable,metadataFinal,_⟩ := RuntimeLastMatch.contract live pc result (denied which) leading metadata
  have flagSpec : (if RuntimeRelayEntry.known (RuntimeRequestSpans.path (headBytes which) (head which)) then 2#32 else 3#32)=(if which=.wrong then 2#32 else 3#32) := by
    cases which <;> decide +kernel
  have matchSpec : (if RouteSpec.relayPath (RuntimeRequestSpans.path (headBytes which) (head which)) then 1#32 else 0#32)=(if which=.valid then 1#32 else 0#32) := by
    cases which <;> decide +kernel
  have countSpec : RouteRelayBody.count (RuntimeRequestSpans.path (headBytes which) (head which))=(if which=.valid ∨ which=.extra then 1#32 else 0#32) := by
    cases which <;> decide +kernel
  refine ⟨2550+nr+nm,d,after,MainHeaderStreamPlan.logs (plan which) 0 (headBytes which).length,?_,?_,pcFinal,
    matchFinal.trans matchSpec,countFinal.trans countSpec,flag.trans flagSpec,stable,metadataFinal⟩
  · simpa only [consumed,List.nil_append,List.append_nil,Nat.add_assoc] using (boot.observed.trans receive).trans route.observed
  · cases which <;> decide +kernel
end E5R.Thermostat.RuntimeLastMatchWitness
