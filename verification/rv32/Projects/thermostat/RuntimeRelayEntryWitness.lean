import Projects.thermostat.RuntimeRelayEntry
import Projects.thermostat.ReceivedFirstMatch
import Projects.thermostat.MainInitWitness
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.Blocking
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.RuntimeRelayEntryWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec

def headBytes (wrong : Bool) := if wrong then WireSpec.ascii "POST /state HTTP/1.1\r\nHost: x\r\n\r\n" else WireSpec.ascii "GET /missing HTTP/1.1\r\nHost: x\r\n\r\n"
def head (wrong : Bool) : Head := match HttpRequestBytes.parse (headBytes wrong) 1024 1024 with
  | .done h => h | _ => ⟨(0,0),(0,0),0,[],0,.empty⟩
def wire (wrong : Bool) (k : Nat) := (headBytes wrong)[k]?.getD 0#8
def plan (wrong : Bool) : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire wrong k).toNat⟩

theorem valid (wrong : Bool) (first count : Nat) : ChunkReceivePlan.Valid (plan wrong) (wire wrong) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire wrong k)⟩
  intro status member;cases member

theorem consumed (wrong : Bool) : consume (wire wrong) (headBytes wrong).length []=⟨(headBytes wrong).length,headBytes wrong,.done (head wrong)⟩ := by
  cases wrong <;> decide +kernel

theorem denied (wrong : Bool) (kind : RouteLiteralInfo.Kind) : RuntimeRequestSpans.path (headBytes wrong) (head wrong)=RouteLiteralInfo.text kind →
    RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token (headBytes wrong) (head wrong).method.2))=false := by
  cases wrong <;> cases kind <;> decide +kernel

/-- Satisfying reset/UART runs through all four literal candidates to the real
    final matcher: one unknown path and one known path with a wrong method. -/
theorem execution (wrong : Bool) :
    ∃ n d after reads lowValue close, Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=headBytes wrong ∧
      RuntimeLiteralInput.At d after (headBytes wrong) Spec.initial (head wrong) 0 (head wrong).len 1 lowValue close 0x80005b9c#32 10#32 0x80001856#32 ∧
      d.get 9=(if wrong then 2#32 else 3#32) ∧ LoopTransactionMemory.At after (BitVec.ofNat 32 (head wrong).len) := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) Blocking.stack_available
  obtain ⟨nr,b,rb,lowValue,close,receive,pc,result,captures,metadata,live,_⟩ := ReceivedFirstMatch.empty ready (wire wrong) (headBytes wrong).length
    (head wrong) (plan wrong) (by cases wrong <;> decide +kernel) (valid _ _ _) (by rw [consumed]) (by cases wrong <;> decide +kernel)
  rw [consumed] at live result
  have leading := RouteReceivedPath.received_path (wire wrong) (headBytes wrong).length (head wrong) (by rw [consumed])
  rw [consumed] at leading
  obtain ⟨nm,d,after,_,route,entry,flag,metadataFinal,_⟩ := RuntimeRelayEntry.contract live pc result (denied wrong) leading metadata
  have flagSpec : (if RuntimeRelayEntry.known (RuntimeRequestSpans.path (headBytes wrong) (head wrong)) then 2#32 else 3#32)=(if wrong then 2#32 else 3#32) := by
    cases wrong <;> decide +kernel
  refine ⟨2550+nr+nm,d,after,MainHeaderStreamPlan.logs (plan wrong) 0 (headBytes wrong).length,lowValue,close,?_,?_,entry,flag.trans flagSpec,metadataFinal⟩
  · simpa only [consumed,List.nil_append,List.append_nil,Nat.add_assoc] using (boot.observed.trans receive).trans route.observed
  · cases wrong <;> decide +kernel
end E5R.Thermostat.RuntimeRelayEntryWitness
