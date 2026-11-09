import Projects.thermostat.FirmwareCompleteRequests
import Projects.thermostat.ReceivedLiteralWriteWitness
import Projects.thermostat.ReceivedRelayWrongMethodWitness
import Projects.thermostat.FirmwareSequenceWitness
set_option autoImplicit false
namespace E5R.Thermostat.FirmwareCompleteWitness
open E5R E5R.Thermostat HttpRequestSpec CompleteRequestSpec

def immediate (wire : Nat → BitVec 8) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire k).toNat⟩

theorem valid (wire : Nat → BitVec 8) (first count : Nat) : ChunkReceivePlan.Valid (immediate wire) wire first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire k)⟩
  intro status member;cases member

/-- Every pure complete request has a satisfying finite logical schedule;
    successful outcomes or machine endpoints are not schedule premises. -/
def one (r : Request) (s : Spec.Snapshot) : CompleteRequestSchedules.One r s where
  headerPlan := immediate r.wire
  headerValid := valid _ _ _
  lengthPlan := immediate r.wire
  chunkPlan := immediate r.wire
  bodyValid := by cases r.framed with
    | empty => trivial
    | length amount => exact valid _ _ _
    | chunked budget => exact valid _ _ _
  hs := fun close => List.replicate (ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length close).length ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩
  bs := List.replicate (ResponseHeadSpec.body (r.reply s).status r.isHead (r.reply s).payload).length ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩
  headerLengths := fun _ => List.length_replicate
  bodyLength := List.length_replicate

def many : (rs : List Request) → (s : Spec.Snapshot) → (served : Nat) → CompleteRequestSchedules.Many rs s served
  | [],s,served => .nil s served
  | r::rs,s,served => .cons (one r s) (many rs (r.reply s).state (r.nextCount served))

def empty : Request where
  wire := ReceivedRelayWrongMethodWitness.wire .empty
  fuel := (ReceivedRelayWrongMethodWitness.headBytes .empty).length
  head := ReceivedRelayWrongMethodWitness.head .empty
  space := by decide +kernel
  accepted := by rw [ReceivedRelayWrongMethodWitness.header]
  framed := .empty (by decide +kernel)

def chunked : Request where
  wire := ReceivedLiteralWriteWitness.wire .setpoint
  fuel := (ReceivedLiteralWriteWitness.headBytes .setpoint).length
  head := ReceivedLiteralWriteWitness.head .setpoint
  space := by decide +kernel
  accepted := by rw [ReceivedLiteralWriteWitness.header]
  framed := .chunked (ReceivedLiteralWriteWitness.encoded .setpoint).length rfl (by decide +kernel) (ReceivedLiteralWriteWitness.chunks .setpoint).2

def length : Request where
  wire := FirmwareSequenceWitness.wire (FirmwareSequenceWitness.request .temp false)
  fuel := (FirmwareSequenceWitness.request .temp false).headBytes.length
  head := (FirmwareSequenceWitness.request .temp false).head
  space := Nat.le_trans (FirmwareSequenceWitness.request .temp false).headBound (by decide)
  accepted := by
    have delivered : ∀ k (hk : k<(FirmwareSequenceWitness.request .temp false).bytes.length),
        FirmwareSequenceWitness.wire (FirmwareSequenceWitness.request .temp false) k=(FirmwareSequenceWitness.request .temp false).bytes[k]'hk := by
      intro k hk
      simp only [FirmwareSequenceWitness.wire,List.getElem?_eq_getElem hk,Option.getD_some]
    rw [ApiConsume.exact_head _ _ delivered]
  framed := .length 2 rfl

/-- A mixed-framing sequence inhabits the public theorem, from actual reset
    through literal write, real relay wrong-method and fixed-length write. -/
theorem mixed :
    ∃ n d after,Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩
      (CompleteRequestSchedules.manyReads (many [chunked,empty,length] Spec.initial 0))
      (UartTxLoop.events (CompleteRequestSpec.output [chunked,empty,length] Spec.initial 0)) ∧
      Observed.input (CompleteRequestSchedules.manyReads (many [chunked,empty,length] Spec.initial 0))=CompleteRequestSpec.input [chunked,empty,length] ∧
      LoopReady.At d after (CompleteRequestSpec.final [chunked,empty,length] Spec.initial 0).1 (CompleteRequestSpec.final [chunked,empty,length] Spec.initial 0).2 ∧
      AppState.At after (CompleteRequestSpec.final [chunked,empty,length] Spec.initial 0).1 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Spec.Inv (CompleteRequestSpec.final [chunked,empty,length] Spec.initial 0).1 :=
  Firmware.complete_request_sequence [chunked,empty,length] (many _ _ _) MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl) rfl Blocking.stack_available
end E5R.Thermostat.FirmwareCompleteWitness
