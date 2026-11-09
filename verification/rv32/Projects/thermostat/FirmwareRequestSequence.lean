import Projects.thermostat.FirmwareNextRequest
set_option autoImplicit false
namespace E5R.Thermostat.LoopSpec
open E5R E5R.Thermostat ApiRequestSpec

def final : List Fixed11 → Spec.Snapshot → Nat → Spec.Snapshot × Nat
  | [],s,served => (s,served)
  | r::rs,s,served => final rs (r.reply s).state (nextCount r served)

def output : List Fixed11 → Spec.Snapshot → Nat → ApiRequestSpec.Bytes
  | [],_,_ => []
  | r::rs,s,served => bytes r s served++output rs (r.reply s).state (nextCount r served)

def input (requests : List Fixed11) : ApiRequestSpec.Bytes := requests.flatMap Fixed11.bytes
end E5R.Thermostat.LoopSpec

namespace E5R.Thermostat.RequestSchedules
open E5R E5R.Thermostat ApiRequestSpec
/-- Finite logical environment schedules. Only byte delivery and valid UART
    readiness/lengths occur here; no machine endpoint or parser result does. -/
structure One (r : Fixed11) (s : Spec.Snapshot) where
  wire : Nat → BitVec 8
  headerPlan : MainHeaderStreamPlan.Plan
  bodyPlan : MainLengthStreamPlan.Plan
  delivers : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk
  headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 r.headBytes.length
  bodyValid : MainLengthStreamPlan.Valid bodyPlan wire r.headBytes.length r.body.length
  hs : Bool → List UartTxLoop.Slot
  bs : List UartTxLoop.Slot
  headerLengths : ∀ close, (hs close).length=(ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length close).length
  bodyLength : bs.length=(r.reply s).payload.length

inductive Many : List Fixed11 → Spec.Snapshot → Nat → Type where
  | nil (s : Spec.Snapshot) (served : Nat) : Many [] s served
  | cons {r : Fixed11} {rs : List Fixed11} {s : Spec.Snapshot} {served : Nat}
      (one : One r s) (rest : Many rs (r.reply s).state (LoopSpec.nextCount r served)) : Many (r::rs) s served

def reads : {rs : List Fixed11} → {s : Spec.Snapshot} → {served : Nat} → Many rs s served → List Observed.Read
  | _,_,_,.nil _ _ => []
  | r::_,_,served,.cons one rest =>
    Firmware.nextReads r served one.headerPlan one.bodyPlan one.hs one.bs++reads rest

/-- Concrete induction over the finite delivered requests. The live boundary
    is re-established by actual ELF execution after every request. -/
theorem execute {requests : List Fixed11} {s : Spec.Snapshot} {served : Nat} (plans : Many requests s served)
    {c : Core} {ram : Word → BitVec 8} (h : LoopReady.At c ram s served) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (reads plans)
      (UartTxLoop.events (LoopSpec.output requests s served)) ∧
      Observed.input (reads plans)=LoopSpec.input requests ∧
      LoopReady.At d after (LoopSpec.final requests s served).1 (LoopSpec.final requests s served).2 := by
  induction plans generalizing c ram with
  | nil s served => exact ⟨0,c,ram,.refl _,rfl,h⟩
  | @cons r rs s served one rest ih =>
    obtain ⟨first,a,mid,trace,accepted,ready⟩ := Firmware.next_request r h one.wire one.headerPlan one.bodyPlan
      one.delivers one.headerValid one.bodyValid one.hs one.bs one.headerLengths one.bodyLength
    obtain ⟨last,d,after,finish,acceptedRest,post⟩ := ih ready
    refine ⟨first+last,d,after,?_,?_,post⟩
    · simpa only [reads,LoopSpec.output,LoopSpec.bytes,UartTxLoop.events,List.map_append,List.append_assoc] using trace.trans finish
    · simp only [reads,Observed.input_append,accepted,acceptedRest,LoopSpec.input,List.flatMap_cons]
end E5R.Thermostat.RequestSchedules

namespace E5R.Thermostat.Firmware
open E5R E5R.Thermostat ApiRequestSpec
/-- T2: arbitrary finite sequences in the reviewed T1 byte domain, from reset
    through the real UART/parser/router/control/reply loop. Logical finite
    schedules remain explicit; full input-domain prefix safety is T3. -/
theorem request_sequence (requests : List Fixed11)
    (plans : RequestSchedules.Many requests Spec.initial 0) (c : Core) (ram : Word → BitVec 8)
    (pc : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (_masked : c.mie_=false)
    (stack : Memory.Block UartPlatform.board 0x80ff0000#32 65536) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (RequestSchedules.reads plans)
      (UartTxLoop.events (LoopSpec.output requests Spec.initial 0)) ∧
      Observed.input (RequestSchedules.reads plans)=LoopSpec.input requests ∧
      LoopReady.At d after (LoopSpec.final requests Spec.initial 0).1 (LoopSpec.final requests Spec.initial 0).2 ∧
      AppState.At after (LoopSpec.final requests Spec.initial 0).1 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Spec.Inv (LoopSpec.final requests Spec.initial 0).1 := by
  obtain ⟨a,mid,boot,ready⟩ := LoopReady.reset c ram pc mpp stack
  obtain ⟨last,d,after,steps,accepted,post⟩ := RequestSchedules.execute plans ready
  refine ⟨2550+last,d,after,?_,accepted,post,post.receive.stable.app,post.receive.stable.app.available,post.receive.stable.invariant⟩
  simpa only [List.nil_append] using boot.observed.trans steps
end E5R.Thermostat.Firmware
