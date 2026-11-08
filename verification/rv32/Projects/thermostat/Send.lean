import Projects.thermostat.SendTransfer
namespace E5R.Thermostat.Send
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Fresh real send_future entry through RET. Valid status/MIME inputs produce
    the specified header and clipped/HEAD/no-body-selected payload as exact THR
    events. Each byte has an explicit finite readiness schedule; this does not
    assume unconditional UART progress or physical delivery. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (frame obj res tx io ctptr : Word)
    (raw status : Nat) (ct payload : List (BitVec 8)) (close head : Bool)
    (h : SendInput.Pre c ram frame obj res tx io ctptr raw status ct payload close head)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes status ct payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body status head payload).length) :
    ∃ d n after, n≤2400+UartWriteAll.time (ResponseHeadSpec.bytes status ct payload.length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body status head payload) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes status ct payload.length close)++UartTxLoop.events (ResponseHeadSpec.body status head payload)) ∧
      FormatCursor.Returned c d ∧ ramRead after (res+0#32) .w=0xffffffff#32 ∧
      ramRead after (res+4#32) .w=ResponseHeadBodyMath.boolWord close ∧ after (obj+45#32)=1#8 ∧
      Bytes.Span B after tx (ResponseHeadSpec.bytes status ct payload.length close) ∧
      (∀ x, (∀ i : Fin 144, x≠frame+BitVec.ofNat 32 i.val) → (∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 8, x≠res+BitVec.ofNat 32 i.val) → (∀ i : Fin 192, x≠tx+BitVec.ofNat 32 i.val) → after x=ram x) := by
  obtain ⟨a,na,ma,ba,ta,qa⟩ := SendHeader.contract c ram frame obj res tx io ctptr raw status ct payload close head h
  obtain ⟨d,nd,after,bd,td,hr,hresult,hclose,hdone,hbytes,hframe⟩ := SendTransfer.contract c a ram ma frame obj res tx io ctptr
    raw status ct payload close head h qa hs bs hhs hbs
  refine ⟨d,na+nd,after,by omega,?_,hr,hresult,hclose,hdone,hbytes,?_⟩
  · simpa only [List.nil_append] using ta.observed.trans td
  · intro x hstack hobj hres htx
    exact (hframe x hobj hres).trans (qa.memoryFrame x hstack hobj htx)

/-- Observable stream projection. Readiness polls are not accepted RBR input,
    and the output concatenates the header with the selected body exactly. -/
theorem projection (status : Nat) (ct payload : List (BitVec 8)) (close head : Bool) (hs bs : List UartTxLoop.Slot) :
    Observed.input (UartTxLoop.reads hs++UartTxLoop.reads bs)=[] ∧
    Observed.output (UartTxLoop.events (ResponseHeadSpec.bytes status ct payload.length close)++UartTxLoop.events (ResponseHeadSpec.body status head payload))=
      ResponseHeadSpec.bytes status ct payload.length close++ResponseHeadSpec.body status head payload := by
  rw [Observed.input_append,Observed.output_append,UartTxLoop.no_input,UartTxLoop.no_input,UartTxLoop.output,UartTxLoop.output]
  exact ⟨rfl,rfl⟩
end E5R.Thermostat.Send
