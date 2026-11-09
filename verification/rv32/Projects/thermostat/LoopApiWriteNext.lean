import Projects.thermostat.LoopApiWriteTransaction
import Projects.thermostat.LoopTransactionMemory
set_option autoImplicit false
namespace E5R.Thermostat.LoopApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec MainApiWriteCaller

/-- Every real write-handler outcome, exact HTTP/UART output, actual keep or
    outer restart and the reusable next-request boundary. The caller metadata
    is supplied by the upstream Request/routing frame proofs. -/
theorem next {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))}
    {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {close : Bool} {used : Word}
    (h : Ready kind future path first c ram input s head amount served close)
    (metadata : LoopTransactionMemory.At ram used) (uart : c.get 19=0x10000000#32)
    (futureReg : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (masked : c.mie_=false)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ n d after, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      LoopReady.At d after reply.state (if close then 0 else served) := by
  dsimp only
  let reply := ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
  have inv : Spec.Inv reply.state := by
    unfold reply ApiWriteHttpSpec.run
    split
    · cases decoded : WireSpec.decode path (MainRequestSpans.body input head amount) first with
      | error status => exact h.invariant
      | ok cmd =>
        dsimp only
        cases result : Spec.transition true s cmd with
        | error err => exact h.invariant
        | ok res =>
          have commit := Spec.commit_inv true s cmd h.invariant
          simpa only [result] using commit
    · exact h.invariant
  obtain ⟨a,na,mid,_,steps,pc,sp,frame,csr,app,_,_,low,capFrame,routeFrame,a19,a22,a18,a23,a26,a21⟩ :=
    LoopApiWriteCaller.transaction h hs bs hhs hbs
  have memory := LoopTransactionMemory.preserve metadata low capFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink low (by decide))) h.serve
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have must := MainCloseSpec.limit head.minor served reached (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
      have contradiction := h.closeSpec.trans must
      rw [kept] at contradiction
      cases contradiction
    · omega
  obtain ⟨nb,d,after,_,finish,ready⟩ := LoopReady.completed a mid reply.state served used close pc sp frame (a19.trans uart)
    (a22.trans h.one) (a18.trans h.two) ((congrArg Prod.fst csr).trans masked) h.stack app inv
    ⟨a21,a23.trans futureReg,a26.trans three⟩ serve room memory.capacity memory.routes
    memory.headLimit memory.bodyLimit memory.filled memory.consumed memory.bound
  refine ⟨na+nb,d,after,?_,ready⟩
  simpa only [List.append_nil] using steps.trans finish.observed
end E5R.Thermostat.LoopApiWriteCaller
