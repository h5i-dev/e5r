import Projects.thermostat.RuntimeReadViews
import Projects.thermostat.LoopReadRound
import Projects.thermostat.LoopTransactionMemory
import Projects.thermostat.MainReadDecoded
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeReadNext
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
/-- The separate real Read transaction reaches the same reusable boundary,
    including actual close/restart and exact full HTTP/UART output. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {served : Nat} {close isHead : Bool} {used : Word}
    (h : RuntimeReadViews.DecodedReady c ram input s served close isHead)
    (metadata : LoopTransactionMemory.At ram used) (future : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32)
    (room : close=false → served<100) (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body 200 isHead (ReplyJson.snapshot s)).length) :
    ∃ n d after, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close)++
        UartTxLoop.events (ResponseHeadSpec.body 200 isHead (ReplyJson.snapshot s))) ∧ LoopReady.At d after s (if close then 0 else served) := by
  have body : ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot s)=ResponseHeadSpec.body 200 isHead (ReplyJson.snapshot s) := by
    rw [h.method];cases isHead <;> rfl
  obtain ⟨a,na,mid,_,steps,pc,sp,frame,csr,app,_,_,_,_,a21,low,capFrame,routeFrame,a19,a22,a18,a23,a26⟩ :=
    LoopReadRound.contract_exact c ram s close h.acquiredInput h.stable.invariant h.stable.app h.stable.stack h.payload h.capacity h.stable.one
      h.replyCapacity h.serve.tx h.serve.txCapacity h.closeByte hs bs hhs (by rw [body];exact hbs)
  rw [body] at steps
  have memory := LoopTransactionMemory.preserve metadata low capFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink low (by decide))) h.serve
  obtain ⟨nb,d,after,_,finish,ready⟩ := LoopReady.completed a mid s served used close pc sp frame (a19.trans h.stable.uart)
    a22 a18 ((congrArg Prod.fst csr).trans h.stable.masked) h.stable.stack app h.stable.invariant
    ⟨a21,a23.trans future,a26.trans three⟩ serve room memory.capacity memory.routes
    memory.headLimit memory.bodyLimit memory.filled memory.consumed memory.bound
  refine ⟨na+nb,d,after,?_,ready⟩
  simpa only [List.append_nil] using steps.trans finish.observed
end E5R.Thermostat.RuntimeReadNext
