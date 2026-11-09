import Projects.thermostat.UnmatchedCore
import Projects.thermostat.RuntimeResponseReply
import Projects.thermostat.LoopReady
import Projects.thermostat.LoopTransactionMemory
import Projects.thermostat.MainTransactionStable
set_option autoImplicit false
namespace E5R.Thermostat.RuntimePreparedRefusalNext
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual prepared empty refusal emits exact HTTP bytes and
    reaches the reusable loop while honoring actual close/count policy. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {served : Nat} {used : Word} {close : Bool} (status : Nat)
    (h : MainTransactionStable.At c ram input s) (metadata : LoopTransactionMemory.At ram used)
    (serve : MainServeLayout.At ram served) (pc : c.pc=0x80001728#32)
    (hlo : 200≤status) (hhi : status≤599)
    (prepared10 : c.get 10=BitVec.ofNat 32 status) (prepared11 : c.get 11=0#32) (prepared20 : c.get 20=0#32)
    (prepared13 : c.get 13=0#32) (prepared12 : c.get 12=1#32) (prepared9 : c.get 9=0x80fff878#32) (prepared24 : c.get 24=0xfffffffe#32)
    (future : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (two : c.get 18=2#32)
    (replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32)
    (closeByte : ram 0x80fff878#32=Encoding.boolByte close) (room : close=false → served<100)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 close).length) :
    ∃ n d after,Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
      (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 close)) ∧ LoopReady.At d after s (if close then 0 else served) := by
  let a := c
  let mid := ram
  have pa : a.pc=0x80001728#32 := pc
  have a10 := prepared10
  have a11 := prepared11
  have a20 := prepared20
  have a13 := prepared13
  have a12 := prepared12
  have a9 := prepared9
  have a24 := prepared24
  have ac : a.sameCsr c := rfl
  have regs (r : Reg) (_ : r∈[2,8,18,19,22,23,26]) : a.get r=c.get r := rfl
  have frame (off len : Nat) (bound : off+len≤3312) : ViewFrame.Region ram mid (sp+BitVec.ofNat 32 off) len := fun _ => rfl
  have app : AppState.At mid s := by
    apply AppState.preserve ram mid s h.app
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide)
  have fpFrame : ViewFrame.Region ram mid fp 532 := fun _ => rfl
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have word := ViewFrame.word fpFrame 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 488=0x80fff9fc#32 by decide +kernel] using word.trans replyCapacity
  have closeFrame : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := fpFrame ⟨100,by decide⟩
    simpa only [show fp+BitVec.ofNat 32 100=0x80fff878#32 by decide +kernel] using byte.trans closeByte
  have serveFrame : ViewFrame.Region ram mid fp 92 := ViewFrame.shrink fpFrame (by decide)
  have serveA := MainServeLayout.preserve (MainServeLayout.region serveFrame) serve
  have metadataA := LoopTransactionMemory.caller metadata (by simpa only [BitVec.add_zero] using frame 0 3304 (by decide))
  have statusWord : a.get 10=BitVec.ofNat 32 status := a10
  have closeWord : mid 0x80fff878#32=(if close then 1#8 else 0#8) := by cases close <;> exact closeFrame
  have headLen : slots.length=(ResponseHeadSpec.bytes status (MainResponseExtractedReply.mime false) ([] : List (BitVec 8)).length close).length := length
  obtain ⟨b,nb,after,_,send,pb,b2,b8,cb,appB,_,b24,b21,rxFrame,low,capFrame,routeFrame,b19,b22,b18,b23,b26⟩ :=
    RuntimeResponseReply.contract_exact false a mid s 0x80ffffc7#32 [] status close pa
      ((regs 2 (by decide)).trans h.sp) ((regs 8 (by decide)).trans h.fp) ((regs 22 (by decide)).trans h.one)
      h.stack app h.invariant (by decide) hlo hhi
      a12 a11 a20 statusWord a13 a9 a24 (Bytes.empty B mid _) cap serveA.tx serveA.txCapacity serveA.uart closeWord
      slots [] headLen (by unfold ResponseHeadSpec.body;split <;> rfl)
  have memory := LoopTransactionMemory.preserve metadataA low capFrame routeFrame
  have serveB := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink low (by decide))) serveA
  obtain ⟨nf,d,final,_,finish,ready⟩ := LoopReady.completed b after s served used close pb b2 b8
    (b19.trans ((regs 19 (by decide)).trans h.uart)) (b22.trans ((regs 22 (by decide)).trans h.one))
    (b18.trans ((regs 18 (by decide)).trans two)) ((congrArg Prod.fst (cb.trans ac)).trans h.masked) h.stack appB h.invariant
    ⟨b21,b23.trans ((regs 23 (by decide)).trans future),b26.trans ((regs 26 (by decide)).trans three)⟩ serveB room memory.capacity memory.routes
    memory.headLimit memory.bodyLimit memory.filled memory.consumed memory.bound
  refine ⟨nb+nf,d,final,?_,ready⟩
  simpa only [ResponseHeadSpec.body,Bool.false_eq_true,ite_false,ite_self,MainResponseExtractedReply.mime,List.length_nil,List.flatMap_nil,List.map_nil,List.append_nil,List.nil_append,UartTxLoop.reads,UartTxLoop.events] using send.trans finish.observed
end E5R.Thermostat.RuntimePreparedRefusalNext
