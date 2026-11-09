import Projects.thermostat.ChunkCallerStart
import Projects.thermostat.ChunkCallerStreaming
import Projects.thermostat.ChunkRejectFinish
import Projects.thermostat.MainHeaderToBodyRegs
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.ChunkRejectBody
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual chunked-body initialization/receive/decode/refusal, full empty
    close response and next poll. All saved registers and static memory words
    at the refusal continuation are derived from the real body loop. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    (h : MainHeaderToBody.Ready c ram input s head) (kind : head.framing=.chunked)
    (served : Nat) (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served)
    (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At ram)
    (wire : Nat → BitVec 8) (arrivals status : Nat) (plan : ChunkReceivePlan.Plan)
    (space : input.length+arrivals≤2048) (valid : ChunkReceivePlan.Valid plan wire input.length arrivals)
    (inputWire : ∀ k (hk : k<input.length), head.len≤k → input[k]'hk=wire k)
    (reject : (consume wire (input.length-head.len+arrivals) head.len head.len cStart []).stop=.reject status)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 true).length) :
    ∃ received d n after, received≤arrivals ∧
      (consume wire (input.length-head.len+arrivals) head.len head.len cStart []).read≤input.length+received ∧
      (input.length≤head.len+1 → received=(consume wire (input.length-head.len+arrivals) head.len head.len cStart []).read-input.length) ∧
      n≤12+125*(input.length-head.len+arrivals)+ChunkReceivePlan.cost plan input.length arrivals+3322+
        UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (ChunkReceivePlan.logs plan input.length received++UartTxLoop.reads slots)
        (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 true)) ∧ LoopReady.At d after s 0 := by
  have startPC : c.pc=0x80000e54#32 := by simpa only [kind,MainBodyHeadDispatch.At] using h.cut
  have chunkLayout : MainChunkLayout.At ram sp := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact h.stable.layout.head.rx
    · exact h.stable.layout.capacity
    · exact h.stable.layout.head.config
    · exact h.stable.layout.head.bodyLimit
    · exact h.stable.layout.filledPtr
  have stack : Memory.Block B sp 4928 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 4928) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have startPtr : c.get 23=sp+3680#32 := by
    simpa only [sp,show 0x80ffeb90#32+3680#32=0x80fff9f0#32 by decide +kernel] using bank.future
  have filled : ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 input.length := by
    simpa only [sp,fp,show 0x80ffeb90#32+3288#32=0x80fff814#32+84#32 by decide +kernel] using h.stable.layout.filled
  obtain ⟨a,mid,init,started,initFrame,initRx⟩ := ChunkCallerStart.contract B c ram sp head.len input.length startPC h.stable.sp h.stable.fp
    startPtr h.length h.stable.one h.stable.uart h.stable.masked stack (by decide) chunkLayout filled (by have := h.bounds.length.2;have := Nat.min_le_left input.length 1024;omega) h.stable.layout.bound
  have complete : (consume wire (input.length-head.len+arrivals) head.len head.len cStart []).stop≠.needInput := by
    rw [reject];intro eq;cases eq
  have unread : ChunkBufferView.Unread wire mid sp head.len input.length := by
    intro k lo hi
    have rx := initRx ⟨k,by have := h.stable.layout.bound;omega⟩
    have byte := h.stable.bytes ⟨k,hi⟩
    change mid ((sp+132#32)+BitVec.ofNat 32 k)=wire k
    apply rx.trans
    apply byte.trans
    exact inputWire k hi lo
  have body : ChunkBufferView.Body mid sp head.len [] := by intro i;exact Fin.elim0 i
  obtain ⟨received,nb,b,rb,receivedBound,bound,decode,terminal,_,appFrame,_,readBound,noLeft,_,filledWord,bodyFrame⟩ :=
    ChunkCallerStreaming.contract wire plan arrivals started space unread body (by simp) valid complete
  have caller := ChunkCallerFrame.trans initFrame bodyFrame
  obtain ⟨endPC,_,_,_,_,_,_,mask,result⟩ := terminal
  rw [reject] at result
  obtain ⟨statusSet,error,tag⟩ := result
  have lo : 200≤status := by rcases statusSet with rfl|rfl <;> decide
  have hi : status≤599 := by rcases statusSet with rfl|rfl <;> decide
  have app : AppState.At rb s := by
    apply AppState.preserve ram rb s h.stable.app
    have region := HeadRegionFrame.sub caller.low 44 25 (by decide)
    simpa only [ViewFrame.Region,sp,show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using region
  have bankB : MainGprBank.At b := MainGprBank.preserve (fun r safe => by
    have kept : ∀ r : Reg, r∈[21,23,26] → MainChunkCoreFrame.Kept r := by decide +kernel
    exact caller.core r (kept r safe)) bank
  have serveB : MainServeLayout.At rb served := by
    apply MainServeLayout.preserve _ serve
    intro off safe
    simpa only [sp,show 0x80ffeb90#32+3204#32=MainServeLayout.fp by decide +kernel] using caller.words off safe
  have capB : ramRead rb 0x80ffeba0#32 .w=2048#32 := by
    have word := ViewFrame.word caller.low 16 (by decide)
    have value : ramRead rb 0x80ffeba0#32 .w=ramRead ram 0x80ffeba0#32 .w := by
      simpa only [sp,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using word
    exact value.trans capacity
  have routesB : MainRouterTable.At rb := by
    apply MainRouterTable.preserve routes
    have region := HeadRegionFrame.sub caller.low 72 60 (by decide)
    simpa only [sp,show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using region
  obtain ⟨d,n,after,sendBound,response,ready⟩ := ChunkRejectFinish.contract b rb s served status endPC tag
    ((caller.core 18 (by decide)).trans h.two) error ((caller.core 2 (by decide)).trans h.stable.sp)
    ((caller.core 8 (by decide)).trans h.stable.fp) ((caller.core 19 (by decide)).trans h.stable.uart)
    ((caller.core 22 (by decide)).trans h.stable.one) mask h.stable.stack app h.stable.invariant bankB serveB capB routesB lo hi slots length
  refine ⟨received,d,12+nb+n,after,receivedBound,readBound,?_,by omega,?_,ready⟩
  · intro narrow
    have exactReceived := noLeft narrow
    omega
  simpa only [List.nil_append,List.append_nil] using (init.observed.trans decode).trans response
end E5R.Thermostat.ChunkRejectBody
