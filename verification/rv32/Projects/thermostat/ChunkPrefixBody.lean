import Projects.thermostat.ChunkCallerStart
import Projects.thermostat.ChunkCallerPump

import Projects.thermostat.MainHeaderToBodyRegs
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.ChunkPrefixBody
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual initialization and arbitrary finite chunk input, including an
    incomplete body. Caller facts, decoded bytes and unread buffered bytes are
    retained for the actual wait, success or capacity-refusal continuation. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    (h : MainHeaderToBody.Ready c ram input s head) (kind : head.framing=.chunked)
    (bank : MainGprBank.At c)
    (wire : Nat → BitVec 8) (arrivals : Nat) (plan : ChunkReceivePlan.Plan)
    (space : input.length+arrivals≤2048) (valid : ChunkReceivePlan.Valid plan wire input.length arrivals)
    (inputWire : ∀ k (hk : k<input.length), head.len≤k → input[k]'hk=wire k)
    :
    let r := consume wire (input.length-head.len+arrivals) head.len head.len cStart []
    ∃ received d n after, received≤arrivals ∧
      n≤12+125*(input.length-head.len+arrivals)+ChunkReceivePlan.cost plan input.length arrivals ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (ChunkReceivePlan.logs plan input.length received) [] ∧
      MainChunkBuffered.Boundary B d after sp head.len (input.length+received) r ∧
      ChunkBufferView.Body after sp head.len r.body ∧ ChunkBufferView.Unread wire after sp r.read (input.length+received) ∧
      r.read≤input.length+received ∧ (input.length≤head.len+1 → received=r.read-input.length) ∧
      ViewFrame.Region ram after (sp+132#32) head.len ∧ d.get 24=BitVec.ofNat 32 r.read ∧ ramRead after (sp+3288#32) .w=BitVec.ofNat 32 (input.length+received) ∧ ChunkCallerFrame.At c d ram after sp := by
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
  have unread : ChunkBufferView.Unread wire mid sp head.len input.length := by
    intro k lo hi
    have rx := initRx ⟨k,by have := h.stable.layout.bound;omega⟩
    have byte := h.stable.bytes ⟨k,hi⟩
    change mid ((sp+132#32)+BitVec.ofNat 32 k)=wire k
    apply rx.trans
    apply byte.trans
    exact inputWire k hi lo
  have body : ChunkBufferView.Body mid sp head.len [] := by intro i;exact Fin.elim0 i
  obtain ⟨received,nb,b,rb,receivedBound,bound,decode,boundary,payload,unreadFinal,_,headerFrame,readBound,noLeft,cursorReg,filledWord,bodyFrame⟩ :=
    ChunkCallerPump.contract wire plan arrivals started space unread body (by simp) valid
  refine ⟨received,b,12+nb,rb,receivedBound,by omega,?_,boundary,payload,unreadFinal,readBound,?_,?_,cursorReg,filledWord,ChunkCallerFrame.trans initFrame bodyFrame⟩
  · simpa only [List.nil_append] using init.observed.trans decode
  · intro narrow
    have exactReceived := noLeft narrow
    omega
  · exact HeadRegionFrame.trans (ViewFrame.shrink initRx (by have := started.startWritten;have := started.writtenRead;have := started.readFilled;have := started.capacity;omega)) headerFrame
end E5R.Thermostat.ChunkPrefixBody
