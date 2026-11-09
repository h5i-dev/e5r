import Projects.thermostat.ChunkPrefixBody
import Projects.thermostat.ChunkCallerPreserve
import Projects.thermostat.RejectBodyResponse
import Projects.thermostat.MainChunkCapacityRefusal
set_option autoImplicit false
namespace E5R.Thermostat.ChunkCapacityBody
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32

/-- A valid but incomplete encoded chunk prefix that fills the real RX array
    follows the actual capacity413 refusal, real response and outer restart.
    Neither caller layout nor the desired refusal PC is an environment premise. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    (h : MainHeaderToBody.Ready c ram input s head) (kind : head.framing=.chunked)
    (served : Nat) (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served)
    (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At ram)
    (wire : Nat → BitVec 8) (arrivals : Nat) (plan : ChunkReceivePlan.Plan)
    (full : input.length+arrivals=2048) (valid : ChunkReceivePlan.Valid plan wire input.length arrivals)
    (inputWire : ∀ k (hk : k<input.length), head.len≤k → input[k]'hk=wire k)
    (incomplete : (consume wire (input.length-head.len+arrivals) head.len head.len cStart []).stop=.needInput)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes 413 [] 0 true).length) :
    ∃ d n after, n≤12+125*(input.length-head.len+arrivals)+ChunkReceivePlan.cost plan input.length arrivals+9+3318+
        UartWriteAll.time (ResponseHeadSpec.bytes 413 [] 0 true) slots ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (ChunkReceivePlan.logs plan input.length arrivals++UartTxLoop.reads slots)
        (UartTxLoop.events (ResponseHeadSpec.bytes 413 [] 0 true)) ∧ LoopReady.At d after s 0 := by
  obtain ⟨received,a,nb,mid,receivedBound,bound,receive,boundary,_,_,readBound,_,_,_,_,frame⟩ := ChunkPrefixBody.contract h kind bank wire arrivals plan (Nat.le_of_eq full) valid inputWire
  let r := consume wire (input.length-head.len+arrivals) head.len head.len cStart []
  have headBound : head.len≤input.length := by have := h.bounds.length.2;have := Nat.min_le_left input.length 1024;omega
  have exhausted := ChunkBufferSpec.exhausted_read wire (input.length-head.len+arrivals) head.len head.len cStart [] incomplete
  have actualRead : r.read=input.length+arrivals := by change r.read=head.len+(input.length-head.len+arrivals) at exhausted;omega
  have receivedEq : received=arrivals := by change r.read≤input.length+received at readBound;omega
  subst received
  have pending : MainChunkLoopInvariant.At B a mid sp head.len r.read r.written 2048 r.state := by
    simpa only [MainChunkBuffered.Boundary,incomplete,full] using boundary
  have allRead : r.read=2048 := actualRead.trans full
  obtain ⟨b,refusal,bpc,error,tag,zero,csr,regs⟩ := MainChunkCapacityRefusal.contract pending allRead rfl
  obtain ⟨appA,bankA,serveA,capA,routesA⟩ := ChunkCallerPreserve.contract frame h.stable.app bank serve capacity routes
  have cut : MainHeaderDispatchTwo.At b (.reject 413) := ⟨bpc,zero,error,tag⟩
  have bankB : MainGprBank.At b := MainGprBank.preserve (fun rr safe => by
    have ne : ∀ rr : Reg, rr∈[21,23,26] → rr≠10 ∧ rr≠11 ∧ rr≠27 ∧ rr≠9 ∧ rr≠18 := by decide +kernel
    obtain ⟨n10,n11,n27,n9,n18⟩ := ne rr safe
    exact regs rr n10 n11 n27 n9 n18) bankA
  obtain ⟨d,n,after,sendBound,response,ready⟩ := RejectBodyResponse.contract b mid s served 413 cut
    ((regs 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pending.stackPtr)
    ((regs 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pending.framePtr)
    ((regs 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pending.uart)
    ((regs 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pending.one)
    ((congrArg Prod.fst csr).trans pending.masked) h.stable.stack appA h.stable.invariant bankB serveA capA routesA
    (by decide) (by decide) slots length
  refine ⟨d,nb+9+n,after,by omega,?_,ready⟩
  simpa only [List.nil_append,List.append_nil] using (receive.trans refusal.observed).trans response
end E5R.Thermostat.ChunkCapacityBody
