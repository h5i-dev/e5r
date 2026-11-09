import Projects.thermostat.ChunkPrefixBody
import Projects.thermostat.ChunkCallerPreserve
import Projects.thermostat.RuntimeRequest
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.ChunkSuccessBody
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32
abbrev rx := 0x80ffec14#32

/-- Compaction never writes beyond the byte currently being consumed. -/
theorem written_read (wire : Nat → BitVec 8) (fuel read written : Nat) (state : CState) (body : List (BitVec 8))
    (ordered : written≤read) : (consume wire fuel read written state body).written≤(consume wire fuel read written state body).read := by
  induction fuel generalizing read written state body with
  | zero => exact ordered
  | succ fuel ih =>
    simp only [consume]
    cases hs : chunkStep state (wire read).toNat 1024 with
    | mk next out =>
      cases out with
      | nothing => simpa only [hs] using ih (read+1) written next body (by omega)
      | data => simpa only [hs] using ih (read+1) (written+1) next (body++[wire read]) (by omega)
      | done => dsimp only;omega
      | reject code => dsimp only;omega

/-- This is a representation of the actual compacted buffer, not an input
    specification. The contract below separately relates its header and body
    to the independent stream decoder. Bytes in the unused tail stay arbitrary. -/
def buffer (ram : Word → BitVec 8) (filled : Nat) : List (BitVec 8) :=
  List.ofFn (fun i : Fin filled => ram (rx+BitVec.ofNat 32 i.val))

structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot)
    (head : Head) (result : ChunkBufferSpec.Result) (served : Nat) : Prop where
  pc : c.pc=0x8000106c#32
  stable : MainTransactionStable.At c ram (buffer ram result.read) s
  bank : MainGprBank.At c
  serve : MainServeLayout.At ram served
  two : c.get 18=2#32
  doneTag : c.get 10=2#32
  view : HeadCompletedView.At ram (sp+3320#32) head
  consumed : ramRead ram (sp+3648#32) .w=BitVec.ofNat 32 head.len
  usedReg : c.get 24=BitVec.ofNat 32 result.read
  readWord : ramRead ram (sp+3656#32) .w=BitVec.ofNat 32 result.read
  writeWord : ramRead ram (sp+3660#32) .w=BitVec.ofNat 32 result.written
  body : ChunkBufferView.Body ram sp head.len result.body
  header : ∀ i : Fin input.length, ram (rx+BitVec.ofNat 32 i.val)=input[i]
  bodyLength : result.written=head.len+result.body.length
  bodyBound : result.body.length≤1024
  extent : head.len+result.body.length≤result.read ∧ result.read≤2048

/-- The actual UART/dechunking loop discharges the successful Next caller's
    saved Head, filled/read/write cursors and buffer premises. In particular,
    filled=read is derived from the one-byte reader, not assumed at exit. -/
theorem contract {c ram input s head served}
    (h : MainHeaderToBody.Ready c ram input s head) (kind : head.framing=.chunked)
    (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served)
    (exactHead : input.length=head.len)
    (wire : Nat → BitVec 8) (arrivals : Nat) (plan : ChunkReceivePlan.Plan)
    (space : input.length+arrivals≤2048) (valid : ChunkReceivePlan.Valid plan wire input.length arrivals)
    (done : (consume wire arrivals head.len head.len cStart []).stop=.done) :
    let r := consume wire arrivals head.len head.len cStart []
    ∃ received n d after, received≤arrivals ∧ head.len+received=r.read ∧
      n≤12+125*arrivals+ChunkReceivePlan.cost plan input.length arrivals ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (ChunkReceivePlan.logs plan input.length received) [] ∧
      Ready d after input s head r served ∧ d.sameCsr c ∧ ViewFrame.Region ram after sp 132 ∧ ViewFrame.Region ram after (sp+3204#32) 84 := by
  obtain ⟨received,d,n,after,recvBound,time,trace,boundary,body,_,_,exactRead,header,cursorReg,filled,frame⟩ :=
    ChunkPrefixBody.contract h kind bank wire arrivals plan space valid (by intro k hk lo;omega)
  let r := consume wire arrivals head.len head.len cStart []
  have eqFuel : input.length-head.len+arrivals=arrivals := by omega
  have terminal : MainChunkBuffered.Terminal after sp head.len r d := by
    simpa only [eqFuel,MainChunkBuffered.Boundary,done] using boundary
  obtain ⟨pc,obj,inv,readWord,writeWord,layout,stackPtr,masked,tag⟩ := terminal
  have actualRead : head.len+received=r.read := by
    have := exactRead (by omega)
    change received=(consume wire (input.length-head.len+arrivals) head.len head.len cStart []).read-input.length at this
    rw [eqFuel] at this
    change received=r.read-input.length at this
    have pos := ChunkBufferSpec.positions wire arrivals head.len head.len cStart []
    change head.len≤r.read ∧ _ at pos
    omega
  have length : r.written=head.len+r.body.length := ChunkBufferSpec.body_length wire arrivals head.len head.len head.len cStart [] (by simp)
  have decoded := ChunkBufferSpec.decoded_length wire arrivals head.len head.len cStart []
  have bodyBound : r.body.length≤1024 := by simpa only [List.length_nil] using decoded (ChunkDecodedInvariant.initial 1024)
  have extent : head.len+r.body.length≤r.read ∧ r.read≤2048 := by
    have ordered := written_read wire arrivals head.len head.len cStart [] (by omega)
    change r.written≤r.read at ordered
    omega
  have stable : MainTransactionStable.At d after (buffer after r.read) s := by
    refine ⟨stackPtr,(frame.core 8 (by decide)).trans h.stable.fp,(frame.core 19 (by decide)).trans h.stable.uart,
      (frame.core 22 (by decide)).trans h.stable.one,?_,?_,?_,?_,h.stable.invariant,h.stable.stack,masked⟩
    · simpa only [buffer,List.length_ofFn] using extent.2
    · simpa only [buffer,List.length_ofFn,sp,fp,show 0x80ffeb90#32+3288#32=0x80fff814#32+84#32 by decide +kernel,exactHead,actualRead] using filled
    · intro i
      change after (rx+BitVec.ofNat 32 i.val)=(List.ofFn (fun j : Fin r.read => after (rx+BitVec.ofNat 32 j.val)))[i.val]' (by simpa only [buffer] using i.isLt)
      simp only [List.getElem_ofFn]
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,sp,show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub frame.low 44 25 (by decide)
  have bankAfter : MainGprBank.At d := MainGprBank.preserve (fun rr member => by
    have safe : ∀ rr : Reg, rr∈[21,23,26] → MainChunkCoreFrame.Kept rr := by decide +kernel
    exact frame.core rr (safe rr member)) bank
  have serveAfter := MainServeLayout.preserve (by intro off safe;simpa only [sp,show 0x80ffeb90#32+3204#32=MainServeLayout.fp by decide +kernel] using frame.words off safe) serve
  have copied : ViewFrame.Region ram after (sp+3320#32) 304 := by
    have sub := HeadRegionFrame.sub frame.futureHigh 28 304 (by decide)
    simpa only [BitVec.add_assoc,show 3292#32+28#32=3320#32 by decide +kernel] using sub
  have headView := MainCopyView.head copied head (by simpa only [sp,fp,show 0x80ffeb90#32+3320#32=0x80fff814#32+116#32 by decide +kernel] using h.view)
  have consumed : ramRead after (sp+3648#32) .w=BitVec.ofNat 32 head.len := by
    have word := ViewFrame.word frame.futureHigh 356 (by decide)
    simpa only [sp,fp,BitVec.add_assoc,show 3292#32+356#32=3648#32 by decide +kernel,show 0x80ffeb90#32+3648#32=0x80fff814#32+444#32 by decide +kernel] using word.trans h.consumed
  refine ⟨received,n,d,after,recvBound,actualRead,by simpa only [eqFuel] using time,trace,
    ⟨pc,stable,bankAfter,serveAfter,(frame.core 18 (by decide)).trans h.two,?_,headView,consumed,(by simpa only [eqFuel] using cursorReg),readWord,writeWord,?_,?_,length,bodyBound,extent⟩,frame.csr,frame.low,frame.futureLow⟩
  · simpa only [r,done] using tag
  · simpa only [eqFuel] using body
  · intro i
    exact (header ⟨i.val,by have := i.isLt;omega⟩).trans (h.stable.bytes i)
end E5R.Thermostat.ChunkSuccessBody
