import Projects.thermostat.ChunkCallerBuffered
import Projects.thermostat.ChunkCallerRefill
import Projects.thermostat.MainChunkStreaming
namespace E5R.Thermostat.ChunkCallerStreaming
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec ChunkBufferView MainChunkStreaming
abbrev B := UartPlatform.board
/-- A terminal decoder must consume at least one supplied byte. This lets
    the one-byte UART reader derive zero buffered leftovers, including errors. -/
theorem terminal_advance (wire : Nat → BitVec 8) (fuel read written : Nat) (s : CState) (body : List (BitVec 8))
    (terminal : (consume wire fuel read written s body).stop≠.needInput) :
    read<(consume wire fuel read written s body).read := by
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    rw [consume]
    cases hs : chunkStep s (wire read).toNat 1024 with
    | mk next out =>
      cases out with
      | nothing => dsimp only;have := ChunkBufferSpec.positions wire fuel (read+1) written next body;omega
      | data => dsimp only;have := ChunkBufferSpec.positions wire fuel (read+1) (written+1) next (body++[wire read]);omega
      | done => dsimp only;omega
      | reject code => dsimp only;omega

/-- Conditional finite stream refinement for the actual in-place body loop.
    A supplied finite LSR/RBR schedule must complete the pure decoder within
    the raw-buffer bound. It does not assert physical or scheduler progress. -/
theorem contract (wire : Nat → BitVec 8) (plan : ChunkReceivePlan.Plan) (arrivals : Nat)
    {c ram sp start read written filled s body}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (space : filled+arrivals≤2048)
    (hu : Unread wire ram sp read filled) (hb : Body ram sp start body)
    (hlen : written=start+body.length)
    (valid : ChunkReceivePlan.Valid plan wire filled arrivals)
    (complete : (consume wire (filled-read+arrivals) read written s body).stop≠.needInput) :
    let r := consume wire (filled-read+arrivals) read written s body
    ∃ received n d after, received≤arrivals ∧
      n≤125*(filled-read+arrivals)+ChunkReceivePlan.cost plan filled arrivals ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (ChunkReceivePlan.logs plan filled received) [] ∧
      MainChunkBuffered.Terminal after sp start r d ∧ Body after sp start r.body ∧
      MainChunkLoopStep.AppFrame ram after sp ∧ ViewFrame.Region ram after (sp+132#32) start ∧
      r.read≤filled+received ∧ (filled≤read+1 → r.read=filled+received) ∧
      d.get 24=BitVec.ofNat 32 r.read ∧ ramRead after (sp+3288#32) .w=BitVec.ofNat 32 (filled+received) ∧ ChunkCallerFrame.At c d ram after sp := by
  induction arrivals generalizing c ram read written filled s body with
  | zero =>
    obtain ⟨n,d,after,hn,trace,bound,bodyView,unread,app,header,cursorReg,filledWord,firstFrame⟩ :=
      ChunkCallerBuffered.contract wire (filled-read) h (by have := h.readFilled;omega) hu hb hlen
    have done : (consume wire (filled-read) read written s body).stop≠.needInput := by simpa only [Nat.add_zero] using complete
    refine ⟨0,n,d,after,by omega,by simpa only [Nat.add_zero,ChunkReceivePlan.cost] using hn,
      trace.observed,terminal_boundary bound done,bodyView,app,header,?_,?_,(by simpa only [Nat.add_zero] using cursorReg),(by simpa only [Nat.add_zero] using filledWord),firstFrame⟩
    · have pos := ChunkBufferSpec.positions wire (filled-read) read written s body
      have := h.readFilled
      simp only [Nat.add_zero]
      omega
    · intro narrow
      have advance := terminal_advance wire (filled-read) read written s body done
      have positions := ChunkBufferSpec.positions wire (filled-read) read written s body
      have := h.readFilled
      simp only [Nat.add_zero]
      omega
  | succ arrivals ih =>
    let q := consume wire (filled-read) read written s body
    obtain ⟨n,d,after,hn,trace,bound,bodyView,unread,app,header,cursorReg,filledWord,firstFrame⟩ :=
      ChunkCallerBuffered.contract wire (filled-read) h (by have := h.readFilled;omega) hu hb hlen
    have split := ChunkBufferConcat.consume_add wire (filled-read) (arrivals+1) read written s body
    by_cases done : q.stop≠.needInput
    · have result : consume wire (filled-read+(arrivals+1)) read written s body=q := by
        rw [split]
        change (if q.stop=.needInput then _ else q)=q
        simp only [done,ite_false]
      refine ⟨0,n,d,after,by omega,by omega,trace.observed,?_,?_,app,header,?_,?_,(by rw [result];exact cursorReg),(by simpa only [Nat.add_zero] using filledWord),firstFrame⟩
      · rw [result];exact terminal_boundary bound done
      · rw [result];exact bodyView
      · rw [result]
        have pos := ChunkBufferSpec.positions wire (filled-read) read written s body
        change q.read≤filled+0
        change read≤q.read ∧ q.read≤read+(filled-read) ∧ _ at pos
        have := h.readFilled
        omega
      · intro narrow
        rw [result]
        have advance := terminal_advance wire (filled-read) read written s body done
        have positions := ChunkBufferSpec.positions wire (filled-read) read written s body
        change q.read=filled+0
        change read<q.read at advance
        change read≤q.read ∧ q.read≤read+(filled-read) ∧ _ at positions
        have := h.readFilled
        omega
    · have need : q.stop=.needInput := Classical.not_not.mp done
      have qr : q.read=filled := by
        have eq := exhausted_read wire (filled-read) read written s body need
        change q.read=read+(filled-read) at eq
        have := h.readFilled
        omega
      have inv : MainChunkLoopInvariant.At B d after sp start q.read q.written filled q.state := by
        change MainChunkBuffered.Boundary B d after sp start filled q at bound
        simpa only [MainChunkBuffered.Boundary,need] using bound
      have len : q.written=start+q.body.length := ChunkBufferSpec.body_length wire _ _ _ _ _ _ hlen
      have planHead := valid filled (by omega) (by omega)
      obtain ⟨e,buf,refill,inv2,rx,stored,app2,refillFrame⟩ := ChunkCallerRefill.contract inv qr (by omega)
        (plan.pending filled) (plan.ready filled) (plan.datum filled) planHead.1 planHead.2.1
      have body2 : Body buf sp start q.body := body_prefix bodyView
        (by have := inv.writtenRead;omega) rx
      have unread2 : Unread wire buf sp q.read (filled+1) := by
        intro k hk he
        have eq : k=filled := by omega
        subst k
        exact stored.trans planHead.2.2
      have result : consume wire (filled-read+(arrivals+1)) read written s body=
          consume wire ((filled+1)-q.read+arrivals) q.read q.written q.state q.body := by
        rw [split]
        change (if q.stop=.needInput then _ else _)=_
        simp only [need,ite_true]
        rw [show (filled+1)-q.read+arrivals=arrivals+1 by omega]
      have complete2 : (consume wire ((filled+1)-q.read+arrivals) q.read q.written q.state q.body).stop≠.needInput := by
        rw [←result];exact complete
      obtain ⟨received,m,final,finalRam,recvBound,hm,rest,terminal,payload,app3,header3,readBound,readExact,finalCursor,finalFilled,restFrame⟩ :=
        ih inv2 (by omega) unread2 body2 len (ChunkReceivePlan.valid_tail valid) complete2
      refine ⟨received+1,n+(25+5*(plan.pending filled).length)+m,final,finalRam,by omega,?_,?_,?_,?_,?_,?_,?_,?_,(by rw [result];exact finalCursor),(by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalFilled),ChunkCallerFrame.trans (ChunkCallerFrame.trans firstFrame refillFrame) restFrame⟩
      · change n+(25+5*(plan.pending filled).length)+m≤
          125*(filled-read+(arrivals+1))+(25+5*(plan.pending filled).length+ChunkReceivePlan.cost plan (filled+1) arrivals)
        rw [qr] at hm
        have sub : filled+1-filled=1 := by omega
        rw [sub] at hm
        omega
      · have combined := (trace.observed.trans refill).trans rest
        simpa only [ChunkReceivePlan.logs,MainChunkRefill.reads,ChunkCallerRefill.reads,List.nil_append,List.append_nil] using combined
      · rw [result];exact terminal
      · rw [result];exact payload
      · exact fun he state hs => app3 he state (app2 he state (app he state hs))
      · intro i
        have mid : buf ((sp+132#32)+BitVec.ofNat 32 i.val)=after ((sp+132#32)+BitVec.ofNat 32 i.val) :=
          rx ⟨i.val,by have := i.isLt;have := inv.startWritten;have := inv.writtenRead;omega⟩
        exact (header3 i).trans (mid.trans (header i))
      · rw [result]
        omega
      · intro narrow
        rw [result]
        have exactReceived := readExact (by omega)
        omega
end E5R.Thermostat.ChunkCallerStreaming
