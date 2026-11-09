import Projects.thermostat.ChunkCallerStreaming
namespace E5R.Thermostat.ChunkCallerPump
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec ChunkBufferView MainChunkStreaming ChunkCallerStreaming
abbrev B := UartPlatform.board

/-- With at most one buffered UART byte, the decoder always consumes it or
    waits after consuming the entire supplied prefix. No zero-leftover premise. -/
theorem buffer_end (wire : Nat → BitVec 8) (read written filled : Nat) (s : CState) (body : List (BitVec 8))
    (ordered : read≤filled) (narrow : filled≤read+1) :
    (consume wire (filled-read) read written s body).read=filled := by
  by_cases done : (consume wire (filled-read) read written s body).stop≠.needInput
  · have advance := terminal_advance wire (filled-read) read written s body done
    have positions := ChunkBufferSpec.positions wire (filled-read) read written s body
    omega
  · have pending : (consume wire (filled-read) read written s body).stop=.needInput := Classical.not_not.mp done
    have exhausted := ChunkBufferSpec.exhausted_read wire (filled-read) read written s body pending
    omega

/-- A supplied finite logical UART prefix either reaches the real decoder
    terminal or leaves the actual body loop ready for more bytes. Completeness
    of the request is not assumed. This is the partial/capacity-refusal edge. -/
theorem contract (wire : Nat → BitVec 8) (plan : ChunkReceivePlan.Plan) (arrivals : Nat)
    {c ram sp start read written filled s body}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (space : filled+arrivals≤2048)
    (hu : Unread wire ram sp read filled) (hb : Body ram sp start body)
    (hlen : written=start+body.length)
    (valid : ChunkReceivePlan.Valid plan wire filled arrivals) :
    let r := consume wire (filled-read+arrivals) read written s body
    ∃ received n d after, received≤arrivals ∧
      n≤125*(filled-read+arrivals)+ChunkReceivePlan.cost plan filled arrivals ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (ChunkReceivePlan.logs plan filled received) [] ∧
      MainChunkBuffered.Boundary B d after sp start (filled+received) r ∧ Body after sp start r.body ∧
      Unread wire after sp r.read (filled+received) ∧
      MainChunkLoopStep.AppFrame ram after sp ∧ ViewFrame.Region ram after (sp+132#32) start ∧
      r.read≤filled+received ∧ (filled≤read+1 → r.read=filled+received) ∧
      d.get 24=BitVec.ofNat 32 r.read ∧ ramRead after (sp+3288#32) .w=BitVec.ofNat 32 (filled+received) ∧ ChunkCallerFrame.At c d ram after sp := by
  induction arrivals generalizing c ram read written filled s body with
  | zero =>
    obtain ⟨n,d,after,hn,trace,bound,bodyView,unread,app,header,cursorReg,filledWord,firstFrame⟩ :=
      ChunkCallerBuffered.contract wire (filled-read) h (by have := h.readFilled;omega) hu hb hlen
    refine ⟨0,n,d,after,by omega,by simpa only [Nat.add_zero,ChunkReceivePlan.cost] using hn,
      trace.observed,(by simpa only [Nat.add_zero] using bound),bodyView,(by simpa only [Nat.add_zero] using unread),app,header,?_,?_,(by simpa only [Nat.add_zero] using cursorReg),(by simpa only [Nat.add_zero] using filledWord),firstFrame⟩
    · have pos := ChunkBufferSpec.positions wire (filled-read) read written s body
      have := h.readFilled
      simp only [Nat.add_zero]
      omega
    · intro narrow
      simpa only [Nat.add_zero] using buffer_end wire read written filled s body h.readFilled narrow
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
      refine ⟨0,n,d,after,by omega,by omega,trace.observed,?_,?_,?_,app,header,?_,?_,(by rw [result];exact cursorReg),(by simpa only [Nat.add_zero] using filledWord),firstFrame⟩
      · rw [result];simpa only [Nat.add_zero] using bound
      · rw [result];exact bodyView
      · rw [result];simpa only [Nat.add_zero] using unread
      · rw [result]
        have pos := ChunkBufferSpec.positions wire (filled-read) read written s body
        change q.read≤filled+0
        change read≤q.read ∧ q.read≤read+(filled-read) ∧ _ at pos
        have := h.readFilled
        omega
      · intro narrow
        rw [result]
        simpa only [Nat.add_zero] using buffer_end wire read written filled s body h.readFilled narrow
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
      obtain ⟨received,m,final,finalRam,recvBound,hm,rest,terminal,payload,unreadFinal,app3,header3,readBound,readExact,finalCursor,finalFilled,restFrame⟩ :=
        ih inv2 (by omega) unread2 body2 len (ChunkReceivePlan.valid_tail valid)
      refine ⟨received+1,n+(25+5*(plan.pending filled).length)+m,final,finalRam,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,(by rw [result];exact finalCursor),(by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalFilled),ChunkCallerFrame.trans (ChunkCallerFrame.trans firstFrame refillFrame) restFrame⟩
      · change n+(25+5*(plan.pending filled).length)+m≤
          125*(filled-read+(arrivals+1))+(25+5*(plan.pending filled).length+ChunkReceivePlan.cost plan (filled+1) arrivals)
        rw [qr] at hm
        have sub : filled+1-filled=1 := by omega
        rw [sub] at hm
        omega
      · have combined := (trace.observed.trans refill).trans rest
        simpa only [ChunkReceivePlan.logs,MainChunkRefill.reads,ChunkCallerRefill.reads,List.nil_append,List.append_nil] using combined
      · rw [result]
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using terminal
      · rw [result];exact payload
      · rw [result]
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using unreadFinal
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
end E5R.Thermostat.ChunkCallerPump
