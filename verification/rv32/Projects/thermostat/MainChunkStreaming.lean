import Projects.thermostat.MainChunkBuffered
import Projects.thermostat.ChunkBufferConcat
import Projects.thermostat.ChunkReceivePlan
namespace E5R.Thermostat.MainChunkStreaming
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec ChunkBufferView
abbrev B := UartPlatform.board

theorem terminal_boundary {c ram sp start filled r}
    (h : MainChunkBuffered.Boundary B c ram sp start filled r) (done : r.stop≠.needInput) :
    MainChunkBuffered.Terminal ram sp start r c := by
  cases he : r.stop with
  | needInput => exact False.elim (done he)
  | done => simpa only [MainChunkBuffered.Boundary,he] using h
  | reject status => simpa only [MainChunkBuffered.Boundary,he] using h

theorem body_prefix {before after sp start body filled}
    (hb : Body before sp start body) (bound : start+body.length≤filled)
    (rx : ViewFrame.Region before after (sp+132#32) filled) : Body after sp start body := by
  intro i
  rw [ChunkBufferView.address,rx ⟨start+i.val,by have := i.isLt;omega⟩]
  simpa only [ChunkBufferView.address] using hb i

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
      r.read≤filled+received := by
  induction arrivals generalizing c ram read written filled s body with
  | zero =>
    obtain ⟨n,d,after,hn,trace,bound,bodyView,unread,app,header⟩ :=
      MainChunkBuffered.contract wire (filled-read) h (by have := h.readFilled;omega) hu hb hlen
    have done : (consume wire (filled-read) read written s body).stop≠.needInput := by simpa only [Nat.add_zero] using complete
    refine ⟨0,n,d,after,by omega,by simpa only [Nat.add_zero,ChunkReceivePlan.cost] using hn,
      trace.observed,terminal_boundary bound done,bodyView,app,header,?_⟩
    have pos := ChunkBufferSpec.positions wire (filled-read) read written s body
    have := h.readFilled
    simp only [Nat.add_zero]
    omega
  | succ arrivals ih =>
    let q := consume wire (filled-read) read written s body
    obtain ⟨n,d,after,hn,trace,bound,bodyView,unread,app,header⟩ :=
      MainChunkBuffered.contract wire (filled-read) h (by have := h.readFilled;omega) hu hb hlen
    have split := ChunkBufferConcat.consume_add wire (filled-read) (arrivals+1) read written s body
    by_cases done : q.stop≠.needInput
    · have result : consume wire (filled-read+(arrivals+1)) read written s body=q := by
        rw [split]
        change (if q.stop=.needInput then _ else q)=q
        simp only [done,ite_false]
      refine ⟨0,n,d,after,by omega,by omega,trace.observed,?_,?_,app,header,?_⟩
      · rw [result];exact terminal_boundary bound done
      · rw [result];exact bodyView
      · rw [result]
        have pos := ChunkBufferSpec.positions wire (filled-read) read written s body
        change q.read≤filled+0
        change read≤q.read ∧ q.read≤read+(filled-read) ∧ _ at pos
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
      obtain ⟨e,buf,refill,inv2,rx,stored,app2⟩ := MainChunkRefill.contract inv qr (by omega)
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
      obtain ⟨received,m,final,finalRam,recvBound,hm,rest,terminal,payload,app3,header3,readBound⟩ :=
        ih inv2 (by omega) unread2 body2 len (ChunkReceivePlan.valid_tail valid) complete2
      refine ⟨received+1,n+(25+5*(plan.pending filled).length)+m,final,finalRam,by omega,?_,?_,?_,?_,?_,?_,?_⟩
      · change n+(25+5*(plan.pending filled).length)+m≤
          125*(filled-read+(arrivals+1))+(25+5*(plan.pending filled).length+ChunkReceivePlan.cost plan (filled+1) arrivals)
        rw [qr] at hm
        have sub : filled+1-filled=1 := by omega
        rw [sub] at hm
        omega
      · have combined := (trace.observed.trans refill).trans rest
        simpa only [ChunkReceivePlan.logs,List.nil_append,List.append_nil] using combined
      · rw [result];exact terminal
      · rw [result];exact payload
      · exact fun he state hs => app3 he state (app2 he state (app he state hs))
      · intro i
        have mid : buf ((sp+132#32)+BitVec.ofNat 32 i.val)=after ((sp+132#32)+BitVec.ofNat 32 i.val) :=
          rx ⟨i.val,by have := i.isLt;have := inv.startWritten;have := inv.writtenRead;omega⟩
        exact (header3 i).trans (mid.trans (header i))
      · rw [result]
        omega
end E5R.Thermostat.MainChunkStreaming
