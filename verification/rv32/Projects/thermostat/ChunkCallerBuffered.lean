import Projects.thermostat.ChunkCallerStep
import Projects.thermostat.MainChunkBuffered
namespace E5R.Thermostat.ChunkCallerBuffered
open E5R E5R.Thermostat HttpRequestSpec ChunkBufferSpec ChunkBufferView MainChunkBuffered
/-- The actual finite in-place body loop refines a byte-stream consumer.
    Fuel is a supplied buffered prefix, not a UART readiness assumption. -/
theorem contract (wire : Nat → BitVec 8) (fuel : Nat)
    {B c ram sp start read written filled s body}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (fuelBound : read+fuel≤filled)
    (hu : Unread wire ram sp read filled) (hb : Body ram sp start body)
    (hlen : written=start+body.length) :
    let r := consume wire fuel read written s body
    ∃ n d after, n≤125*fuel ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Boundary B d after sp start filled r ∧ Body after sp start r.body ∧
      Unread wire after sp r.read filled ∧ MainChunkLoopStep.AppFrame ram after sp ∧
      ViewFrame.Region ram after (sp+132#32) start ∧ d.get 24=BitVec.ofNat 32 r.read ∧ ramRead after (sp+3288#32) .w=BitVec.ofNat 32 filled ∧ ChunkCallerFrame.At c d ram after sp := by
  induction fuel generalizing c ram read written s body with
  | zero =>
    exact ⟨0,c,ram,by omega,.refl _,h,hb,hu,(fun _ _ hs => hs),(fun _ => rfl),h.cursor,h.filledWord,ChunkCallerFrame.refl c ram sp⟩
  | succ fuel ih =>
    have startBound : start≤2048 := by
      have := h.startWritten;have := h.writtenRead;have := h.readFilled;have := h.capacity;omega
    have available : read<filled := by omega
    have hbyte : MainChunkLoopStep.byte ram sp read=wire read := hu read (by omega) available
    obtain ⟨n,d,after,hlo,hn,trace,post,cursorReg,filledWord,firstFrame⟩ := ChunkCallerStep.contract h available
    cases hs : chunkStep s (wire read).toNat 1024 with
    | mk s' out =>
      have hs' : MainChunkLoopStep.next ram sp read s=(s',out) := by
        simpa only [MainChunkLoopStep.next,hbyte] using hs
      have hh : MainChunkLoopStep.Post B c ram sp start read written filled s d after := post
      simp only [MainChunkLoopStep.Post,hs'] at hh
      cases out with
      | nothing =>
        rcases hh with ⟨inv,rx,app⟩
        have hb' := body_frame hb hlen (by have := h.writtenRead;have := h.readFilled;have := h.capacity;omega) rx
        have hu' := unread_frame hu rx h.capacity
        obtain ⟨m,e,final,hm,rest,bound,bodyView,unread,app2,header2,finalCursor,finalFilled,restFrame⟩ :=
          ih inv (by omega) hu' hb' hlen
        refine ⟨n+m,e,final,by omega,trace.trans rest,?_,?_,?_,?_,?_,(by simpa only [consume,hs] using finalCursor),finalFilled,ChunkCallerFrame.trans firstFrame restFrame⟩
        · simpa only [consume,hs] using bound
        · simpa only [consume,hs] using bodyView
        · simpa only [consume,hs] using unread
        · exact fun he state ha => app2 he state (app he state ha)
        · exact fun i => (header2 i).trans (rx ⟨i.val,by have := i.isLt;omega⟩)
      | data =>
        rcases hh with ⟨inv,stored,other,app⟩
        rw [hbyte] at stored
        have hb' := body_data hb hlen (MainChunkLoopInvariant.write_bound h available) stored other
        have hu' := unread_data hu h.writtenRead h.capacity other
        have len' : written+1=start+(body++[wire read]).length := by
          simp only [List.length_append,List.length_singleton];omega
        obtain ⟨m,e,final,hm,rest,bound,bodyView,unread,app2,header2,finalCursor,finalFilled,restFrame⟩ :=
          ih inv (by omega) hu' hb' len'
        refine ⟨n+m,e,final,by omega,trace.trans rest,?_,?_,?_,?_,?_,(by simpa only [consume,hs] using finalCursor),finalFilled,ChunkCallerFrame.trans firstFrame restFrame⟩
        · simpa only [consume,hs] using bound
        · simpa only [consume,hs] using bodyView
        · simpa only [consume,hs] using unread
        · exact fun he state ha => app2 he state (app he state ha)
        · intro i
          have hi := i.isLt
          have hw := h.startWritten
          exact (header2 i).trans (other i.val (by omega) (by omega))
      | done =>
        have finish := terminal h hs' hh (Or.inl rfl)
        rcases hh with ⟨pc,obj,inv,rd,wr,status,layout,rx,tag,core,csr,app⟩
        refine ⟨n,d,after,by omega,trace,?_,?_,?_,app,ViewFrame.shrink rx startBound,(by simpa only [consume,hs] using cursorReg),filledWord,firstFrame⟩
        · simpa only [consume,hs,Boundary,Terminal] using finish
        · simpa only [consume,hs] using body_frame hb hlen (by have := h.writtenRead;have := h.readFilled;have := h.capacity;omega) rx
        · simpa only [consume,hs] using unread_frame hu rx h.capacity
      | reject code =>
        have finish := terminal h hs' hh (Or.inr ⟨code,rfl⟩)
        rcases hh with ⟨pc,obj,inv,rd,wr,status,layout,rx,tag,core,csr,app⟩
        refine ⟨n,d,after,by omega,trace,?_,?_,?_,app,ViewFrame.shrink rx startBound,(by simpa only [consume,hs] using cursorReg),filledWord,firstFrame⟩
        · simpa only [consume,hs,Boundary,Terminal] using finish
        · simpa only [consume,hs] using body_frame hb hlen (by have := h.writtenRead;have := h.readFilled;have := h.capacity;omega) rx
        · simpa only [consume,hs] using unread_frame hu rx h.capacity

end E5R.Thermostat.ChunkCallerBuffered
