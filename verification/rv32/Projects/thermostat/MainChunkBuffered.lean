import Projects.thermostat.MainChunkLoopStep
import Projects.thermostat.ChunkBufferSpec
import Projects.thermostat.ChunkBufferView
namespace E5R.Thermostat.MainChunkBuffered
open E5R E5R.Thermostat HttpRequestSpec
open ChunkBufferSpec ChunkBufferView

def Terminal (ram : Word → BitVec 8) (sp : Word) (start : Nat) (r : ChunkBufferSpec.Result) (d : Core) : Prop :=
  d.pc=0x8000106c#32 ∧ ChunkLayout.At ram (sp+3680#32) r.state ∧
  ChunkDecodedInvariant.Inv 1024 r.state (r.written-start) ∧
  ramRead ram (sp+3656#32) .w=BitVec.ofNat 32 r.read ∧
  ramRead ram (sp+3660#32) .w=BitVec.ofNat 32 r.written ∧ MainChunkLayout.At ram sp ∧
  d.get 2=sp ∧ d.mie_=false ∧
  match r.stop with
  | .reject status => (status=400 ∨ status=413) ∧ d.get 27=BitVec.ofNat 32 status ∧ d.get 10=3#32
  | .done => d.get 10=2#32
  | .needInput => False

def Boundary (B : Board) (d : Core) (ram : Word → BitVec 8) (sp : Word)
    (start filled : Nat) (r : ChunkBufferSpec.Result) : Prop :=
  match r.stop with
  | .needInput => MainChunkLoopInvariant.At B d ram sp start r.read r.written filled r.state
  | .done | .reject _ => Terminal ram sp start r d

theorem terminal {B c ram sp start read written filled s d after s' out}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (hs : MainChunkLoopStep.next ram sp read s=(s',out))
    (hp : MainChunkLoopStep.Finished c ram sp start read written s d after)
    (ht : out=.done ∨ ∃ status, out=.reject status) :
    Boundary B d after sp start filled
      ⟨read+1,written,s',[],match out with | .reject status => .reject status | _ => .done⟩ := by
  rcases hp with ⟨pc,obj,inv,rd,wr,status,layout,rx,tag,core,csr,app⟩
  rw [hs] at obj inv status tag
  have st := (core 2 (by decide)).trans h.stackPtr
  have mask := MainChunkCoreFrame.masked csr h.masked
  rcases ht with rfl|⟨code,rfl⟩
  · exact ⟨pc,obj,inv,rd,wr,layout,st,mask,tag⟩
  · exact ⟨pc,obj,inv,rd,wr,layout,st,mask,(status code rfl).1,(status code rfl).2,tag⟩

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
      ViewFrame.Region ram after (sp+132#32) start := by
  induction fuel generalizing c ram read written s body with
  | zero =>
    exact ⟨0,c,ram,by omega,.refl _,h,hb,hu,(fun _ _ hs => hs),fun _ => rfl⟩
  | succ fuel ih =>
    have startBound : start≤2048 := by
      have := h.startWritten;have := h.writtenRead;have := h.readFilled;have := h.capacity;omega
    have available : read<filled := by omega
    have hbyte : MainChunkLoopStep.byte ram sp read=wire read := hu read (by omega) available
    obtain ⟨n,d,after,hlo,hn,trace,post⟩ := MainChunkLoopStep.contract h available
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
        obtain ⟨m,e,final,hm,rest,bound,bodyView,unread,app2,header2⟩ :=
          ih inv (by omega) hu' hb' hlen
        refine ⟨n+m,e,final,by omega,trace.trans rest,?_,?_,?_,?_,?_⟩
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
        obtain ⟨m,e,final,hm,rest,bound,bodyView,unread,app2,header2⟩ :=
          ih inv (by omega) hu' hb' len'
        refine ⟨n+m,e,final,by omega,trace.trans rest,?_,?_,?_,?_,?_⟩
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
        refine ⟨n,d,after,by omega,trace,?_,?_,?_,app,ViewFrame.shrink rx startBound⟩
        · simpa only [consume,hs,Boundary,Terminal] using finish
        · simpa only [consume,hs] using body_frame hb hlen (by have := h.writtenRead;have := h.readFilled;have := h.capacity;omega) rx
        · simpa only [consume,hs] using unread_frame hu rx h.capacity
      | reject code =>
        have finish := terminal h hs' hh (Or.inr ⟨code,rfl⟩)
        rcases hh with ⟨pc,obj,inv,rd,wr,status,layout,rx,tag,core,csr,app⟩
        refine ⟨n,d,after,by omega,trace,?_,?_,?_,app,ViewFrame.shrink rx startBound⟩
        · simpa only [consume,hs,Boundary,Terminal] using finish
        · simpa only [consume,hs] using body_frame hb hlen (by have := h.writtenRead;have := h.readFilled;have := h.capacity;omega) rx
        · simpa only [consume,hs] using unread_frame hu rx h.capacity

/-- Consume all currently buffered input. Exhaustion leaves the actual cursor
    at filled; terminal cases expose the real status/tag and persisted state. -/
theorem all_buffered (wire : Nat → BitVec 8)
    {B c ram sp start read written filled s body}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (hu : Unread wire ram sp read filled) (hb : Body ram sp start body)
    (hlen : written=start+body.length) :
    let r := consume wire (filled-read) read written s body
    ∃ n d after, n≤125*(filled-read) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Boundary B d after sp start filled r ∧ Body after sp start r.body ∧
      Unread wire after sp r.read filled ∧ MainChunkLoopStep.AppFrame ram after sp ∧
      ViewFrame.Region ram after (sp+132#32) start ∧ r.body.length≤1024 ∧ (r.stop=.needInput → r.read=filled) ∧
      (∀ k e reads evs, k<n → Observed.Steps B img k ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hn,trace,bound,bodyView,unread,app,header⟩ :=
    contract wire (filled-read) h (by have := h.readFilled;omega) hu hb hlen
  have count : written-start=body.length := by omega
  have decoded : ChunkDecodedInvariant.Inv 1024 s body.length := by rw [←count];exact h.decoder
  refine ⟨n,d,after,hn,Interrupt.close trace.det h.masked,bound,bodyView,unread,app,header,
    ChunkBufferSpec.decoded_length wire _ _ _ _ _ decoded,?_,?_⟩
  · intro he
    have eq := exhausted_read wire (filled-read) read written s body he
    have := h.readFilled
    omega
  · exact fun _ _ _ _ hk actual => QuietPrefix.safe trace h.masked hk actual

end E5R.Thermostat.MainChunkBuffered
