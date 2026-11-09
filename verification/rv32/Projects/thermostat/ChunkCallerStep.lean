import Projects.thermostat.ChunkCallerNothing
import Projects.thermostat.ChunkCallerData
import Projects.thermostat.ChunkCallerTerminal
import Projects.thermostat.MainChunkLoopStep
set_option autoImplicit false
namespace E5R.Thermostat.ChunkCallerStep
open E5R E5R.Thermostat HttpRequestSpec MainChunkLoopStep

/-- Same complete byte transition, with caller facts retained for its actual
    error/success continuation instead of postulated at that boundary. -/
theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled) :
    ∃ n d after, 81≤n ∧ n≤125 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post B c ram sp start read written filled s d after ∧ d.get 24=BitVec.ofNat 32 (read+1) ∧ ramRead after (sp+3288#32) .w=BitVec.ofNat 32 filled ∧ ChunkCallerFrame.At c d ram after sp := by
  cases he : (next ram sp read s).2 with
  | nothing =>
    obtain ⟨n,d,after,hlo,hn,trace,inv,rx,app,frame⟩ := ChunkCallerNothing.contract h available he
    refine ⟨n,d,after,hlo,by omega,trace,?_,inv.cursor,inv.filledWord,frame⟩
    simp only [Post,he]
    exact ⟨inv,rx,app⟩
  | data =>
    obtain ⟨n,d,after,hlo,hn,trace,inv,stored,rx,app,frame⟩ := ChunkCallerData.contract h available he
    refine ⟨n,d,after,by omega,hn,trace,?_,inv.cursor,inv.filledWord,frame⟩
    simp only [Post,he]
    exact ⟨inv,stored,rx,app⟩
  | done =>
    obtain ⟨n,d,after,hlo,hn,trace,pc,obj,inv,rd,wr,status,layout,rx,tag,core,csr,app,cursorReg,filledWord,frame⟩ :=
      ChunkCallerTerminal.contract h available (Or.inl he)
    refine ⟨n,d,after,hlo,by omega,trace,?_,cursorReg,filledWord,frame⟩
    simp only [Post,he]
    exact ⟨pc,obj,inv,rd,wr,status,layout,rx,tag,core,csr,app⟩
  | reject status =>
    obtain ⟨n,d,after,hlo,hn,trace,pc,obj,inv,rd,wr,error,layout,rx,tag,core,csr,app,cursorReg,filledWord,frame⟩ :=
      ChunkCallerTerminal.contract h available (Or.inr ⟨status,he⟩)
    refine ⟨n,d,after,hlo,by omega,trace,?_,cursorReg,filledWord,frame⟩
    simp only [Post,he]
    exact ⟨pc,obj,inv,rd,wr,error,layout,rx,tag,core,csr,app⟩
end E5R.Thermostat.ChunkCallerStep
