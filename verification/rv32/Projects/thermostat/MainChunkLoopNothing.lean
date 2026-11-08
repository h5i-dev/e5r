import Projects.thermostat.MainChunkLoopInput
import Projects.thermostat.MainChunkFrame
namespace E5R.Thermostat.MainChunkLoopNothing
open E5R E5R.Thermostat HttpRequestSpec

theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled)
    (nothing : (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).2=.nothing) :
    ∃ n d after, 81≤n ∧ n≤114 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainChunkLoopInvariant.At B d after sp start (read+1) written filled
        (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).1 ∧
      ViewFrame.Region ram after (sp+132#32) 2048 ∧
      (sp=0x80ffeb90#32 → ∀ engineState, AppState.At ram engineState → AppState.At after engineState) := by
  obtain ⟨a,guard,ready,stable1,csr1⟩ := MainChunkLoopInput.contract h available
  obtain ⟨n,d,after,hlo,hn,body,pc,object,inv,index2,cursor2,status2,sp2,fp2,state2,cache2,one2,frame2,tag3,stable2,csr2⟩ :=
    MainChunkOutcome.contract B a ram sp (sp+132#32) (sp+3280#32) (BitVec.ofNat 32 read) 1024#32 s ready h.readWord
      ((stable1 22 (by decide)).trans h.one)
  have core := MainChunkCoreFrame.trans stable1 stable2
  have frame : MainChunkFrame.BeforeAfter ram after sp := frame2
  have low := MainChunkFrame.low frame
  have decoded := ChunkDecodedInvariant.preserved s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024
    (written-start) h.decoder (by decide)
  refine ⟨5+n,d,after,by omega,by omega,guard.trans body,?_,?_,?_⟩
  · constructor
    · simpa only [show (1024#32).toNat=1024 by decide +kernel,nothing,MainChunkDispatch.continuation] using pc
    · exact (core 2 (by decide)).trans h.stackPtr
    · exact (core 8 (by decide)).trans h.framePtr
    · exact (core 23 (by decide)).trans h.statePtr
    · simpa only [BitVec.ofNat_add] using cursor2
    · exact one2
    · exact (core 19 (by decide)).trans h.uart
    · exact MainChunkCoreFrame.masked (csr2.trans csr1) h.masked
    · exact h.stack
    · exact h.align
    · exact MainChunkFrame.layout frame h.layout
    · exact (ViewFrame.word low 3288 (by decide)).trans h.filledWord
    · simpa only [BitVec.ofNat_add] using index2
    · exact (MainChunkFrame.write_cursor frame).trans h.writeWord
    · exact object
    · simpa only [nothing,ChunkDecodedInvariant.advance,reduceCtorEq,ite_false] using decoded
    · exact h.startWritten
    · have := h.writtenRead;omega
    · omega
    · exact h.capacity
  · intro i
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using low ⟨132+i.val,by omega⟩

  · intro he state hs
    have actualFrame : MainChunkFrame.BeforeAfter ram after 0x80ffeb90#32 := by simpa only [he] using frame
    exact MainChunkFrame.app (before := ram) (after := after) actualFrame state hs

end E5R.Thermostat.MainChunkLoopNothing
