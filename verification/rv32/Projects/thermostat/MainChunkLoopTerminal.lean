import Projects.thermostat.MainChunkLoopInput
import Projects.thermostat.MainChunkFrame
import Projects.thermostat.ChunkRejectStatus
namespace E5R.Thermostat.MainChunkLoopTerminal
open E5R E5R.Thermostat HttpRequestSpec

theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled)
    (terminal : (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).2=.done ∨
      ∃ status, (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).2=.reject status) :
    ∃ n d after, 81≤n ∧ n≤114 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x8000106c#32 ∧
      ChunkLayout.At after (sp+3680#32) (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).1 ∧
      ChunkDecodedInvariant.Inv 1024 (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).1 (written-start) ∧
      ramRead after (sp+3656#32) .w=BitVec.ofNat 32 (read+1) ∧
      ramRead after (sp+3660#32) .w=BitVec.ofNat 32 written ∧
      (∀ code, (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).2=.reject code →
        (code=400 ∨ code=413) ∧ d.get 27=BitVec.ofNat 32 code) ∧
      MainChunkLayout.At after sp ∧ ViewFrame.Region ram after (sp+132#32) 2048 ∧
      d.get 10=ChunkOutputView.tag (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).2 ∧
      MainChunkCoreFrame.At c d ∧ d.sameCsr c ∧
      (sp=0x80ffeb90#32 → ∀ engineState, AppState.At ram engineState → AppState.At after engineState) := by
  obtain ⟨a,guard,ready,stable1,csr1⟩ := MainChunkLoopInput.contract h available
  obtain ⟨n,d,after,hlo,hn,body,pc,object,inv,index2,cursor2,status2,sp2,fp2,state2,cache2,one2,frame2,tag3,stable2,csr2⟩ :=
    MainChunkOutcome.contract B a ram sp (sp+132#32) (sp+3280#32) (BitVec.ofNat 32 read) 1024#32 s ready h.readWord
      ((stable1 22 (by decide)).trans h.one)
  have frame : MainChunkFrame.BeforeAfter ram after sp := frame2
  have low := MainChunkFrame.low frame
  have donePC : d.pc=0x8000106c#32 := by
    rcases terminal with he|⟨code,he⟩
    all_goals simpa only [show (1024#32).toNat=1024 by decide +kernel,he,MainChunkDispatch.continuation] using pc
  have decoded := ChunkDecodedInvariant.preserved s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024
    (written-start) h.decoder (by decide)
  have decoded' : ChunkDecodedInvariant.Inv 1024 (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).1 (written-start) := by
    rcases terminal with he|⟨code,he⟩
    all_goals simpa only [he,ChunkDecodedInvariant.advance,reduceCtorEq,ite_false] using decoded
  refine ⟨5+n,d,after,by omega,by omega,guard.trans body,donePC,object,decoded',?_,
    (MainChunkFrame.write_cursor frame).trans h.writeWord,?_,MainChunkFrame.layout frame h.layout,?_,
    tag3,MainChunkCoreFrame.trans stable1 stable2,csr2.trans csr1,?_⟩
  · simpa only [BitVec.ofNat_add] using index2
  · intro code he
    have range := ChunkRejectStatus.range s _ 1024 code he
    exact ⟨range,status2 code he (by rcases range with rfl|rfl <;> decide +kernel)⟩
  · intro i
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using low ⟨132+i.val,by omega⟩

  · intro he state hs
    have actualFrame : MainChunkFrame.BeforeAfter ram after 0x80ffeb90#32 := by simpa only [he] using frame
    exact MainChunkFrame.app (before := ram) (after := after) actualFrame state hs

end E5R.Thermostat.MainChunkLoopTerminal
