import Projects.thermostat.MainChunkLoopInput
import Projects.thermostat.MainChunkFrame
import Projects.thermostat.MainChunkDataFrame
namespace E5R.Thermostat.MainChunkLoopData
open E5R E5R.Thermostat HttpRequestSpec

theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled)
    (data : (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).2=.data) :
    ∃ n d after, 92≤n ∧ n≤125 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainChunkLoopInvariant.At B d after sp start (read+1) (written+1) filled
        (chunkStep s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024).1 ∧
      after ((sp+132#32)+BitVec.ofNat 32 written)=ram ((sp+132#32)+BitVec.ofNat 32 read) ∧
      (∀ k : Nat, k<2048 → k≠written →
        after ((sp+132#32)+BitVec.ofNat 32 k)=ram ((sp+132#32)+BitVec.ofNat 32 k)) ∧
      (sp=0x80ffeb90#32 → ∀ engineState, AppState.At ram engineState → AppState.At after engineState) := by
  obtain ⟨a,guard,ready,stable1,csr1⟩ := MainChunkLoopInput.contract h available
  obtain ⟨n,z,before,hlo,hn,body,pc,object,inv,index2,cursor2,status2,sp2,fp2,state2,cache2,one2,frame2,tag3,stable2,csr2⟩ :=
    MainChunkOutcome.contract B a ram sp (sp+132#32) (sp+3280#32) (BitVec.ofNat 32 read) 1024#32 s ready h.readWord
      ((stable1 22 (by decide)).trans h.one)
  have core := MainChunkCoreFrame.trans stable1 stable2
  have frame : MainChunkFrame.BeforeAfter ram before sp := frame2
  have low := MainChunkFrame.low frame
  have layout := MainChunkFrame.layout frame h.layout
  have wb : written<2048 := MainChunkLoopInvariant.write_bound h available
  have w32 : written<4294967296 := by omega
  have wb' : (BitVec.ofNat 32 written).toNat<2048 := by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt w32] using wb
  have pcData : z.pc=0x80000f6a#32 := by
    simpa only [show (1024#32).toNat=1024 by decide +kernel,data,MainChunkDispatch.continuation] using pc
  let value := BitVec.ofNat 32 (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat
  obtain ⟨d,append,pc3,w3,rx3,r3,saved3,csr3⟩ := MainChunkDataAppend.contract B z before sp
    (BitVec.ofNat 32 written) (BitVec.ofNat 32 read+1#32) value fp2 cache2 h.stack h.align wb'
    ((MainChunkFrame.write_cursor frame).trans h.writeWord) index2 layout.capacity layout.rx pcData
  let after := MainChunkDataAppend.memory before sp (BitVec.ofNat 32 written) (BitVec.ofNat 32 read+1#32) value
  have decoded := ChunkDecodedInvariant.preserved s (ram ((sp+132#32)+BitVec.ofNat 32 read)).toNat 1024
    (written-start) h.decoder (by decide)
  have length : written+1-start=(written-start)+1 := by have := h.startWritten;omega
  refine ⟨5+n+11,d,after,by omega,by omega,(guard.trans body).trans append,?_,?_,?_,?_⟩
  · constructor
    · exact pc3
    · exact (saved3 2 (by decide) (by decide) (by decide)).trans sp2
    · exact (saved3 8 (by decide) (by decide) (by decide)).trans fp2
    · exact (saved3 23 (by decide) (by decide) (by decide)).trans state2
    · simpa only [BitVec.ofNat_add] using r3
    · exact (saved3 22 (by decide) (by decide) (by decide)).trans one2
    · exact (saved3 19 (by decide) (by decide) (by decide)).trans ((core 19 (by decide)).trans h.uart)
    · exact MainChunkCoreFrame.masked (csr3.trans (csr2.trans csr1)) h.masked
    · exact h.stack
    · exact h.align
    · exact MainChunkDataFrame.layout wb' layout
    · exact (MainChunkDataFrame.word before sp _ _ value wb' 3288 (by decide) (by decide)).trans
        ((ViewFrame.word low 3288 (by decide)).trans h.filledWord)
    · simpa only [BitVec.ofNat_add] using (MainChunkDataFrame.read_cursor before sp _ _ value wb').trans index2
    · simpa only [BitVec.ofNat_add] using MainChunkDataMemory.cursor before sp (BitVec.ofNat 32 written) _ value
    · exact MainChunkDataFrame.state wb' object
    · simpa only [data,ChunkDecodedInvariant.advance,ite_true,length] using decoded
    · have := h.startWritten;omega
    · have := h.writtenRead;omega
    · omega
    · exact h.capacity
  · exact MainChunkDataMemory.stored_byte before sp (BitVec.ofNat 32 written) _
      (ram ((sp+132#32)+BitVec.ofNat 32 read)) wb'
  · intro k hk hne
    calc
      after ((sp+132#32)+BitVec.ofNat 32 k)=before ((sp+132#32)+BitVec.ofNat 32 k) :=
        MainChunkDataMemory.rx_other before sp _ _ value k wb' hk (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt w32] using hne)
      _=ram ((sp+132#32)+BitVec.ofNat 32 k) := by
        simpa only [BitVec.ofNat_add,BitVec.add_assoc] using low ⟨132+k,by omega⟩

  · intro he state hs
    have actualFrame : MainChunkFrame.BeforeAfter ram before 0x80ffeb90#32 := by simpa only [he] using frame
    have app1 := MainChunkFrame.app (before := ram) (after := before) actualFrame state hs
    change AppState.At (MainChunkDataAppend.memory before sp _ _ value) state
    rw [he]
    exact MainChunkDataFrame.app before _ _ value state wb' app1

end E5R.Thermostat.MainChunkLoopData
