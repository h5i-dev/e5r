import Projects.thermostat.ChunkSizeAcceptData
import Projects.thermostat.ChunkCapacityMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkSizeAcceptSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem representation (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (s : CState) (h : ChunkLayout.At ram src s) (hbound : s.total+s.size<4294967296) :
    ChunkLayout.At (ChunkSizeAccept.memory c ram src dst input limit) dst ({s with phase := 1, total := s.total+s.size}) ∧
    ChunkLayout.OutAt (ChunkSizeAccept.memory c ram src dst input limit) dst (.nothing) := by
  constructor
  · constructor
    · intro i
      have hi := i.isLt
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases hc with h0|h0|h0|h0|h0|h0
      · simp only [h0,show 4*0=0 by decide]
        rw [ChunkSizeAcceptData.word0]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨0,by decide⟩
      · simp only [h0,show 4*1=4 by decide]
        rw [ChunkSizeAcceptData.word4]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨1,by decide⟩
      · simp only [h0,show 4*2=8 by decide]
        rw [ChunkSizeAcceptData.word8]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨2,by decide⟩
      · simp only [h0,show 4*3=12 by decide]
        rw [ChunkSizeAcceptData.word12]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨3,by decide⟩
      · simp only [h0,show 4*4=16 by decide]
        rw [ChunkSizeAcceptData.word16]
        simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read16 h]
        rw [ChunkSizeMath.add]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*5=20 by decide]
        rw [ChunkSizeAcceptData.word20]
        simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read16 h,ChunkMath.read20 h]
        rw [ChunkSizeMath.no_carry s.total s.size hbound]
        simp [ChunkLayout.words,h0,alu]
    · rw [ChunkSizeAcceptData.byte24]
      rfl
  · refine ⟨?_,?_,?_⟩
    · rw [ChunkSizeAcceptData.byte32];rfl
    · rw [ChunkSizeAcceptData.byte33];rfl
    · trivial
end E5R.Thermostat.ChunkSizeAcceptSpec
