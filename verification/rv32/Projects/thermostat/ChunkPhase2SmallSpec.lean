import Projects.thermostat.ChunkPhase2SmallData
import Projects.thermostat.ChunkWordMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkPhase2SmallSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem representation (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (s : CState) (h : ChunkLayout.At ram src s) :
    ChunkLayout.At (ChunkPhase2Small.memory c ram src dst input limit) dst ({s with phase := 3, size := 0}) ∧
    ChunkLayout.OutAt (ChunkPhase2Small.memory c ram src dst input limit) dst (.data) := by
  constructor
  · constructor
    · intro i
      have hi := i.isLt
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases hc with h0|h0|h0|h0|h0|h0
      · simp only [h0,show 4*0=0 by decide]
        rw [ChunkPhase2SmallData.word0]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*1=4 by decide]
        rw [ChunkPhase2SmallData.word4]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*2=8 by decide]
        rw [ChunkPhase2SmallData.word8]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨2,by decide⟩
      · simp only [h0,show 4*3=12 by decide]
        rw [ChunkPhase2SmallData.word12]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨3,by decide⟩
      · simp only [h0,show 4*4=16 by decide]
        rw [ChunkPhase2SmallData.word16]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨4,by decide⟩
      · simp only [h0,show 4*5=20 by decide]
        rw [ChunkPhase2SmallData.word20]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨5,by decide⟩
    · rw [ChunkPhase2SmallData.byte24]
      rfl
  · refine ⟨?_,?_,?_⟩
    · rw [ChunkPhase2SmallData.byte32];rfl
    · rw [ChunkPhase2SmallData.byte33];rfl
    · trivial
end E5R.Thermostat.ChunkPhase2SmallSpec
