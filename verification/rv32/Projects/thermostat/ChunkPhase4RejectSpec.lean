import Projects.thermostat.ChunkPhase4RejectData
import Projects.thermostat.ChunkWordMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkPhase4RejectSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem representation (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (s : CState) (h : ChunkLayout.At ram src s) :
    ChunkLayout.At (ChunkPhase4Reject.memory c ram src dst input limit) dst ({s with phase := 4, size := 0}) ∧
    ChunkLayout.OutAt (ChunkPhase4Reject.memory c ram src dst input limit) dst (.reject 400) := by
  constructor
  · constructor
    · intro i
      have hi := i.isLt
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases hc with h0|h0|h0|h0|h0|h0
      · simp only [h0,show 4*0=0 by decide]
        rw [ChunkPhase4RejectData.word0]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*1=4 by decide]
        rw [ChunkPhase4RejectData.word4]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*2=8 by decide]
        rw [ChunkPhase4RejectData.word8]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨2,by decide⟩
      · simp only [h0,show 4*3=12 by decide]
        rw [ChunkPhase4RejectData.word12]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨3,by decide⟩
      · simp only [h0,show 4*4=16 by decide]
        rw [ChunkPhase4RejectData.word16]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨4,by decide⟩
      · simp only [h0,show 4*5=20 by decide]
        rw [ChunkPhase4RejectData.word20]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨5,by decide⟩
    · rw [ChunkPhase4RejectData.byte24]
      rfl
  · refine ⟨?_,?_,?_⟩
    · rw [ChunkPhase4RejectData.byte32];rfl
    · rw [ChunkPhase4RejectData.byte33];rfl
    · constructor
      · rw [ChunkPhase4RejectData.byte34];rfl
      · rw [ChunkPhase4RejectData.byte35];rfl
end E5R.Thermostat.ChunkPhase4RejectSpec
