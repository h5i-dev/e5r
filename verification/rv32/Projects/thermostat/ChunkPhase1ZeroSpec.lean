import Projects.thermostat.ChunkPhase1ZeroData
import Projects.thermostat.ChunkWordMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkPhase1ZeroSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem representation (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (s : CState) (h : ChunkLayout.At ram src s) :
    ChunkLayout.At (ChunkPhase1Zero.memory c ram src dst input limit) dst ({s with phase := 5, digits := 0}) ∧
    ChunkLayout.OutAt (ChunkPhase1Zero.memory c ram src dst input limit) dst (.nothing) := by
  constructor
  · constructor
    · intro i
      have hi := i.isLt
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases hc with h0|h0|h0|h0|h0|h0
      · simp only [h0,show 4*0=0 by decide]
        rw [ChunkPhase1ZeroData.word0]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨0,by decide⟩
      · simp only [h0,show 4*1=4 by decide]
        rw [ChunkPhase1ZeroData.word4]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨1,by decide⟩
      · simp only [h0,show 4*2=8 by decide]
        rw [ChunkPhase1ZeroData.word8]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*3=12 by decide]
        rw [ChunkPhase1ZeroData.word12]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*4=16 by decide]
        rw [ChunkPhase1ZeroData.word16]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨4,by decide⟩
      · simp only [h0,show 4*5=20 by decide]
        rw [ChunkPhase1ZeroData.word20]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨5,by decide⟩
    · rw [ChunkPhase1ZeroData.byte24]
      rfl
  · refine ⟨?_,?_,?_⟩
    · rw [ChunkPhase1ZeroData.byte32];rfl
    · rw [ChunkPhase1ZeroData.byte33];rfl
    · trivial
end E5R.Thermostat.ChunkPhase1ZeroSpec
