import Projects.thermostat.ChunkHexDecimalSizeRejectData
import Projects.thermostat.ChunkWordMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkHexDecimalSizeRejectSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem representation (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (s : CState) (h : ChunkLayout.At ram src s) :
    ChunkLayout.At (ChunkHexDecimalSizeReject.memory c ram src dst input limit) dst (s) ∧
    ChunkLayout.OutAt (ChunkHexDecimalSizeReject.memory c ram src dst input limit) dst (.reject 400) := by
  constructor
  · constructor
    · intro i
      have hi := i.isLt
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases hc with h0|h0|h0|h0|h0|h0
      · simp only [h0,show 4*0=0 by decide]
        rw [ChunkHexDecimalSizeRejectData.word0]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨0,by decide⟩
      · simp only [h0,show 4*1=4 by decide]
        rw [ChunkHexDecimalSizeRejectData.word4]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨1,by decide⟩
      · simp only [h0,show 4*2=8 by decide]
        rw [ChunkHexDecimalSizeRejectData.word8]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨2,by decide⟩
      · simp only [h0,show 4*3=12 by decide]
        rw [ChunkHexDecimalSizeRejectData.word12]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨3,by decide⟩
      · simp only [h0,show 4*4=16 by decide]
        rw [ChunkHexDecimalSizeRejectData.word16]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨4,by decide⟩
      · simp only [h0,show 4*5=20 by decide]
        rw [ChunkHexDecimalSizeRejectData.word20]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨5,by decide⟩
    · rw [ChunkHexDecimalSizeRejectData.byte24]
      rw [ChunkWordMath.extend_word,ChunkWordMath.first_byte];exact h.2
  · refine ⟨?_,?_,?_⟩
    · rw [ChunkHexDecimalSizeRejectData.byte32];rfl
    · rw [ChunkHexDecimalSizeRejectData.byte33];rfl
    · constructor
      · rw [ChunkHexDecimalSizeRejectData.byte34];rfl
      · rw [ChunkHexDecimalSizeRejectData.byte35];rfl
end E5R.Thermostat.ChunkHexDecimalSizeRejectSpec
