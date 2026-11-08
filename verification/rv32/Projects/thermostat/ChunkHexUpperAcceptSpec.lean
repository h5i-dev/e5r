import Projects.thermostat.ChunkHexUpperAcceptData
import Projects.thermostat.ChunkByteFacts
import Projects.thermostat.ChunkSizeMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkHexUpperAcceptSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem representation (c : Core) (ram : Word → BitVec 8) (src dst limit : Word)
    (s : CState) (b : BitVec 8) (h : ChunkLayout.At ram src s)
    (hb : 65≤b.toNat ∧ b.toNat≤70) (hsize : s.size≤268435455) (hdigits : s.digits<8) :
    ChunkLayout.At (ChunkHexUpperAccept.memory c ram src dst (BitVec.ofNat 32 b.toNat) limit) dst
      ({s with phase := 0, size := s.size*16+hexv b.toNat, digits := s.digits+1}) ∧
    ChunkLayout.OutAt (ChunkHexUpperAccept.memory c ram src dst (BitVec.ofNat 32 b.toNat) limit) dst .nothing := by
  have hv := ChunkByteFacts.upper_value b hb
  have hx : hexv b.toNat<16 := (ChunkByteFacts.classes b).mp (Or.inr (Or.inr hb))
  have hl : s.size<4294967296 := by omega
  constructor
  · constructor
    · intro i
      have hi := i.isLt
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases hc with h0|h0|h0|h0|h0|h0
      · simp only [h0,show 4*0=0 by decide]
        rw [ChunkHexUpperAcceptData.word0]
        simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h]
        rw [hv,ChunkSizeMath.masked _ (by omega),ChunkSizeMath.left4 _ hl]
        rw [ChunkSizeMath.add]
        simp [ChunkLayout.words,h0,Nat.mul_comm,Nat.add_comm]
      · simp only [h0,show 4*1=4 by decide]
        rw [ChunkHexUpperAcceptData.word4]
        simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h]
        rw [hv,ChunkSizeMath.masked _ (by omega),ChunkSizeMath.left4 _ hl]
        rw [ChunkSizeMath.right28_zero _ hsize,
          show alu .sll 0#32 4#32=0#32 by decide +kernel,
          show alu .or 0#32 0#32=0#32 by rfl,
          ChunkSizeMath.no_carry (hexv b.toNat) (16*s.size) (by omega)]
        simp [ChunkLayout.words,h0,alu]
      · simp only [h0,show 4*2=8 by decide]
        rw [ChunkHexUpperAcceptData.word8]
        simp only [ChunkWordMath.extend_word,ChunkMath.read8 h]
        rw [ChunkSizeMath.add]
        simp [ChunkLayout.words,h0]
      · simp only [h0,show 4*3=12 by decide]
        rw [ChunkHexUpperAcceptData.word12]
        simp only [ChunkWordMath.extend_word,ChunkMath.read8 h,ChunkMath.read12 h]
        rw [ChunkSizeMath.add s.digits 1,ChunkNumberMath.less (s.digits+1) 1 (by omega) (by decide)]
        simp [show ¬s.digits+1<1 by omega,ChunkLayout.words,h0,alu]
      · simp only [h0,show 4*4=16 by decide]
        rw [ChunkHexUpperAcceptData.word16]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨4,by decide⟩
      · simp only [h0,show 4*5=20 by decide]
        rw [ChunkHexUpperAcceptData.word20]
        simpa [ChunkWordMath.extend_word,ChunkLayout.words,h0] using h.1 ⟨5,by decide⟩
    · rw [ChunkHexUpperAcceptData.byte24];rfl
  · refine ⟨?_,?_,True.intro⟩
    · rw [ChunkHexUpperAcceptData.byte32];rfl
    · rw [ChunkHexUpperAcceptData.byte33];rfl
end E5R.Thermostat.ChunkHexUpperAcceptSpec
