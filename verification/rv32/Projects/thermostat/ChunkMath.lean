import Projects.thermostat.ChunkWordMath
namespace E5R.Thermostat.ChunkMath
open E5R E5R.Thermostat HttpRequestSpec

theorem read0 {ram src s} (h : ChunkLayout.At ram src s) :
    ramRead ram (src+0#32) .w=BitVec.ofNat 32 s.size := by
  simpa [ChunkLayout.words] using h.1 ⟨0,by decide⟩
theorem read4 {ram src s} (h : ChunkLayout.At ram src s) :
    ramRead ram (src+4#32) .w=0#32 := by
  simpa [ChunkLayout.words] using h.1 ⟨1,by decide⟩
theorem read8 {ram src s} (h : ChunkLayout.At ram src s) :
    ramRead ram (src+8#32) .w=BitVec.ofNat 32 s.digits := by
  simpa [ChunkLayout.words] using h.1 ⟨2,by decide⟩
theorem read12 {ram src s} (h : ChunkLayout.At ram src s) :
    ramRead ram (src+12#32) .w=0#32 := by
  simpa [ChunkLayout.words] using h.1 ⟨3,by decide⟩
theorem read16 {ram src s} (h : ChunkLayout.At ram src s) :
    ramRead ram (src+16#32) .w=BitVec.ofNat 32 s.total := by
  simpa [ChunkLayout.words] using h.1 ⟨4,by decide⟩
theorem read20 {ram src s} (h : ChunkLayout.At ram src s) :
    ramRead ram (src+20#32) .w=0#32 := by
  simpa [ChunkLayout.words] using h.1 ⟨5,by decide⟩

theorem word_eq (a b : Nat) (ha : a<4294967296) (hb : b<4294967296) :
    (BitVec.ofNat 32 a=BitVec.ofNat 32 b) ↔ a=b := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using h'
  · intro h;rw [h]

theorem eq_guard (a b : Nat) (ha : a<4294967296) (hb : b<4294967296) :
    taken .eq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [taken,beq_iff_eq,decide_eq_true_eq,word_eq a b ha hb]

theorem ne_guard (a b : Nat) (ha : a<4294967296) (hb : b<4294967296) :
    taken .ne (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a≠b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [taken,bne_iff_ne,decide_eq_true_eq,ne_eq,word_eq a b ha hb]

end E5R.Thermostat.ChunkMath
