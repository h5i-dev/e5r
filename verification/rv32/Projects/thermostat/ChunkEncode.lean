import Projects.thermostat.ChunkLayout
import Projects.thermostat.PackedBytes
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkEncode
open E5R E5R.Thermostat HttpRequestSpec

/-- A satisfiable input representation; padding retains arbitrary old bytes. -/
def memory (ram : Word → BitVec 8) (p : Word) (s : CState) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (p+0#32) (BitVec.ofNat 32 s.size) .w) (p+4#32) (0#32) .w) (p+8#32) (BitVec.ofNat 32 s.digits) .w) (p+12#32) (0#32) .w) (p+16#32) (BitVec.ofNat 32 s.total) .w) (p+20#32) (0#32) .w) (p+24#32) (BitVec.ofNat 32 s.phase) .b

theorem at_state (ram : Word → BitVec 8) (p : Word) (s : CState) (hp : s.phase<256) :
    ChunkLayout.At (memory ram p s) p s := by
  constructor
  · intro i
    have hi := i.isLt
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
    rcases hc with h0|h0|h0|h0|h0|h0
    · simp only [h0,show 4*0=0 by decide]
      unfold memory
      rw [ChunkLayout.read_away _ p _ 0 24 .b (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 0 20 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 0 16 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 0 12 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 0 8 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 0 4 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,h0]
    · simp only [h0,show 4*1=4 by decide]
      unfold memory
      rw [ChunkLayout.read_away _ p _ 4 24 .b (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 4 20 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 4 16 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 4 12 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 4 8 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,h0]
    · simp only [h0,show 4*2=8 by decide]
      unfold memory
      rw [ChunkLayout.read_away _ p _ 8 24 .b (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 8 20 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 8 16 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 8 12 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,h0]
    · simp only [h0,show 4*3=12 by decide]
      unfold memory
      rw [ChunkLayout.read_away _ p _ 12 24 .b (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 12 20 .w (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 12 16 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,h0]
    · simp only [h0,show 4*4=16 by decide]
      unfold memory
      rw [ChunkLayout.read_away _ p _ 16 24 .b (by decide) (by decide) (by decide)]
      rw [ChunkLayout.read_away _ p _ 16 20 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,h0]
    · simp only [h0,show 4*5=20 by decide]
      unfold memory
      rw [ChunkLayout.read_away _ p _ 20 24 .b (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,h0]
  · unfold memory
    simp only [ramWrite,ramPut_eq]
    rw [PackedBytes.low0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
end E5R.Thermostat.ChunkEncode
