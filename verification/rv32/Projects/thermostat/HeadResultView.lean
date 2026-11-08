import Projects.thermostat.HeadResultStore
import Projects.thermostat.HeadIncomplete
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ResponseWordBytes
import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadResultView
open E5R E5R.Thermostat HttpRequestSpec

/-- Only the early variants are covered here. Done requires its complete
    header/span/framing layout proof; it is deliberately not accepted. -/
def At (ram : Word → BitVec 8) (dst : Word) : HeadR → Prop
  | .incomplete => ramRead ram dst .w=3#32 ∧ ramRead ram (dst+4#32) .w=0#32
  | .reject code => code<65536 ∧ ramRead ram dst .w=4#32 ∧ ramRead ram (dst+4#32) .w=0#32 ∧
      extend .h false (ramRead ram (dst+8#32) .h)=BitVec.ofNat 32 code
  | .done _ => False

theorem tag (ram : Word → BitVec 8) (dst tag status : Word) :
    ramRead (HeadResultStore.memory ram dst tag status) dst .w=tag := by
  unfold HeadResultStore.memory
  simp only [BitVec.add_zero]
  have h := FrameOffsets.word (ramWrite (ramWrite ram (dst+0#32) tag .w) (dst+4#32) 0#32 .w)
    dst status 0 8 .h (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at h
  rw [h]
  have h := FrameOffsets.word (ramWrite ram (dst+0#32) tag .w) dst 0#32 0 4 .w (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at h
  rw [h]
  exact ramRead_ramWrite_w _ _ _

theorem zero (ram : Word → BitVec 8) (dst tag status : Word) :
    ramRead (HeadResultStore.memory ram dst tag status) (dst+4#32) .w=0#32 := by
  unfold HeadResultStore.memory
  rw [FrameOffsets.word _ dst status 4 8 .h (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem status (ram : Word → BitVec 8) (dst tag status : Word) (bound : status.toNat<65536) :
    extend .h false (ramRead (HeadResultStore.memory ram dst tag status) (dst+8#32) .h)=status := by
  apply ResponseWordBytes.half _ _ _ bound
  intro i
  have hi := i.isLt
  have cases : i.val=0 ∨ i.val=1 := by omega
  rcases cases with h|h
  · simp only [h,BitVec.add_zero]
    unfold HeadResultStore.memory
    have ne : dst+8#32≠(dst+8#32)+1#32 := by simp [BitVec.self_eq_add_right]
    simp only [ramWrite,ramPut,show (1 : Word)=1#32 by decide +kernel,ite_true,ne,ite_false]
  · simp only [h]
    unfold HeadResultStore.memory
    simp only [ramWrite,ramPut,show (1 : Word)=1#32 by decide +kernel,ite_true]

theorem reject (ram : Word → BitVec 8) (dst : Word) (code : Nat) (bound : code<65536) :
    At (HeadResultStore.memory ram dst 4#32 (BitVec.ofNat 32 code)) dst (.reject code) := by
  exact ⟨bound,tag _ _ _ _,zero _ _ _ _,status _ _ _ _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];exact bound)⟩

theorem incomplete (ram : Word → BitVec 8) (dst : Word) : At (HeadIncomplete.memory ram dst) dst .incomplete := by
  constructor
  · unfold HeadIncomplete.memory
    have h := FrameOffsets.word (ramWrite ram (dst+0#32) 3#32 .w) dst 0#32 0 4 .w (by decide) (by decide) (by decide)
    simp only [BitVec.add_zero] at h ⊢
    rw [h]
    exact ramRead_ramWrite_w _ _ _
  · unfold HeadIncomplete.memory
    exact ramRead_ramWrite_w _ _ _

theorem done_not_covered (ram : Word → BitVec 8) (dst : Word) (head : Head) : ¬At ram dst (.done head) := by
  intro h
  exact h
end E5R.Thermostat.HeadResultView
