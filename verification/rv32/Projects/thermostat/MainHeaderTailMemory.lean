import Projects.thermostat.MainHeaderTail
import Projects.thermostat.MainHeaderLayout
namespace E5R.Thermostat.MainHeaderTailMemory
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (fp filled x : Word)
    (count : ∀ i : Fin 4, x≠(fp+84#32)+BitVec.ofNat 32 i.val) (poll : x≠fp+464#32) :
    MainHeaderTail.memory ram fp filled x=ram x := by
  unfold MainHeaderTail.memory
  simp only [BitVec.add_zero]
  rw [StoreBytes.frame _ _ _ _ .w count]
  apply StoreBytes.frame _ _ _ _ .b
  intro i
  have hz : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
  simpa only [hz,BitVec.add_zero] using poll

theorem word_frame (ram : Word → BitVec 8) (fp filled : Word) (off : Nat)
    (bound : off+4≤464) (apart : off+4≤84 ∨ 88≤off) :
    ramRead (MainHeaderTail.memory ram fp filled) (fp+BitVec.ofNat 32 off) .w=ramRead ram (fp+BitVec.ofNat 32 off) .w := by
  unfold MainHeaderTail.memory
  simp only [BitVec.add_zero]
  rw [FrameOffsets.word _ fp (filled+1#32) off 84 .w (by omega) (by decide) apart]
  exact FrameOffsets.word ram fp 1#32 off 464 .b (by omega) (by decide) (Or.inl bound)

theorem count (ram : Word → BitVec 8) (fp filled : Word) :
    ramRead (MainHeaderTail.memory ram fp filled) (fp+84#32) .w=filled+1#32 := by
  unfold MainHeaderTail.memory
  simp only [BitVec.add_zero]
  exact ramRead_ramWrite_w _ _ _

theorem layout {ram : Word → BitVec 8} {filled : Nat} (h : MainHeaderLayout.At ram filled) (room : filled<2048) :
    MainHeaderLayout.At (MainHeaderTail.memory ram 0x80fff814#32 (BitVec.ofNat 32 filled)) (filled+1) := by
  have word (off : Nat) (bound : off+4≤464) (apart : off+4≤84 ∨ 88≤off) := word_frame ram 0x80fff814#32 (BitVec.ofNat 32 filled) off bound apart
  have head : MainHeadLayout.At (MainHeaderTail.memory ram 0x80fff814#32 (BitVec.ofNat 32 filled)) :=
    ⟨(word 108 (by decide) (Or.inr (by decide))).trans h.head.rx,
      (word 432 (by decide) (Or.inr (by decide))).trans h.head.config,
      (word 76 (by decide) (Or.inl (by decide))).trans h.head.headLimit,
      (word 80 (by decide) (Or.inl (by decide))).trans h.head.bodyLimit⟩
  refine ⟨head,by omega,(word 112 (by decide) (Or.inr (by decide))).trans h.capacity,
    (word 436 (by decide) (Or.inr (by decide))).trans h.filledPtr,?_,(word 440 (by decide) (Or.inr (by decide))).trans h.uartPtr⟩
  exact (count ram 0x80fff814#32 (BitVec.ofNat 32 filled)).trans (by rw [←BitVec.ofNat_add])
end E5R.Thermostat.MainHeaderTailMemory
