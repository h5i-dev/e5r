import Projects.thermostat.HeadRegionFrame
import Projects.thermostat.MainChunkFrame
import Projects.thermostat.MainChunkDataFrame
import Projects.thermostat.MainChunkRefillFrame
import Projects.thermostat.MainServeLayout
set_option autoImplicit false
namespace E5R.Thermostat.ChunkCallerFrame
open E5R E5R.Thermostat

/-- Exactly the caller facts lost by the old terminal-only chunk interface:
    registers, App/routes/capacity bytes and immutable serve words. Filled84
    is deliberately excluded because real UART refill changes it. -/
structure At (c d : Core) (before after : Word → BitVec 8) (sp : Word) : Prop where
  core : MainChunkCoreFrame.At c d
  low : ViewFrame.Region before after sp 132
  words : ∀ off∈MainServeLayout.slots, ramRead after ((sp+3204#32)+BitVec.ofNat 32 off) .w=
    ramRead before ((sp+3204#32)+BitVec.ofNat 32 off) .w
  futureLow : ViewFrame.Region before after (sp+3204#32) 84
  futureHigh : ViewFrame.Region before after (sp+3292#32) 364
  csr : d.sameCsr c

theorem refl (c : Core) (ram : Word → BitVec 8) (sp : Word) : At c c ram ram sp :=
  ⟨(fun _ _ => rfl),(fun _ => rfl),(fun _ _ => rfl),(fun _ => rfl),(fun _ => rfl),rfl⟩

theorem trans {a b c : Core} {ra rb rc : Word → BitVec 8} {sp : Word}
    (first : At a b ra rb sp) (last : At b c rb rc sp) : At a c ra rc sp :=
  ⟨MainChunkCoreFrame.trans first.core last.core,HeadRegionFrame.trans first.low last.low,
    (fun off safe => (last.words off safe).trans (first.words off safe)),HeadRegionFrame.trans first.futureLow last.futureLow,
    HeadRegionFrame.trans first.futureHigh last.futureHigh,last.csr.trans first.csr⟩

theorem committed {c d : Core} {before after : Word → BitVec 8} {sp : Word}
    (core : MainChunkCoreFrame.At c d) (memory : MainChunkFrame.BeforeAfter before after sp)
    (csr : d.sameCsr c) : At c d before after sp := by
  refine ⟨core,ViewFrame.shrink (MainChunkFrame.low memory) (by decide),?_,
    HeadRegionFrame.sub (MainChunkFrame.low memory) 3204 84 (by decide),
    HeadRegionFrame.sub (MainChunkFrame.low memory) 3292 364 (by decide),csr⟩
  intro off safe
  have bounds := MainServeLayout.bounds off safe
  have word := MainChunkFrame.word memory (3204+off) (by omega)
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using word

theorem data_region (ram : Word → BitVec 8) (sp w r value : Word) (bound : w.toNat<2048) :
    ViewFrame.Region ram (MainChunkDataAppend.memory ram sp w r value) sp 132 := by
  intro i
  apply MainChunkDataMemory.frame
  · have ne := FrameOffsets.ne sp 0 132 i.val w.toNat (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega)
    simpa only [BitVec.add_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using ne
  · intro j
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 3660 i.val j.val (by have := i.isLt;omega)
      (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem data_future (ram : Word → BitVec 8) (sp w r value : Word) (bound : w.toNat<2048)
    (off len : Nat) (lo : 2180≤off) (hi : off+len≤3656) :
    ViewFrame.Region ram (MainChunkDataAppend.memory ram sp w r value) (sp+BitVec.ofNat 32 off) len := by
  intro i
  apply MainChunkDataMemory.frame
  · have ne := FrameOffsets.ne sp off 132 i.val w.toNat (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using ne
  · intro j
    exact FrameOffsets.ne sp off 3660 i.val j.val (by have := i.isLt;omega)
      (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem data {c d : Core} (ram : Word → BitVec 8) (sp w r value : Word) (bound : w.toNat<2048)
    (core : MainChunkCoreFrame.At c d) (csr : d.sameCsr c) :
    At c d ram (MainChunkDataAppend.memory ram sp w r value) sp := by
  refine ⟨core,data_region ram sp w r value bound,?_,
    data_future ram sp w r value bound 3204 84 (by decide) (by decide),
    data_future ram sp w r value bound 3292 364 (by decide) (by decide),csr⟩
  intro off safe
  have bounds := MainServeLayout.bounds off safe
  have word := MainChunkDataFrame.word ram sp w r value bound (3204+off) (by omega) (by omega)
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using word

theorem refill {c d : Core} (ram : Word → BitVec 8) (sp filled read datum io : Word) (bound : filled.toNat<2048)
    (core : MainChunkCoreFrame.At c d) (csr : d.sameCsr c) :
    At c d ram (MainChunkRefillFrame.memory ram sp filled read datum io) sp := by
  refine ⟨core,?_,?_,?_,?_,csr⟩
  · simpa only [BitVec.add_zero] using MainChunkRefillFrame.region ram sp filled read datum io 0 132 bound
      (by decide) (Or.inl (by omega)) (Or.inl (by decide)) (Or.inl (by decide))
  · intro off safe
    have bounds := MainServeLayout.bounds off safe
    have word := MainChunkRefillFrame.word ram sp filled read datum io (3204+off) bound
      (by omega) (by omega) (Or.inl (by omega)) (by omega)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using word
  · exact MainChunkRefillFrame.region ram sp filled read datum io 3204 84 bound
      (by decide) (Or.inr (by omega)) (Or.inl (by decide)) (Or.inl (by decide))
  · exact MainChunkRefillFrame.region ram sp filled read datum io 3292 364 bound
      (by decide) (Or.inr (by omega)) (Or.inl (by decide)) (Or.inr (by decide))

end E5R.Thermostat.ChunkCallerFrame
