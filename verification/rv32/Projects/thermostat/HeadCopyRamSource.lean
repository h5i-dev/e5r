import Projects.thermostat.Memory
import Projects.thermostat.WordZero
namespace E5R.Thermostat.HeadCopyRamSource
open E5R E5R.Thermostat

/-- A snapshot of aligned RAM words, with actual readable RAM geometry. -/
structure Source (B : Board) (ram : Word → BitVec 8) (src : Word) (words : List Word) : Prop where
  aligned : src.toNat%4=0
  block : Memory.Block B src (4*words.length)
  values : ∀ i : Fin words.length, ramRead ram (src+BitVec.ofNat 32 (4*i.val)) .w=words[i.val]

theorem head {B ram src w ws} (h : Source B ram src (w::ws)) :
    B.inRam src 4=true ∧ ramRead ram src .w=w := by
  constructor
  · simpa only [BitVec.add_zero] using Memory.block_access h.block (off := 0) (width := 4) (by decide) (by simp only [List.length_cons];omega)
  · have value := h.values ⟨0,by simp only [List.length_cons];omega⟩
    simpa only [Nat.mul_zero,BitVec.add_zero,List.getElem_cons_zero] using value

/-- An aligned destination word above a source word cannot alter that source.
    Both address additions are justified before using numeric inequalities. -/
theorem word_before (ram : Word → BitVec 8) (src dst value : Word)
    (apart : src.toNat+4≤dst.toNat) (nowrap : dst.toNat+4≤4294967296) :
    ramRead (ramWrite ram dst value .w) src .w=ramRead ram src .w := by
  apply Memory.read_word_write_other
  intro i j eq
  have hi : i.val<4 := i.isLt
  have hj : j.val<4 := j.isLt
  have h := congrArg BitVec.toNat eq
  rw [WordZero.add_nat src i.val (by have := dst.isLt;omega),WordZero.add_nat dst j.val (by omega)] at h
  omega

/-- A real destination store preserves the remaining RAM snapshot when the
    complete source precedes it. No ROM interpretation or copy is assumed. -/
theorem tail_after {B ram src w ws} (h : Source B ram src (w::ws)) (dst value : Word)
    (positive : 0<ws.length) (apart : src.toNat+4*(w::ws).length≤dst.toNat)
    (nowrap : dst.toNat+4≤4294967296) :
    Source B (ramWrite ram dst value .w) (src+4#32) ws := by
  have sourceEnd : src.toNat+4*(ws.length+1)≤dst.toNat := by simpa only [List.length_cons] using apart
  refine ⟨Memory.word_aligned src 1 h.aligned,Memory.sub_block h.block (off := 4) (m := 4*ws.length) (by omega) (by simp only [List.length_cons];omega),?_⟩
  intro i
  have hi := i.isLt
  have address : (src+4#32)+BitVec.ofNat 32 (4*i.val)=src+BitVec.ofNat 32 (4*(i.val+1)) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2;omega
  have numeric : (src+BitVec.ofNat 32 (4*(i.val+1))).toNat=src.toNat+4*(i.val+1) :=
    WordZero.add_nat src _ (by have := dst.isLt;omega)
  rw [address,word_before ram _ dst value (by rw [numeric];omega) nowrap]
  have snapshot := h.values ⟨i.val+1,by simp only [List.length_cons];omega⟩
  simpa only [List.getElem_cons_succ] using snapshot
end E5R.Thermostat.HeadCopyRamSource
