import Projects.thermostat.HeadCopyRamSource
namespace E5R.Thermostat.MainRamCopySource
open E5R E5R.Thermostat

/-- Either numeric order of two non-overlapping complete word regions. -/
def Apart (src dst : Word) (n : Nat) : Prop := src.toNat+4*n≤dst.toNat ∨ dst.toNat+4*n≤src.toNat

theorem word_above (ram : Word → BitVec 8) (src dst value : Word)
    (apart : dst.toNat+4≤src.toNat) (nowrap : src.toNat+4≤4294967296) :
    ramRead (ramWrite ram dst value .w) src .w=ramRead ram src .w := by
  apply Memory.read_word_write_other
  intro i j eq
  have hi : i.val<4 := i.isLt
  have hj : j.val<4 := j.isLt
  have h := congrArg BitVec.toNat eq
  rw [WordZero.add_nat src i.val (by omega),WordZero.add_nat dst j.val (by have := src.isLt;omega)] at h
  omega

/-- The actual store below a source snapshot preserves every remaining word.
    This covers the real main Head/Request copies whose destination is lower
    than the source; RAM is never reinterpreted as a ROM literal. -/
theorem tail_below {B ram src w ws} (h : HeadCopyRamSource.Source B ram src (w::ws)) (dst value : Word)
    (positive : 0<ws.length) (apart : dst.toNat+4≤src.toNat) :
    HeadCopyRamSource.Source B (ramWrite ram dst value .w) (src+4#32) ws := by
  have bound : src.toNat+4*(ws.length+1)≤4294967296 := by simpa only [List.length_cons] using h.block.2.2
  refine ⟨Memory.word_aligned src 1 h.aligned,Memory.sub_block h.block (off := 4) (m := 4*ws.length) (by omega) (by simp only [List.length_cons];omega),?_⟩
  intro i
  have hi := i.isLt
  have address : (src+4#32)+BitVec.ofNat 32 (4*i.val)=src+BitVec.ofNat 32 (4*(i.val+1)) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2;omega
  have numeric : (src+BitVec.ofNat 32 (4*(i.val+1))).toNat=src.toNat+4*(i.val+1) := WordZero.add_nat src _ (by omega)
  rw [address,word_above ram _ dst value (by rw [numeric];omega) (by rw [numeric];omega)]
  have snapshot := h.values ⟨i.val+1,by simp only [List.length_cons];omega⟩
  simpa only [List.getElem_cons_succ] using snapshot

theorem tail_after {B ram src w ws} (h : HeadCopyRamSource.Source B ram src (w::ws)) (dst value : Word)
    (positive : 0<ws.length) (apart : Apart src dst (w::ws).length) (nowrap : dst.toNat+4≤4294967296) :
    HeadCopyRamSource.Source B (ramWrite ram dst value .w) (src+4#32) ws := by
  rcases apart with forward|backward
  · exact HeadCopyRamSource.tail_after h dst value positive forward nowrap
  · exact tail_below h dst value positive (by simp only [List.length_cons] at backward;omega)
end E5R.Thermostat.MainRamCopySource
