import Projects.thermostat.PackedFetch
import Projects.thermostat.Memory
namespace E5R.Thermostat.AlignedSource
open E5R E5R.Thermostat

/-- Actual aligned ROM loads for the optimized memcpy path. These facts concern
    memory only and remain valid after arbitrary RAM stores. -/
structure Source (B : Board) (src : Word) (ws : List Word) : Prop where
  aligned : src.toNat%4=0
  outside : ∀ i : Fin ws.length, B.inRam (src+BitVec.ofNat 32 (4*i.val)) 4 = false
  values : ∀ i : Fin ws.length, romRead? img (src+BitVec.ofNat 32 (4*i.val)).toNat 4 false = some ws[i.val]

theorem head {B src w ws} (h : Source B src (w::ws)) : B.inRam src 4 = false ∧ romRead? img src.toNat 4 false = some w := by
  have ho := h.outside ⟨0,by simp⟩
  have hv := h.values ⟨0,by simp⟩
  simpa only [Nat.mul_zero,BitVec.add_zero,List.getElem_cons_zero] using And.intro ho hv

theorem tail {B src w ws} (h : Source B src (w::ws)) : Source B (src+4#32) ws := by
  refine ⟨Memory.word_aligned src 1 h.aligned,?_,?_⟩
  · intro i
    have hh := h.outside ⟨i.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ i.isLt⟩
    have he : (src+4#32)+BitVec.ofNat 32 (4*i.val) = src+BitVec.ofNat 32 (4*(i.val+1)) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4+4*i.val = 4*(i.val+1) by omega]
    rw [he];exact hh
  · intro i
    have hh := h.values ⟨i.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ i.isLt⟩
    have he : (src+4#32)+BitVec.ofNat 32 (4*i.val) = src+BitVec.ofNat 32 (4*(i.val+1)) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4+4*i.val = 4*(i.val+1) by omega]
    rw [he];exact hh
end E5R.Thermostat.AlignedSource
